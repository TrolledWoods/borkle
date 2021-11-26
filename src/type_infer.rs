//! Type inferrence system
//!
//! # Will try and document more later once I feel fairly done with the first version of this system, but for now just some generic info I want to put here

mod static_values {
    //! Static value header, e.g. value indices we know what their values are statically, for very common types,
    //! like integers and so on.
    use super::ValueId;

    pub const POINTER  : ValueId = 0;
    pub const ONE      : ValueId = 1;
    pub const TWO      : ValueId = 2;
    pub const FOUR     : ValueId = 3;
    pub const EIGHT    : ValueId = 4;
    pub const TRUE     : ValueId = 5;
    pub const FALSE    : ValueId = 6;
    pub const INT_SIZE : ValueId = 7;
    pub const BOOL     : ValueId = 8;
}

use crate::errors::ErrorCtx;
use crate::program::Program;
use crate::location::Location;
use crate::operators::BinaryOp;
use crate::types::{self, IntTypeKind};
use std::collections::HashMap;
use std::hint::unreachable_unchecked;
use std::iter::repeat_with;
use std::mem;
use std::sync::Arc;
use ustr::Ustr;
use crate::program::constant::ConstantRef;

mod value_sets;
pub use value_sets::{ValueSets, ValueSetId, ValueSetHandles, ValueSet};

pub trait IntoBoxSlice<T> {
    fn into_box_slice(self) -> Option<Box<[T]>>;
}

impl<T> IntoBoxSlice<T> for Box<[T]> {
    fn into_box_slice(self) -> Option<Box<[T]>> {
        Some(self)
    }
}

impl<'a, T: Copy> IntoBoxSlice<T> for &'a [T] {
    fn into_box_slice(self) -> Option<Box<[T]>> {
        Some(self.to_vec().into_boxed_slice())
    }
}

impl<T, const N: usize> IntoBoxSlice<T> for [T; N] {
    fn into_box_slice(self) -> Option<Box<[T]>> {
        Some(Box::new(self))
    }
}

impl<T> IntoBoxSlice<T> for () {
    fn into_box_slice(self) -> Option<Box<[T]>> {
        None
    }
}

pub trait IntoConstant {
    fn into_constant(self) -> Option<ConstantRef>;
}

impl IntoConstant for ConstantRef {
    fn into_constant(self) -> Option<ConstantRef> {
        Some(self)
    }
}

impl IntoConstant for () {
    fn into_constant(self) -> Option<ConstantRef> {
        None
    }
}

pub trait IntoValueSet {
    fn add_set(self, value_sets: &mut ValueSets, already_complete: bool) -> ValueSetHandles;
}

impl IntoValueSet for () {
    fn add_set(self, _value_sets: &mut ValueSets, already_complete: bool) -> ValueSetHandles {
        ValueSetHandles::empty(already_complete)
    }
}

impl IntoValueSet for &ValueSetHandles {
    fn add_set(self, value_sets: &mut ValueSets, already_complete: bool) -> ValueSetHandles {
        self.clone(value_sets, already_complete)
    }
}

impl IntoValueSet for ValueSetId {
    fn add_set(self, value_sets: &mut ValueSets, already_complete: bool) -> ValueSetHandles {
        value_sets.with_one(self, already_complete)
    }
}

#[derive(Clone, Copy)]
pub struct CompilerType(pub types::Type);

#[derive(Clone, Copy)]
pub struct Empty;
#[derive(Clone, Copy)]
pub struct Var(pub ValueId);
#[derive(Clone, Copy)]
pub struct Unknown;

pub trait IntoAccess {
    fn into_variance(self, system: &mut TypeSystem, set: ValueSetId) -> ValueId;
}

impl IntoAccess for Access {
    fn into_variance(self, system: &mut TypeSystem, set: ValueSetId) -> ValueId {
        system.add_access(Some(self), set)
    }
}

impl IntoAccess for Var {
    fn into_variance(self, _: &mut TypeSystem, _: ValueSetId) -> ValueId {
        self.0
    }
}

impl IntoAccess for Unknown {
    fn into_variance(self, system: &mut TypeSystem, set: ValueSetId) -> ValueId {
        system.add_access(None, set)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeKind {
    // bool, u8
    Int,
    // No arguments, the size of an integer, hidden type that the user cannot access
    IntSize,

    Bool,
    Empty,

    // return, (arg0, arg1, arg2, ...)
    Function,
    // element: type, length: int
    Array,
    // mutability, type
    Reference,
    // mutability, type
    Buffer,
    // (type, type, type, type), in the same order as the strings.
    Struct(Box<[Ustr]>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Variance {
    /// Covariance
    Covariant,
    /// Variance
    Variant,
    /// Require exact equality
    Invariant,
    /// For cases where variance can't be computed yet, so ignore it for now.
    DontCare,
}

impl Variance {
    fn to_string(&self) -> &'static str {
        match self {
            Self::Covariant => "<=",
            Self::Variant => "=>",
            Self::Invariant => "==",
            Self::DontCare => "~~",
        }
    }

    /// Applies this variance to another variance.
    /// If self is DontCare, the other variance will also be DontCare.
    /// If self is Variant, the other variance will remain unchanged, if self is Covariant the other variance will be flipped.
    /// If self is Invariant, the other variance will also become Invariant.
    fn apply_to(self, other: Variance) -> Variance {
        match (self, other) {
            (Variance::DontCare, _) => Variance::DontCare,
            (Variance::Variant, c) => c,
            (Variance::Covariant, c) => c.invert(),
            (Variance::Invariant, _) => Variance::Invariant,
        }
    }

    fn combine(&mut self, other: Variance) {
        match (*self, other) {
            (Variance::DontCare, c) => *self = c,
            (Variance::Covariant, Variance::Variant) | (Variance::Variant, Variance::Covariant) => {
                *self = Variance::Invariant
            }
            (_, Variance::Invariant) => *self = Variance::Invariant,
            (_, Variance::DontCare)
            | (Variance::Invariant, _)
            | (Variance::Variant, Variance::Variant)
            | (Variance::Covariant, Variance::Covariant) => {}
        }
    }

    fn invert(self) -> Variance {
        match self {
            Self::Covariant => Self::Variant,
            Self::Variant => Self::Covariant,
            Self::Invariant => Self::Invariant,
            Self::DontCare => Self::DontCare,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Access {
    pub cannot_read: bool,
    pub needs_read: bool,
    pub cannot_write: bool,
    pub needs_write: bool,
}

impl Default for Access {
    fn default() -> Self {
        Self {
            cannot_read: false,
            cannot_write: false,
            needs_read: false,
            needs_write: false,
        }
    }
}

impl Access {
    pub fn cannot_read(&self) -> bool {
        self.cannot_read
    }

    pub fn cannot_write(&self) -> bool {
        self.cannot_write
    }

    pub fn needs_read(&self) -> bool {
        self.needs_read
    }

    pub fn needs_write(&self) -> bool {
        self.needs_write
    }

    pub fn specific(read: bool, write: bool) -> Self {
        Self {
            cannot_read: !read,
            cannot_write: !write,
            needs_read: read,
            needs_write: write,
        }
    }
    
    pub fn disallows(cannot_read: bool, cannot_write: bool) -> Self {
        Self {
            cannot_read,
            cannot_write,
            needs_read: false,
            needs_write: false,
        }
    }

    pub fn needs(needs_read: bool, needs_write: bool) -> Self {
        Self {
            cannot_read: false,
            cannot_write: false,
            needs_read,
            needs_write,
        }
    }

    pub fn is_complete(&self) -> bool {
        self.cannot_read <= self.needs_read && self.cannot_write <= self.needs_write
    }

    pub fn combine_with(&mut self, other: &mut Self, variance: Variance) {
        match variance {
            Variance::Variant => {
                self.needs_read |= other.needs_read;
                self.needs_write |= other.needs_write;
                other.cannot_read &= self.cannot_read;
                other.cannot_write &= self.cannot_write;
            }
            Variance::Covariant => {
                other.needs_read |= self.needs_read;
                other.needs_write |= self.needs_write;
                self.cannot_read &= other.cannot_read;
                self.cannot_write &= other.cannot_write;
            }
            Variance::Invariant => {
                other.needs_read |= self.needs_read;
                self.needs_read = other.needs_read;
                other.needs_write |= self.needs_write;
                self.needs_write = other.needs_write;
                other.needs_read &= self.needs_read;
                self.needs_read = other.needs_read;
                other.needs_write &= self.needs_write;
                self.needs_write = other.needs_write;
            }
            Variance::DontCare => {},
        }
    }
}

#[derive(Debug)]
pub struct Type {
    pub kind: TypeKind,
    pub args: Option<Box<[ValueId]>>,
}

impl Type {
    fn primitive(kind: TypeKind) -> Self {
        Self {
            kind,
            args: Some(Box::new([])),
        }
    }
}

#[derive(Debug)]
pub struct Constant {
    pub type_: ValueId,
    pub value: Option<ConstantRef>,
}

#[derive(Debug)]
pub enum ValueKind {
    Error,

    Type(Option<Type>),

    // @Cleanup: Rename to Constant
    /// For now values can only be usize, but you could theoretically have any value.
    Value(Option<Constant>),

    /// These are the only coerced values for now.
    Access(Option<Access>),
}

impl ValueKind {
    fn is_complete(&self) -> bool {
        matches!(
            self,
            ValueKind::Type(Some(Type { args: Some(_), .. }))
            | ValueKind::Value(Some(Constant { value: Some(_), .. }))
            | ValueKind::Access(Some(_))
        )
    }

    fn to_unknown(&self) -> Self {
        match self {
            Self::Type(_) => Self::Type(None),
            Self::Value(_) => Self::Value(None),
            Self::Access(_) => Self::Access(None),
            Self::Error => Self::Error,
        }
    }
}

type ConstraintId = usize;

#[derive(Debug, Clone, Copy)]
struct Constraint {
    kind: ConstraintKind,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum ConstraintKind {
    BinaryOp {
        op: BinaryOp,
        values: [ValueId; 3],
    },
    Equal {
        values: [ValueId; 2],
        variance: Variance,
    },
    EqualsField {
        values: [ValueId; 2],
        index: usize,
        variance: Variance,
    },
    EqualNamedField {
        values: [ValueId; 2],
        index: Ustr,
        variance: Variance,
    },
    Dead,
}

impl Constraint {
    /// Fixes the order of the fields, or sets the constraint to Dead if it becomes redundant.
    fn fix_order(&mut self) {
        match &mut self.kind {
            ConstraintKind::Equal {
                values: [a, b],
                variance,
            } => {
                if a == b {
                    self.kind = ConstraintKind::Dead;
                } else if a > b {
                    mem::swap(a, b);
                    *variance = variance.invert();
                }
            }
            ConstraintKind::EqualsField { .. }
            | ConstraintKind::EqualNamedField { .. }
            | ConstraintKind::BinaryOp { .. }
            | ConstraintKind::Dead => {}
        }
    }

    fn apply_variance(mut self, from: Variance) -> Self {
        if let Some(variance) = self.variance_mut() {
            *variance = from.apply_to(*variance);
        }

        self
    }

    fn values(&self) -> &[ValueId] {
        match &self.kind {
            ConstraintKind::Equal { values, .. }
            | ConstraintKind::EqualsField { values, .. }
            | ConstraintKind::EqualNamedField { values, .. } => &*values,
            ConstraintKind::BinaryOp { values, .. } => &*values,
            ConstraintKind::Dead => &[],
        }
    }

    fn values_mut(&mut self) -> &mut [ValueId] {
        match &mut self.kind {
            ConstraintKind::Equal { values, .. }
            | ConstraintKind::EqualsField { values, .. }
            | ConstraintKind::EqualNamedField { values, .. } => &mut *values,
            ConstraintKind::BinaryOp { values, .. } => &mut *values,
            ConstraintKind::Dead => &mut [],
        }
    }

    fn variance_mut(&mut self) -> Option<&mut Variance> {
        match &mut self.kind {
            ConstraintKind::Equal { variance, .. }
            | ConstraintKind::EqualsField { variance, .. }
            | ConstraintKind::EqualNamedField { variance, .. } => Some(variance),
            ConstraintKind::Dead | ConstraintKind::BinaryOp { .. } => None,
        }
    }

    fn equal(a: ValueId, b: ValueId, variance: Variance) -> Self {
        let kind = if a == b {
            ConstraintKind::Dead
        } else if b > a {
            ConstraintKind::Equal {
                values: [a, b],
                variance,
            }
        } else {
            ConstraintKind::Equal {
                values: [b, a],
                variance: variance.invert(),
            }
        };

        Self { kind, }
    }
}

#[derive(Debug)]
pub struct Error {
    a: ValueId,
    b: ValueId,
    kind: ErrorKind,
}

impl Error {
    fn new(a: ValueId, b: ValueId, kind: ErrorKind) -> Self {
        Self { a, b, kind }
    }
}

#[derive(Debug)]
pub enum ErrorKind {
    NonexistantOperation,
    MixingTypesAndValues,
    IncompatibleTypes,
    IncompatibleValues,
    ValueAndTypesIntermixed,
    IndexOutOfBounds(usize),
    NonexistantName(Ustr),
}

struct VarianceConstraint {
    /// The variance between the two Access operations
    variance: Variance,
    /// The variance "strength" applied in the last queueing of constraints. This is so we can make sure we don't
    /// issue all the constraints several times unnecessarily.
    last_variance_applied: Variance,
    constraints: Vec<(ConstraintId, Variance)>,
}

// Temporary, until we move to calling values.get immediately.
fn get_value(values: &Values, id: ValueId) -> &Value {
    values.get(id)
}

fn get_value_mut(values: &mut Values, id: ValueId) -> &mut Value {
    values.get_mut(id)
}

fn insert_constraint(
    constraints: &mut Vec<Constraint>,
    available_constraints: &mut HashMap<ValueId, Vec<ConstraintId>>,
    constraint: Constraint,
) -> Option<ConstraintId> {
    // @Performance: We can do a faster lookup using available_constraints.
    // We also want to join constraints together that are the exact same but with just different variances.
    if let Some(id) = constraints.iter().position(|v| v.kind == constraint.kind) {
        return Some(id);
    }

    let id = constraints.len();
    constraints.push(constraint);

    match constraint.kind {
        ConstraintKind::Equal { values: [a, b], .. } => {
            if a == b {
                return None;
            };
        }
        _ => {}
    }

    for &value in constraint.values() {
        let vec = available_constraints.entry(value).or_insert_with(Vec::new);
        vec.push(id);
    }

    Some(id)
}

fn insert_active_constraint(
    constraints: &mut Vec<Constraint>,
    available_constraints: &mut HashMap<ValueId, Vec<ConstraintId>>,
    queued_constraints: &mut Vec<ConstraintId>,
    constraint: Constraint,
) {
    // @Performance: We can do a faster lookup using available_constraints
    // @TODO: We want to check for equality things with just different variances here too, but I think
    // I have to change how constraints are represented first as well.
    if let Some(_) = constraints.iter().position(|v| v.kind == constraint.kind) {
        return;
    }

    // We probably want to find a dead constraint to slot things into? Should we have a list of dead constraints that are available, or is that getting too overkill?
    let id = constraints.len();
    constraints.push(constraint);

    match constraint.kind {
        ConstraintKind::Equal { values: [a, b], .. } => {
            if a == b {
                return;
            };
        }
        _ => {}
    }

    for &value in constraint.values() {
        let vec = available_constraints.entry(value).or_insert_with(Vec::new);
        vec.push(id);
    }

    queued_constraints.push(id);
}

fn type_kind_to_str(
    string: &mut String,
    type_kind: &TypeKind,
    num_args: Option<usize>,
) -> std::fmt::Result {
    use std::fmt::Write;
    match type_kind {
        TypeKind::Int => write!(string, "int"),
        TypeKind::IntSize => write!(string, "<size of int>"),
        TypeKind::Bool => write!(string, "bool"),
        TypeKind::Empty => write!(string, "Empty"),
        TypeKind::Function => {
            write!(string, "fn(")?;
            if let Some(num_args) = num_args {
                write!(string, "{}", vec!["_"; num_args - 1].join(", "))?;
            } else {
                write!(string, "...")?;
            }
            write!(string, ") -> _")
        }
        TypeKind::Struct(names) => {
            write!(string, "{{ ")?;
            for (i, name) in names.iter().enumerate() {
                if i > 0 {
                    write!(string, ", ")?;
                }
                write!(string, "{}: _", name)?;
            }
            write!(string, " }}")
        }
        TypeKind::Array => write!(string, "[_] _"),
        TypeKind::Reference => write!(string, "&_"),
        TypeKind::Buffer => write!(string, "[] _"),
    }
}

pub type ValueId = u32;

#[derive(Debug)]
struct Value {
    kind: ValueKind,
    value_sets: ValueSetHandles,
}

struct LookupElement {
    internal_id: u32,
    // u32::MAX is None
    next_in_lookup: u32,
}

// @Temporary: Should be replaced with the real value some day
struct ValueWrapper {
    value: Value,
    structure_id: u32,
    // u32::MAX means that there is nothing.
    next_in_structure_group: u32,
}

struct Values {
    structure: Vec<(u32, u32)>,
    values: Vec<ValueWrapper>,
}

impl Values {
    fn new() -> Self {
        Self {
            structure: Vec::new(),
            values: Vec::with_capacity(32),
        }
    }

    fn structurally_combine(&mut self, a: ValueId, b: ValueId) {
        let structure_id = self.values[a as usize].structure_id;
        let old_b_structure_id = self.values[b as usize].structure_id;

        if structure_id == old_b_structure_id {
            return;
        }

        let (b_structure_start, b_structure_len) = mem::replace(&mut self.structure[old_b_structure_id as usize], (u32::MAX, 0));
        self.structure[structure_id as usize].1 += b_structure_len;

        // Join the two linked lists together
        let mut value_id = a;
        loop {
            let value = &mut self.values[value_id as usize];
            if value.next_in_structure_group == u32::MAX {
                value.next_in_structure_group = b_structure_start;
                break;
            }
            value_id = value.next_in_structure_group;
        }

        // Convert the old structure list to the new structure
        let mut value_id = b_structure_start;
        loop {
            let value = &mut self.values[value_id as usize];
            value.structure_id = structure_id;
            if value.next_in_structure_group == u32::MAX {
                break;
            }
            value_id = value.next_in_structure_group;
        }
    }

    fn add(&mut self, mut value: Value) -> ValueId {
        let structure_id = self.structure.len() as u32;
        let id = self.values.len() as u32;
        assert!(id < u32::MAX, "Too many values, overflows a u32");
        self.structure.push((structure_id, 1));

        self.values.push(ValueWrapper {
            value,
            structure_id,
            next_in_structure_group: u32::MAX,
        });
        id
    }

    fn iter(&self) -> impl Iterator<Item = &Value> {
        self.values.iter().map(|v| &v.value)
    }

    fn iter_mut(&mut self) -> impl Iterator<Item = &mut Value> {
        self.values.iter_mut().map(|v| &mut v.value)
    }

    fn get(&self, id: ValueId) -> &Value {
        &self.values[id as usize].value
    }

    fn get_mut(&mut self, id: ValueId) -> &mut Value {
        &mut self.values[id as usize].value
    }

    /// Returns the value id that will returned by the next call to `add`
    fn next_value_id(&self) -> ValueId {
        self.values.len() as u32
    }

    fn get_disjoint_mut(&mut self, a: ValueId, b: ValueId) -> (&mut Value, &mut Value) {
        debug_assert_ne!(a, b, "Cannot call get_disjoint_mut on the same values");
        debug_assert!(a < b, "When calling get_disjoint_mut, a has to be less than b");

        let (section_a, section_b) = self.values.split_at_mut(b as usize);

        (&mut section_a[a as usize].value, &mut section_b[0].value)
    }
}

pub struct TypeSystem {
    /// The first few values are always primitive values, with a fixed position, to make them trivial to create.
    /// 0 - Int
    values: Values,

    pub value_sets: ValueSets,

    constraints: Vec<Constraint>,

    /// When the access level of certain things determine the variance of constraints, those constraints are put into here.
    variance_updates: HashMap<(ValueId, ValueId), VarianceConstraint>,

    available_constraints: HashMap<ValueId, Vec<ConstraintId>>,
    queued_constraints: Vec<ConstraintId>,

    pub errors: Vec<Error>,
}

impl TypeSystem {
    pub fn new(program: &crate::program::Program) -> Self {
        let u8_type = crate::types::Type::new(crate::types::TypeKind::Int(IntTypeKind::U8));
        let bool_type = crate::types::Type::new(crate::types::TypeKind::Bool);

        let mut this = Self {
            values: Values::new(),
            value_sets: ValueSets::default(),
            variance_updates: HashMap::new(),
            constraints: Vec::new(),
            available_constraints: HashMap::new(),
            queued_constraints: Vec::new(),
            errors: Vec::new(),
        };

        for i in [0, 1, 2, 4, 8_u8] {
            let buffer = program.insert_buffer(u8_type, &i);
            this.add_value(static_values::INT_SIZE, buffer, ());
        }

        for i in [1, 0_u8] {
            let buffer = program.insert_buffer(bool_type, &i);
            this.add_value(static_values::BOOL, buffer, ());
        }

        this.add_type(TypeKind::IntSize, [], ());
        this.add_type(TypeKind::Bool, [], ());

        this
    }

    /// Only to be used when generating incompleteness-errors
    pub fn flag_all_values_as_complete(&mut self) {
        for value in self.values.iter_mut() {
            value.value_sets.complete(&mut self.value_sets);
        }
    }

    pub fn output_errors(&self, errors: &mut ErrorCtx) -> bool {
        let mut has_errors = false;
        if self.value_sets.iter().any(|v| v.has_errors) {
            has_errors = true;
            use std::fmt::Write;
            for value in self.values.iter() {
                if let Value {
                    kind: ValueKind::Error,
                    ..
                } = value {
                    // TODO: Use the ast node location
                    errors.global_error("Typing error!".to_string());
                }
            }
        }

        for error in &self.errors {
            has_errors = true;

            match *error {
                _ => errors.global_error(format!("Temporary type-inference error: {:?}", error)),
            }
        }

        has_errors
    }

    pub fn value_is_in_set(&self, value_id: ValueId, set_id: ValueSetId) -> bool {
        get_value(&self.values, value_id).value_sets.contains(set_id)
    }

    pub fn value_to_compiler_type(&self, value_id: ValueId) -> types::Type {
        let ValueKind::Type(Some(Type { kind: type_kind, args: Some(type_args) })) = &get_value(&self.values, value_id).kind else {
            panic!("Cannot call value_to_compiler_type on incomplete value")
        };

        match *type_kind {
            TypeKind::IntSize => unreachable!("Int sizes are a hidden type for now, the user shouldn't be able to access them"),
            TypeKind::Int => {
                let [signed, size] = &**type_args else {
                    unreachable!("Invalid int size and sign")
                };

                let Value { kind: ValueKind::Value(Some(Constant {
                    type_: _,
                    value: Some(sign_value),
                })), .. } = get_value(&self.values, *signed) else {
                    unreachable!("No!!!")
                };

                let Value { kind: ValueKind::Value(Some(Constant {
                    type_: _,
                    value: Some(size_value),
                })), .. } = get_value(&self.values, *size) else {
                    unreachable!("No!!!")
                };

                let sign_value = unsafe { *sign_value.as_ptr().cast::<bool>() };
                let size_value = unsafe { *size_value.as_ptr().cast::<u8>() };
                let int_type_kind = match (sign_value, size_value) {
                    (false, 0) => IntTypeKind::Usize,
                    (false, 1) => IntTypeKind::U8,
                    (false, 2) => IntTypeKind::U16,
                    (false, 4) => IntTypeKind::U32,
                    (false, 8) => IntTypeKind::U64,
                    (true, 0) => IntTypeKind::Isize,
                    (true, 1) => IntTypeKind::I8,
                    (true, 2) => IntTypeKind::I16,
                    (true, 4) => IntTypeKind::I32,
                    (true, 8) => IntTypeKind::I64,
                    (_, _) => unreachable!("Invalid sign+size combination"),
                };

                types::Type::new(types::TypeKind::Int(int_type_kind))
            }
            TypeKind::Bool => types::Type::new(types::TypeKind::Bool),
            TypeKind::Empty => types::Type::new(types::TypeKind::Empty),
            TypeKind::Function => {
                let [return_type, arg_types @ ..] = &**type_args else {
                    unreachable!("Invalid function type")
                };

                let returns = self.value_to_compiler_type(*return_type);
                let args = arg_types
                    .iter()
                    .map(|v| self.value_to_compiler_type(*v))
                    .collect();

                types::Type::new(types::TypeKind::Function { args, returns })
            }
            TypeKind::Array => {
                let [element_type, length] = &**type_args else {
                    unreachable!("Invalid array type")
                };

                let element_type = self.value_to_compiler_type(*element_type);

                let ValueKind::Value(Some(Constant { value: Some(length), .. })) = &get_value(&self.values, *length).kind else {
                    unreachable!("Array length isn't a value")
                };

                let length = unsafe { usize::from_le_bytes(*length.as_ptr().cast::<[u8; 8]>()) };

                types::Type::new(types::TypeKind::Array(element_type, length))
            }
            TypeKind::Buffer => {
                let [mutability, pointee] = &**type_args else {
                    unreachable!("Invalid reference type")
                };

                let ValueKind::Access(Some(access)) = &get_value(&self.values, *mutability).kind else {
                    unreachable!("Requires access")
                };

                let pointee = self.value_to_compiler_type(*pointee);
                let permits = types::PtrPermits::from_read_write(access.needs_read(), access.needs_write());

                types::Type::new(types::TypeKind::Buffer { pointee, permits })
            }
            TypeKind::Reference => {
                let [mutability, pointee] = &**type_args else {
                    unreachable!("Invalid reference type")
                };

                let ValueKind::Access(Some(access)) = &get_value(&self.values, *mutability).kind else {
                    unreachable!("Requires access")
                };

                let pointee = self.value_to_compiler_type(*pointee);
                let permits = types::PtrPermits::from_read_write(access.needs_read(), access.needs_write());

                types::Type::new(types::TypeKind::Reference { pointee, permits })
            }
            TypeKind::Struct(ref fields) => {
                let fields = fields
                    .iter()
                    .zip(type_args.iter())
                    .map(|(&name, &v)| (name, self.value_to_compiler_type(v)))
                    .collect::<Vec<_>>();
                types::Type::new(types::TypeKind::Struct(fields))
            }
        }
    }
    
    pub fn set_op_equal(&mut self, op: BinaryOp, a: ValueId, b: ValueId, result: ValueId) {
        insert_active_constraint(
            &mut self.constraints,
            &mut self.available_constraints,
            &mut self.queued_constraints,
            Constraint {
                kind: ConstraintKind::BinaryOp {
                    values: [a, b, result],
                    op,
                },
            },
        );
    }

    pub fn set_equal(&mut self, a: ValueId, b: ValueId, variance: Variance) {
        if a == b {
            return;
        }
        insert_active_constraint(
            &mut self.constraints,
            &mut self.available_constraints,
            &mut self.queued_constraints,
            Constraint::equal(a, b, variance),
        );
    }

    pub fn set_field_equal(
        &mut self,
        a: ValueId,
        field_index: usize,
        b: ValueId,
        variance: Variance,
    ) {
        insert_active_constraint(
            &mut self.constraints,
            &mut self.available_constraints,
            &mut self.queued_constraints,
            Constraint {
                kind: ConstraintKind::EqualsField {
                    values: [a, b],
                    index: field_index,
                    variance,
                },
            },
        );
    }

    pub fn set_field_name_equal(
        &mut self,
        a: ValueId,
        field_name: Ustr,
        b: ValueId,
        variance: Variance,
    ) {
        insert_active_constraint(
            &mut self.constraints,
            &mut self.available_constraints,
            &mut self.queued_constraints,
            Constraint {
                kind: ConstraintKind::EqualNamedField {
                    values: [a, b],
                    index: field_name,
                    variance,
                },
            },
        );
    }

    pub fn solve(&mut self) {
        // @Performance: I think this might be more performant than not sorting, but not 100% sure.
        // self.queued_constraints.sort_unstable_by_key(|v| matches!(&self.constraints[*v], ConstraintKind::Equal { variance: Variance::Invariant, .. }));

        // self.print_state();

        let mut i = 1;
        while let Some(available_id) = self.queued_constraints.pop() {
            i += 1;

            // println!("Applied constraint: {}", self.constraint_to_string(&self.constraints[available_id]));

            self.apply_constraint(available_id);

            // self.print_state();
        }

        // self.print_state();

        // println!("-- Number of steps required: {}", i);
    }

    fn constant_to_str(&self, type_: ValueId, value: ConstantRef, rec: usize) -> String {
        match &get_value(&self.values, type_).kind {
            ValueKind::Type(Some(Type { kind: TypeKind::IntSize, .. })) => {
                let mut byte = 0_u8;
                unsafe {
                    byte = *value.as_ptr();
                }
                match byte {
                    0 => "ptr".to_string(),
                    1 => "1".to_string(),
                    2 => "2".to_string(),
                    4 => "4".to_string(),
                    8 => "8".to_string(),
                    num => format!("<invalid int size value {}>", num),
                }
            }
            ValueKind::Type(Some(Type { kind: TypeKind::Int, args: Some(c) })) => {
                let [signed, size] = &**c else { panic!() };

                let (
                    Value { kind: ValueKind::Value(Some(Constant { value: Some(signed), .. })), .. },
                    Value { kind: ValueKind::Value(Some(Constant { value: Some(size), .. })), .. },
                ) = (get_value(&self.values, *signed), get_value(&self.values, *size)) else {
                    return "(?)".to_string();
                };

                let signed = unsafe { *signed.as_ptr().cast::<bool>() };
                let size = unsafe { *size.as_ptr().cast::<u8>() } as usize;

                let mut big_int = [0; 16];
                unsafe {
                    std::ptr::copy_nonoverlapping(value.as_ptr(), big_int.as_mut_ptr(), size);
                }

                if (big_int[size] & 0x80) > 0 {
                    big_int[size + 1..].fill(0xff);
                }

                format!("{}", i128::from_le_bytes(big_int))
            }
            ValueKind::Type(Some(Type { kind: TypeKind::Bool, .. })) => {
                let mut byte = 0_u8;
                unsafe {
                    byte = *value.as_ptr();
                }
                match byte {
                    0 => "false".to_string(),
                    1 => "true".to_string(),
                    num => format!("<invalid bool value {}>", num),
                }
            }
            ValueKind::Type(_) => {
                format!("(cannot format {})", self.value_to_str(type_, rec))
            }
            ValueKind::Error { .. } => {
                format!("error!")
            }
            v => unreachable!("Not a type! {:?}", v),
        }
    }

    pub fn value_to_str(&self, value: ValueId, rec: usize) -> String {
        if rec > 7 {
            return "...".to_string();
        }
        match &self.values.get(value).kind {
            ValueKind::Access(None) => format!("_"),
            ValueKind::Error => format!("ERR"),
            ValueKind::Access(Some(access)) => {
                format!(
                    "{}{}",
                    match (access.needs_read(), access.needs_write()) {
                        (true, true) => "rw",
                        (true, false) => "r",
                        (false, true) => "w",
                        (false, false) => "!!",
                    },
                    match (
                        access.cannot_read() && access.needs_read(),
                        access.cannot_write() && access.needs_write(),
                    ) {
                        (true, true) => "-rw",
                        (true, false) => "-r",
                        (false, true) => "-w",
                        (false, false) => "",
                    },
                )
            }
            ValueKind::Type(Some(Type { kind: TypeKind::Bool, .. })) => "bool".to_string(),
            ValueKind::Type(Some(Type { kind: TypeKind::Empty, .. })) => "Empty".to_string(),
            ValueKind::Type(Some(Type { kind: TypeKind::IntSize, .. })) => "<size of int>".to_string(),
            ValueKind::Type(None) => "_".to_string(),
            ValueKind::Value(None) => "_(value)".to_string(),
            ValueKind::Value(Some(Constant { type_, value: None, .. })) => {
                format!("(_: {})", self.value_to_str(*type_, rec + 1))
            }
            ValueKind::Value(Some(Constant { type_, value: Some(value), .. })) => {
                format!("{}", self.constant_to_str(*type_, *value, rec + 1))
            }
            ValueKind::Type(Some(Type { kind, args: None, .. })) => format!("{:?}", kind),
            ValueKind::Type(Some(Type { kind: TypeKind::Int, args: Some(c) })) => match &**c {
                [signed, size] => format!(
                    "int({}, {})",
                    self.value_to_str(*signed, rec + 1),
                    self.value_to_str(*size, rec + 1),
                ),
                _ => unreachable!("A function pointer type has to have at least a return type"),
            }
            ValueKind::Type(Some(Type { kind: TypeKind::Function, args: Some(c) })) => match &**c {
                [return_, args @ ..] => format!(
                    "fn({}) -> {}",
                    args.iter()
                        .map(|&v| self.value_to_str(v, rec + 1))
                        .collect::<Vec<_>>()
                        .join(", "),
                    self.value_to_str(*return_, rec + 1),
                ),
                _ => unreachable!("A function pointer type has to have at least a return type"),
            },
            ValueKind::Type(Some(Type { kind: TypeKind::Struct(names), args: Some(c), .. })) => {
                let list = names
                    .iter()
                    .zip(c.iter())
                    .map(|(name, type_)| {
                        format!("{}: {}", name, self.value_to_str(*type_, rec + 1))
                    })
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("{{ {} }}", list)
            }
            ValueKind::Type(Some(Type { kind: TypeKind::Array, args: Some(c), .. })) => match &**c {
                [type_, length] => format!(
                    "[{}] {}",
                    self.value_to_str(*length, rec + 1),
                    self.value_to_str(*type_, rec + 1),
                ),
                _ => unreachable!("Arrays should only ever have two type parameters"),
            },
            ValueKind::Type(Some(Type { kind: TypeKind::Buffer, args: Some(c), .. })) => match &**c {
                [mutability, type_] => format!(
                    "[]{} {}",
                    self.value_to_str(*mutability, rec + 1),
                    self.value_to_str(*type_, rec + 1)
                ),
                _ => unreachable!("Buffers should only ever have two type parameters"),
            },
            ValueKind::Type(Some(Type { kind: TypeKind::Reference, args: Some(c), .. })) => match &**c {
                [mutability, type_] => format!(
                    "&{} {}",
                    self.value_to_str(*mutability, rec + 1),
                    self.value_to_str(*type_, rec + 1)
                ),
                _ => unreachable!("References should only ever have two type parameters"),
            },
        }
    }

    fn constraint_to_string(&self, constraint: &Constraint) -> String {
        match constraint.kind {
            ConstraintKind::Dead => format!("< removed >"),
            ConstraintKind::BinaryOp { values: [a, b, result], op } => {
                format!(
                    "{} {:?} {} == {}",
                    self.value_to_str(a, 0),
                    op,
                    self.value_to_str(b, 0),
                    self.value_to_str(result, 0),
                )
            }
            ConstraintKind::Equal {
                values: [a_id, b_id],
                variance,
            } => {
                format!(
                    "{}({}) {} {}({})",
                    a_id,
                    self.value_to_str(a_id, 0),
                    variance.to_string(),
                    b_id,
                    self.value_to_str(b_id, 0)
                )
            }
            ConstraintKind::EqualsField {
                values: [a_id, b_id],
                index: field_index,
                variance,
            } => {
                format!(
                    "{}({}).{} {} {}({})",
                    a_id,
                    self.value_to_str(a_id, 0),
                    field_index,
                    variance.to_string(),
                    b_id,
                    self.value_to_str(b_id, 0)
                )
            }
            ConstraintKind::EqualNamedField {
                values: [a_id, b_id],
                index: field_name,
                variance,
            } => {
                format!(
                    "{}({}).{} {} {}({})",
                    a_id,
                    self.value_to_str(a_id, 0),
                    field_name,
                    variance.to_string(),
                    b_id,
                    self.value_to_str(b_id, 0)
                )
            }
        }
    }

    pub fn print_state(&self) {
        println!("Values:");
        // @Volatile: If we change how value ids work, this will no longer work.
        for (i, v) in self.values.iter().enumerate() {
            println!("{}: {}, {}", i, v.value_sets.is_complete(), self.value_to_str(i as u32, 0));
        }
        println!();

        println!("Queued constraints:");

        for &constraint_id in &self.queued_constraints {
            let constraint = &self.constraints[constraint_id];
            println!("({}) {}", constraint_id, self.constraint_to_string(constraint));
        }
        println!();
    }

    pub fn finish(&self) {
        if !self.errors.is_empty() {
            println!("There were errors:");

            for error in &self.errors {
                println!(
                    "{}, {}\n{:?}",
                    self.value_to_str(error.a, 0),
                    self.value_to_str(error.b, 0),
                    error.kind
                );
            }
        }
    }

    fn apply_constraint(&mut self, constraint_id: ConstraintId) {
        let constraint = self.constraints[constraint_id];

        let mut progress = [false; 8];

        match constraint.kind {
            ConstraintKind::Dead => {}
            ConstraintKind::BinaryOp {
                values: [a_id, b_id, result_id],
                op,
            } => {
                let a = get_value(&self.values, a_id);
                let b = get_value(&self.values, b_id);
                let result = get_value(&self.values, result_id);

                let (a, b, result) = match (&a.kind, &b.kind, &result.kind) {
                    (ValueKind::Type(a), ValueKind::Type(b), ValueKind::Type(result)) => (a, b, result),
                    (_, _, _) => {
                        // Error! This is temporary, I want to change how I do errors later anyway so who cares.
                        let result = get_value_mut(&mut self.values, result_id);
                        result.value_sets.make_erroneous(&mut self.value_sets);
                        *result = Value {
                            kind: ValueKind::Error,
                            value_sets: ValueSetHandles::already_complete(),
                        };
                        return;
                    }
                };

                match (op, (a.as_ref().map(|v| &v.kind), b.as_ref().map(|v| &v.kind), result.as_ref().map(|v| &v.kind))) {
                    (
                        BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mult | BinaryOp::Div | BinaryOp::BitAnd | BinaryOp::BitOr,
                        (Some(TypeKind::Int), Some(TypeKind::Int), Some(TypeKind::Int)),
                    ) => {
                        self.set_equal(a_id, b_id, Variance::Invariant);
                        self.set_equal(a_id, result_id, Variance::Invariant);
                    }
                    (
                        BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mult | BinaryOp::Div | BinaryOp::BitAnd | BinaryOp::BitOr,
                        (Some(TypeKind::Reference), Some(TypeKind::Int), Some(TypeKind::Reference)),
                    ) => {
                        // No reason given for why the type is a usize....
                        let usize = self.add_int(IntTypeKind::Usize, ());
                        self.set_equal(usize, b_id, Variance::Invariant);
                        self.set_equal(a_id, result_id, Variance::Invariant);
                    }
                    (
                        BinaryOp::And | BinaryOp::Or,
                        (_, _, _),
                    ) => {
                        // Temporary: No type validation, just equality :)
                        let bool = self.add_type(TypeKind::Bool, [], ());
                        self.set_equal(bool, a_id, Variance::Invariant);
                        self.set_equal(bool, b_id, Variance::Invariant);
                        self.set_equal(bool, result_id, Variance::Invariant);
                    }
                    (
                        BinaryOp::Equals | BinaryOp::NotEquals | BinaryOp::LargerThanEquals | BinaryOp::LargerThan | BinaryOp::LessThanEquals | BinaryOp::LessThan,
                        (Some(TypeKind::Int), Some(TypeKind::Int), _) | (Some(TypeKind::Reference), Some(TypeKind::Reference), _)
                    ) => {
                        let id = self.add_type(TypeKind::Bool, [], ());

                        self.set_equal(result_id, id, Variance::Invariant);
                        self.set_equal(a_id, b_id, Variance::DontCare);
                    }
                    (
                        _,
                        (Some(a), Some(b), Some(c)),
                    ) => unimplemented!("Operator {:?} with operands {:?}, {:?}, and returning {:?}, not supported in type inferrence yet", op, a, b, c),
                    _ => return,
                }

                self.constraints[constraint_id].kind = ConstraintKind::Dead;
            }
            ConstraintKind::EqualNamedField {
                values: [a_id, b_id],
                index: field_name,
                variance,
            } => {
                let a = get_value(&self.values, a_id);

                match &a.kind {
                    ValueKind::Error { .. } => {
                        // TODO: Deal with this case somehow. I think that a good method would be just
                        // to flag the child member as being dependant on an error, e.g. if we knew what this
                        // type was it might be set, so just don't report incompleteness-errors on that value.
                    }
                    ValueKind::Type(None) => {}
                    ValueKind::Type(Some(Type { kind: TypeKind::Buffer, args, .. })) => {
                        match &*field_name {
                            "ptr" => {
                                if let Some(args) = args {
                                    let &[mutability, pointee] = &args[..] else {
                                        unreachable!("All buffer types should have two arguments")
                                    };

                                    // @Performance: This is mega-spam of values, we want to later cache this value
                                    // so we don't have to re-add it over and over.
                                    let mut value_sets = a.value_sets.clone(&mut self.value_sets, true);
                                    // @TODO: We want EqualNamedField constraints to store locations, since these constraints
                                    // are very tightly linked with where they're created, as opposed to Equal.
                                    // And then we can generate a good reason here.
                                    // These reasons aren't correct at all....
                                    let new_value_id = self.values.add(Value {
                                        kind: ValueKind::Type(Some(Type {
                                            kind: TypeKind::Reference,
                                            args: Some(Box::new([mutability, pointee])),
                                        })),
                                        value_sets,
                                    });

                                    self.set_equal(new_value_id, b_id, variance);
                                }
                            }
                            "len" => {
                                // @Performance: This is mega-spam of values, we want to later cache this value
                                // so we don't have to re-add it over and over.

                                let value_sets = a.value_sets.clone(&mut self.value_sets, true);
                                // @TODO: We want EqualNamedField constraints to store locations, since these constraints
                                // are very tightly linked with where they're created, as opposed to Equal.
                                // And then we can generate a good reason here.
                                // These reasons aren't correct at all....
                                let field_type = self.add_int(IntTypeKind::Usize, &value_sets);

                                self.set_equal(field_type, b_id, variance);

                                self.constraints[constraint_id].kind = ConstraintKind::Dead;
                            }
                            _ => {
                                self.errors.push(Error::new(
                                    a_id,
                                    b_id,
                                    ErrorKind::NonexistantName(field_name),
                                ));
                                return;
                            }
                        }
                    }
                    ValueKind::Type(Some(Type { kind: TypeKind::Struct(names), .. })) => {
                        if let Some(pos) = names.iter().position(|&v| v == field_name) {
                            insert_active_constraint(
                                &mut self.constraints,
                                &mut self.available_constraints,
                                &mut self.queued_constraints,
                                Constraint {
                                    kind: ConstraintKind::EqualsField {
                                        values: [a_id, b_id],
                                        index: pos,
                                        variance,
                                    },
                                },
                            );
                        } else {
                            self.errors.push(Error::new(
                                a_id,
                                b_id,
                                ErrorKind::NonexistantName(field_name),
                            ));
                            return;
                        }
                    }
                    ValueKind::Type(Some(Type { kind: TypeKind::Array, .. })) => {
                        // @Correctness: We should have a check that the argument is in range
                        if let Some(_) = field_name.strip_prefix("_").and_then(|v| v.parse::<usize>().ok()) {
                            insert_active_constraint(
                                &mut self.constraints,
                                &mut self.available_constraints,
                                &mut self.queued_constraints,
                                Constraint {
                                    kind: ConstraintKind::EqualsField {
                                        values: [a_id, b_id],
                                        index: 0,
                                        variance,
                                    },
                                },
                            );
                        } else {
                            self.errors.push(Error::new(
                                a_id,
                                b_id,
                                ErrorKind::NonexistantName(field_name),
                            ));
                            return;
                        }
                    }
                    ValueKind::Type(Some(_)) => {
                        self.errors.push(Error::new(
                            a_id,
                            b_id,
                            ErrorKind::NonexistantName(field_name),
                        ));
                        return;
                    }
                    ValueKind::Access(_) | ValueKind::Value(_) => {
                        self.errors.push(Error::new(
                            a_id,
                            b_id,
                            ErrorKind::ValueAndTypesIntermixed,
                        ));
                        return;
                    }
                }
            }
            ConstraintKind::EqualsField {
                values: [a_id, b_id],
                index: field_index,
                variance,
            } => {
                let a = &get_value(&self.values, a_id).kind;

                match a {
                    ValueKind::Error { .. } => {
                    }
                    ValueKind::Type(None) | ValueKind::Type(Some(Type { args: None, .. })) => {}
                    ValueKind::Type(Some(Type { args: Some(fields), .. })) => {
                        if let Some(&field) = fields.get(field_index) {
                            insert_active_constraint(
                                &mut self.constraints,
                                &mut self.available_constraints,
                                &mut self.queued_constraints,
                                Constraint::equal(field, b_id, variance),
                            );
                        } else {
                            self.errors.push(Error::new(
                                a_id,
                                b_id,
                                ErrorKind::IndexOutOfBounds(field_index),
                            ));
                            return;
                        }
                    }
                    ValueKind::Access(_) | ValueKind::Value(_) => {
                        self.errors.push(Error::new(
                            a_id,
                            b_id,
                            ErrorKind::ValueAndTypesIntermixed,
                        ));
                        return;
                    }
                }
            }
            ConstraintKind::Equal {
                values: [a_id, b_id],
                variance,
            } => {
                let values_len = self.values.next_value_id();
                let (a_value, b_value) = self.values.get_disjoint_mut(a_id, b_id);

                use ErrorKind::*;
                match (&mut *a_value, a_id, &mut *b_value, b_id) {
                    (Value { kind: ValueKind::Error, value_sets: error_value_sets, .. }, error_id, non_error, non_error_id)
                    | (non_error, non_error_id, Value { kind: ValueKind::Error, value_sets: error_value_sets, .. }, error_id) => {
                        non_error.value_sets.make_erroneous(&mut self.value_sets);
                        error_value_sets.make_erroneous(&mut self.value_sets);

                        // @Duplicate code with the invariance optimization below, we could probably join them
                        // together somehow.
                        // Any constraints with the value should have the values id changed.
                        // This sets the current equality constraint to dead as well.
                        // This does not queue them, since we queue the values once again later anyway
                        if let Some(affected_constraints) = self.available_constraints.remove(&b_id)
                        {
                            for affected_constraint_id in affected_constraints {
                                let affected_constraint =
                                    &mut self.constraints[affected_constraint_id];
                                for value in affected_constraint.values_mut() {
                                    if *value == b_id {
                                        *value = a_id;
                                        self.available_constraints
                                            .entry(a_id)
                                            .or_insert_with(Vec::new)
                                            .push(affected_constraint_id);
                                    }
                                }

                                affected_constraint.fix_order();
                            }
                        }

                        *a_value = Value {
                            kind: ValueKind::Error,
                            // The value sets of the errors are already set as erroneous, so it doesn't matter that this one is empty.
                            value_sets: ValueSetHandles::already_complete(),
                        };

                        *b_value = Value {
                            kind: ValueKind::Error,
                            value_sets: ValueSetHandles::already_complete(),
                        };

                        if let Some(available_constraints) = self.available_constraints.get_mut(&a_id) {
                            available_constraints.retain(|&constraint| {
                                if matches!(self.constraints[constraint].kind, ConstraintKind::Dead) {
                                    false
                                } else {
                                    self.queued_constraints.push(constraint);
                                    true
                                }
                            });
                        }
                    }
                    (Value { kind: ValueKind::Type(a), .. }, _, Value { kind: ValueKind::Type(b), .. }, _) => {
                        let (a_type, b_type) = match (a, b) {
                            (None, None) => return,
                            (Some(a_type), b_type @ None) => {
                                progress[1] = true;
                                let b_type = b_type.insert(Type {
                                    kind: a_type.kind.clone(),
                                    args: None,
                                });
                                (a_type, b_type)
                            }
                            (a_type @ None, Some(b_type)) => {
                                progress[0] = true;
                                let a_type = a_type.insert(Type {
                                    kind: b_type.kind.clone(),
                                    args: None,
                                });
                                (a_type, b_type)
                            }
                            (Some(a_type), Some(b_type)) => (a_type, b_type),
                        };

                        if a_type.kind != b_type.kind
                            || a_type.args
                                .as_ref()
                                .zip(b_type.args.as_ref())
                                .map_or(false, |(a, b)| a.len() != b.len())
                        {
                            let base_a = a_type.kind.clone();
                            let base_b = b_type.kind.clone();

                            let a_temp = (base_a.clone(), a_type.args.as_ref().map(|v| v.len()));
                            let b_temp = (base_b.clone(), b_type.args.as_ref().map(|v| v.len()));

                            a_value.value_sets.make_erroneous(&mut self.value_sets);
                            b_value.value_sets.make_erroneous(&mut self.value_sets);

                            // @Duplicate code with the invariance optimization below, we could probably join them
                            // together somehow.
                            // Any constraints with the value should have the values id changed.
                            // This sets the current equality constraint to dead as well.
                            if let Some(affected_constraints) =
                                self.available_constraints.remove(&b_id)
                            {
                                for affected_constraint_id in affected_constraints {
                                    let affected_constraint =
                                        &mut self.constraints[affected_constraint_id];
                                    for value in affected_constraint.values_mut() {
                                        if *value == b_id {
                                            *value = a_id;
                                            self.available_constraints
                                                .entry(a_id)
                                                .or_insert_with(Vec::new)
                                                .push(affected_constraint_id);
                                        }
                                    }

                                    affected_constraint.fix_order();

                                    if !matches!(affected_constraint.kind, ConstraintKind::Dead)
                                    {
                                        self.queued_constraints.push(affected_constraint_id);
                                    }
                                }
                            }

                            *self.values.get_mut(a_id) = Value {
                                kind: ValueKind::Error,
                                value_sets: ValueSetHandles::already_complete(),
                            };
                            *self.values.get_mut(b_id) = Value {
                                kind: ValueKind::Error,
                                value_sets: ValueSetHandles::already_complete(),
                            };
                            return;
                        }

                        let [a_progress, b_progress, ..] = &mut progress;
                        match (&mut a_type.args, a_id, a_progress, &mut b_type.args, b_id, b_progress) {
                            (None, _, _, None, _, _) => return,
                            (
                                Some(known),
                                _,
                                _,
                                unknown @ None,
                                unknown_id,
                                unknown_progress,
                            )
                            | (
                                unknown @ None,
                                unknown_id,
                                unknown_progress,
                                Some(known),
                                _,
                                _,
                            ) => {
                                *unknown_progress = true;

                                // We do this weird thing so we can utilize the mutable reference to unknown
                                // before writing to values. After that we have to recompute the references
                                // since they may have moved if the vector grew (one of the cases where
                                // the borrow checker was right!)
                                *unknown = Some((values_len .. values_len + known.len() as u32).collect());

                                let variant_fields = known.clone();

                                let base_value = get_value_mut(&mut self.values, unknown_id);
                                let mut base_value_sets = base_value.value_sets.take();

                                for &v in variant_fields.iter() {
                                    let variant_value = get_value(&self.values, v);
                                    let kind = variant_value.kind.to_unknown();
                                    let new_value = Value {
                                        kind,
                                        value_sets: base_value_sets.clone(&mut self.value_sets, false),
                                    };
                                    self.values.add(new_value);
                                }

                                base_value_sets.complete(&mut self.value_sets);
                                get_value_mut(&mut self.values, unknown_id).value_sets.set_to(base_value_sets);
                            }
                            (Some(_), _, _, Some(_), _, _) => {}
                        };

                        // @Duplicate code from above.
                        let a = get_value(&self.values, a_id);
                        let b = get_value(&self.values, b_id);
                        let (ValueKind::Type(Some(Type { kind: base_a, args: Some(a_fields), .. })), ValueKind::Type(Some(Type { kind: base_b, args: Some(b_fields), .. }))) = (&a.kind, &b.kind) else {
                            // @Speed: Could be replaced with unreachable_unchecked in the real version.
                            unreachable!("Because of computations above, this is always true")
                        };

                        // Ugly special case for references and buffers. This would apply for anything that has a
                        // mutability parameter that controls the variance of another field, because that behaviour
                        // is quite messy and complex.
                        if *base_a == TypeKind::Reference || *base_a == TypeKind::Buffer {
                            // @Cleanup: This has to be done because a has to be less than b, otherwise
                            // the lookups don't work properly. However, this is messy. So it would be nice if it
                            // could be factored out to something else.
                            let (a_access_id, a_inner, b_access_id, b_inner, variance) =
                                if a_fields[0] < b_fields[0] {
                                    (
                                        a_fields[0],
                                        a_fields[1],
                                        b_fields[0],
                                        b_fields[1],
                                        variance,
                                    )
                                } else {
                                    (
                                        b_fields[0],
                                        b_fields[1],
                                        a_fields[0],
                                        a_fields[1],
                                        variance.invert(),
                                    )
                                };

                            let variance_constraint = self
                                .variance_updates
                                .entry((a_access_id, b_access_id))
                                .or_insert_with(|| VarianceConstraint {
                                    variance,
                                    last_variance_applied: Variance::DontCare,
                                    constraints: Vec::new(),
                                });
                            // We use guaranteed_variance instead of last_variance_applied here, since if they are different
                            // it just means the VarianceConstraint has more work to do in the future to catch up, so we may as well
                            // do that work right now, and save some work in the future.
                            let inner_constraint = Constraint::equal(
                                a_inner,
                                b_inner,
                                Variance::DontCare.apply_to(variance),
                            );
                            if let Some(inner_constraint_id) = insert_constraint(
                                &mut self.constraints,
                                &mut self.available_constraints,
                                inner_constraint,
                            ) {
                                if !variance_constraint
                                    .constraints
                                    .iter()
                                    .any(|(v, _)| v == &inner_constraint_id)
                                {
                                    variance_constraint
                                        .constraints
                                        .push((inner_constraint_id, variance));
                                    self.queued_constraints.push(inner_constraint_id);
                                }
                            }
                            insert_active_constraint(
                                &mut self.constraints,
                                &mut self.available_constraints,
                                &mut self.queued_constraints,
                                Constraint::equal(a_access_id, b_access_id, variance),
                            );
                        } else if *base_a == TypeKind::Function {
                            insert_active_constraint(
                                &mut self.constraints,
                                &mut self.available_constraints,
                                &mut self.queued_constraints,
                                Constraint::equal(
                                    a_fields[0],
                                    b_fields[0],
                                    variance,
                                ),
                            );
                            for (&a_field, &b_field) in a_fields[1..].iter().zip(&b_fields[1..])
                            {
                                insert_active_constraint(
                                    &mut self.constraints,
                                    &mut self.available_constraints,
                                    &mut self.queued_constraints,
                                    Constraint::equal(a_field, b_field, variance.invert()),
                                );
                            }
                        } else {
                            // Now, we want to apply equality to all the fields as well.
                            for (&a_field, &b_field) in a_fields.iter().zip(&**b_fields) {
                                // @Improvement: Later, variance should be definable in a much more generic way(for generic types).
                                // In a generic type, you could paramaterize the mutability of something, which might then influence
                                // the variance of other parameters.
                                insert_active_constraint(
                                    &mut self.constraints,
                                    &mut self.available_constraints,
                                    &mut self.queued_constraints,
                                    Constraint::equal(a_field, b_field, variance),
                                );
                            }
                        }
                    }

                    (Value { kind: ValueKind::Value(a), value_sets: a_value_sets, .. }, _, Value { kind: ValueKind::Value(b), value_sets: b_value_sets, .. }, _) => {
                        match (&mut *a, &mut *b) {
                            (None, None) => {},
                            (Some(a), None) => {
                                if a.value.is_some() {
                                    b_value_sets.complete(&mut self.value_sets);
                                }
                                // @Correctness: Should this type be a part of the current value set?
                                // @Cleanup: This is from a self.values.len() call further up, no elements have been
                                // added because of the borrow checker. But the fact that the call has to be up there
                                // is also because of the borrow checker!!!
                                let type_ = values_len;
                                *b = Some(Constant {
                                    type_,
                                    value: a.value,
                                });
                                insert_active_constraint(
                                    &mut self.constraints,
                                    &mut self.available_constraints,
                                    &mut self.queued_constraints,
                                    Constraint::equal(a.type_, type_, variance),
                                );

                                // @HACK! We assume that no values were added in between here, and that the id of
                                // the inserted type is the same. This isn't too unreasonable, because we never
                                // borrow `self.values`
                                self.add_unknown_type();
                                    
                                progress[1] = true;
                            }
                            (None, Some(b)) => {
                                if b.value.is_some() {
                                    a_value_sets.complete(&mut self.value_sets);
                                }
                                // @Correctness: Should this type be a part of the current value set?
                                // @Cleanup: This is from a self.values.len() call further up, no elements have been
                                // added because of the borrow checker. But the fact that the call has to be up there
                                // is also because of the borrow checker!!!
                                let type_ = values_len;
                                *a = Some(Constant {
                                    type_,
                                    value: b.value,
                                });
                                insert_active_constraint(
                                    &mut self.constraints,
                                    &mut self.available_constraints,
                                    &mut self.queued_constraints,
                                    Constraint::equal(type_, b.type_, variance),
                                );

                                // @HACK! We assume that no values were added in between here, and that the id of
                                // the inserted type is the same. This isn't too unreasonable, because we never
                                // borrow `self.values`
                                self.add_unknown_type();
                                progress[0] = true;
                            }
                            (Some(a), Some(b)) => {
                                let a_type = a.type_;
                                let b_type = b.type_;

                                // @TODO: We want to also combine the reasons for the values here.
                                match (&mut a.value, &mut b.value) {
                                    (None, None) => {},
                                    (Some(a_value), b_value @ None) => {
                                        *b_value = Some(*a_value);
                                        b_value_sets.complete(&mut self.value_sets);
                                        progress[1] = true;
                                    }
                                    (a_value @ None, Some(b_value)) => {
                                        *a_value = Some(*b_value);
                                        a_value_sets.complete(&mut self.value_sets);
                                        progress[1] = true;
                                    }
                                    (Some(a_constant), Some(b_constant)) => {
                                        if *a_constant != *b_constant {
                                            let a_constant = *a_constant;
                                            a_value.value_sets.make_erroneous(&mut self.value_sets);
                                            *a_value = Value {
                                                kind: ValueKind::Error,
                                                value_sets: ValueSetHandles::already_complete(),
                                            };
                                            // @HACK: I do this so I don't have to do some annoying manipulation more than necessary,
                                            // this should not actually be done.
                                            self.queued_constraints.push(constraint_id);
                                        }
                                    }
                                }

                                self.set_equal(a_type, b_type, variance);
                            }
                        }
                    }
                    (Value { kind: ValueKind::Access(a), value_sets: a_value_sets, .. }, _, Value { kind: ValueKind::Access(b), value_sets: b_value_sets, .. }, _) => {
                        let a = a.get_or_insert_with(|| {
                            a_value_sets.complete(&mut self.value_sets);
                            Access::default()
                        });
                        let b = b.get_or_insert_with(|| {
                            b_value_sets.complete(&mut self.value_sets);
                            Access::default()
                        });

                        let old = (*a, *b);
                        a.combine_with(b, variance);
                        let different = (*a, *b) != old;

                        progress[0] = different;
                        progress[1] = different;

                        if a.needs_write() && a.cannot_write() || a.needs_read() && a.cannot_read()
                        || b.needs_write() && b.cannot_write() || b.needs_read() && b.cannot_read() {
                            a.combine_with(b, Variance::Invariant);
                            let access = a.clone();
                            let value = get_value_mut(&mut self.values, a_id);
                            value.value_sets.make_erroneous(&mut self.value_sets);
                            *value = Value {
                                kind: ValueKind::Error,
                                value_sets: ValueSetHandles::already_complete(),
                            };
                            // @HACK: I do this so I don't have to do some annoying manipulation more than necessary,
                            // this should not actually be done.
                            self.queued_constraints.push(constraint_id);
                        } else if let Some(variance_constraint) =
                            self.variance_updates.get_mut(&(a_id, b_id))
                        {
                            run_variance_constraint(
                                variance_constraint,
                                a_id,
                                b_id,
                                &self.values,
                                &mut self.constraints,
                                &mut self.available_constraints,
                                &mut self.queued_constraints,
                            );
                        }
                    }
                    _ => {
                        // TODO: We should generate an error value in this case.
                        self.errors
                            .push(Error::new(a_id, b_id, MixingTypesAndValues));
                    }
                }

                self.values.structurally_combine(a_id, b_id);
            }
        }

        for (value_id, progress) in constraint.values().iter().zip(progress) {
            if progress {
                self.queued_constraints.extend(
                    self.available_constraints
                        .get(value_id)
                        .iter()
                        .flat_map(|v| v.iter())
                        .copied()
                        .filter(|v| v != &constraint_id),
                );
            }
        }
    }

    pub fn params(&self, value: ValueId) -> Option<&[ValueId]> {
        match get_value(&self.values, value) {
            Value {
                kind: ValueKind::Type(Some(Type { ref args, .. })),
                ..
            } => args.as_deref(),
            _ => None,
        }
    }

    pub fn add(&mut self, value: ValueKind, set: ValueSetId) -> ValueId {
        let value_sets = self.value_sets.with_one(set, value.is_complete());
        self.values.add(Value {
            kind: value,
            value_sets,
        })
    }

    pub fn add_without_reason(&mut self, value: ValueKind, set: ValueSetId) -> ValueId {
        // @Cleanup: We could clean this up by having a concept of "complete" and "incomplete" values.
        let value_sets = self.value_sets.with_one(set, value.is_complete());
        self.values.add(Value {
            kind: value,
            value_sets,
        })
    }

    /// Adds a value set to a value. This value has to be an unknown type, otherwise it will panic
    /// in debug mode. It also cannot be an alias. This is solely intended for use by the building
    /// process of the typer.
    pub fn set_value_set(&mut self, value_id: ValueId, value_set_id: ValueSetId) {
        let value = self.values.get_mut(value_id);

        // There can be no children, this function shouldn't have to recurse.
        debug_assert!(matches!(value.kind, ValueKind::Type(None)));

        // We don't want to worry about sorting or binary searching
        value.value_sets.set_to(self.value_sets.with_one(value_set_id, false));
    }

    pub fn add_unknown_type_with_set(&mut self, set: ValueSetId) -> ValueId {
        self.values.add(Value {
            kind: ValueKind::Type(None),
            value_sets: self.value_sets.with_one(set, false),
        })
    }

    pub fn add_compiler_type(&mut self, type_: types::Type, set: ValueSetId) -> ValueId {
        match *type_.kind() {
            types::TypeKind::Function { ref args, returns } => {
                let mut new_args = Vec::with_capacity(args.len() + 1);

                // @TODO: We should append the sub-expression used to the reason as well.
                new_args.push(self.add_compiler_type(returns, set));

                for &arg in args {
                    new_args.push(self.add_compiler_type(arg, set));
                }

                self.add_type(TypeKind::Function, &new_args[..], set)
            }
            types::TypeKind::Int(int_type_kind) => {
                let v = self.add_unknown_type();
                self.set_int(v, int_type_kind, set);
                v
            }
            types::TypeKind::Empty => self.add_type(TypeKind::Empty, [], set),
            types::TypeKind::Bool  => self.add_type(TypeKind::Bool, [], set),
            types::TypeKind::Buffer { pointee, permits } => {
                // @Cleanup: This is ugly!
                let permits = self.add_access(Some(Access::disallows(!permits.read(), !permits.write())), set);
                let pointee = self.add_compiler_type(pointee, set);

                self.add_type(TypeKind::Buffer, [permits, pointee], set)
            }
            types::TypeKind::Reference { pointee, permits } => {
                // @Cleanup: This is ugly!
                let permits = self.add_access(Some(Access::disallows(!permits.read(), !permits.write())), set);
                let pointee = self.add_compiler_type(pointee, set);

                self.add_type(TypeKind::Reference, [permits, pointee], set)
            }
            types::TypeKind::Array(type_, length) => {
                todo!("We need a function for turning a compiler type into an actionable type that also takes the program");
            }
            types::TypeKind::Struct(ref fields) => {
                let field_names = fields.iter().map(|&(v, _)| v).collect();
                let field_types: Box<[_]> = fields
                    .iter()
                    // @TODO: We should append the sub-expression used to the reason as well.
                    .map(|&(_, v)| self.add_compiler_type(v, set))
                    .collect();
                self.add_type(TypeKind::Struct(field_names), field_types, set)
            }
            _ => todo!("This compiler type is not done yet"),
        }
    }

    #[track_caller]
    pub fn set_type(&mut self, value_id: ValueId, kind: TypeKind, args: impl IntoBoxSlice<ValueId>, set: impl IntoValueSet) -> ValueId {
        let value @ Value { kind: ValueKind::Type(None), .. } = self.values.get_mut(value_id) else {
            unreachable!("Cannot call set_type on anything other than an unknown type")
        };

        let args = args.into_box_slice();
        let is_complete = args.is_some();
        let value_sets = set.add_set(&mut self.value_sets, is_complete);
        value.kind = ValueKind::Type(Some(Type {
            kind,
            args,
        }));
        if is_complete {
            value.value_sets.complete(&mut self.value_sets);
        }
        value.value_sets.take_from(value_sets, &mut self.value_sets);

        value_id
    }

    pub fn add_int(&mut self, int_kind: IntTypeKind, set: impl IntoValueSet) -> ValueId {
        let id = self.add_unknown_type();
        self.set_int(id, int_kind, set);
        id
    }

    // @Speed: This creates a temporary, but is also a kind of temporary value itself....
    pub fn set_int(&mut self, value_id: ValueId, int_kind: IntTypeKind, set: impl IntoValueSet) {
        let (signed, size) = match int_kind {
            IntTypeKind::U8    => (static_values::FALSE, static_values::ONE),
            IntTypeKind::U16   => (static_values::FALSE, static_values::TWO),
            IntTypeKind::U32   => (static_values::FALSE, static_values::FOUR),
            IntTypeKind::U64   => (static_values::FALSE, static_values::EIGHT),
            IntTypeKind::Usize => (static_values::FALSE, static_values::POINTER),
            IntTypeKind::I8    => (static_values::TRUE,  static_values::ONE),
            IntTypeKind::I16   => (static_values::TRUE,  static_values::TWO),
            IntTypeKind::I32   => (static_values::TRUE,  static_values::FOUR),
            IntTypeKind::I64   => (static_values::TRUE,  static_values::EIGHT),
            IntTypeKind::Isize => (static_values::TRUE,  static_values::POINTER),
        };

        self.set_type(value_id, TypeKind::Int, [signed, size], set);
    }

    pub fn add_type(&mut self, kind: TypeKind, args: impl IntoBoxSlice<ValueId>, set: impl IntoValueSet) -> ValueId {
        let args = args.into_box_slice();
        let is_complete = args.is_some();
        let value_sets = set.add_set(&mut self.value_sets, is_complete);
        self.values.add(Value {
            kind: ValueKind::Type(Some(Type {
                kind,
                args,
            })),
            value_sets,
        })
    }

    pub fn add_unknown_type(&mut self) -> ValueId {
        self.values.add(Value {
            kind: ValueKind::Type(None),
            value_sets: ValueSetHandles::default(),
        })
    }

    pub fn add_value(&mut self, type_: ValueId, value: impl IntoConstant, set: impl IntoValueSet) -> ValueId {
        let value = value.into_constant();
        let is_complete =  value.is_some();
        let value_sets = set.add_set(&mut self.value_sets, is_complete);
        self.values.add(Value {
            kind: ValueKind::Value(Some(Constant {
                type_,
                value,
            })),
            value_sets,
        })
    }

    pub fn add_empty_access(&mut self, set: ValueSetId) -> ValueId {
        self.values.add(Value {
            kind: ValueKind::Access(None),
            value_sets: self.value_sets.with_one(set, false),
        })
    }

    pub fn add_access(
        &mut self,
        access: Option<Access>,
        set: ValueSetId,
    ) -> ValueId {
        self.add(ValueKind::Access(access), set)
    }
}

/// If a and b are accesses permissions used to determine the variance of an operation, and they are "equal" with a variance
/// relationship, what variance is the operation required to have at least?
///
/// Variances are seen as constraints, so if the operation _could_ be Invariant, this function may still return Covariant or
/// Variant, because applying both Covariant "equality" and Invariant "equality" is the same as just applying Invariant "equality".
fn biggest_guaranteed_variance_of_operation(a: &Option<Access>, b: &Option<Access>, variance: Variance) -> Variance {
    let (a_read, a_write) = a.as_ref().map_or((false, false), |v| (v.needs_read(), v.needs_write()));
    let (b_read, b_write) = b.as_ref().map_or((false, false), |v| (v.needs_read(), v.needs_write()));

    let (needs_read, needs_write) = match variance {
        Variance::Variant => (b_read, b_write),
        Variance::Covariant => (a_read, a_write),
        Variance::Invariant => (a_read || b_read, a_write || b_write),
        Variance::DontCare => (a_read && b_read, a_write && b_write),
    };

    match (needs_read, needs_write) {
        (true, true) => Variance::Invariant,
        (false, true) => Variance::Covariant,
        (true, false) => Variance::Variant,
        (false, false) => Variance::DontCare,
    }
}

fn run_variance_constraint(
    constraint: &mut VarianceConstraint,
    a: ValueId,
    b: ValueId,
    values: &Values,
    constraints: &mut Vec<Constraint>,
    available_constraints: &mut HashMap<ValueId, Vec<ConstraintId>>,
    queued_constraints: &mut Vec<ConstraintId>,
) {
    let ValueKind::Access(a_access) = &get_value(&values, a).kind else { panic!() };
    let ValueKind::Access(b_access) = &get_value(&values, b).kind else { panic!() };

    let new_variance = biggest_guaranteed_variance_of_operation(
        a_access,
        b_access,
        constraint.variance,
    );

    if new_variance != constraint.last_variance_applied {
        for &(constraint, variance) in &constraint.constraints {
            // If the constraint doesn't have a variance we don't even care, since it won't
            // depend on this system anyways, and when it was inserted all the logic it could use would have been
            // run already.
            if let Some(variance_mut) = constraints[constraint].variance_mut() {
                let old = *variance_mut;
                variance_mut.combine(new_variance.apply_to(variance));
                if old != *variance_mut {
                    queued_constraints.push(constraint);
                }
            }
        }
        constraint.last_variance_applied = new_variance;
    }
}
