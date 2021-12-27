//! Type inferrence system
//!
//! # Will try and document more later once I feel fairly done with the first version of this system, but for now just some generic info I want to put here

const DEBUG: bool = false;

pub mod static_values {
    //! Static value header, e.g. value indices we know what their values are statically, for very common types,
    //! like integers and so on.
    use super::ValueId;

    pub const INT_SIZE : ValueId = 0;
    pub const BOOL     : ValueId = 1;
    pub const POINTER  : ValueId = 2;
    pub const ONE      : ValueId = 4;
    pub const TWO      : ValueId = 6;
    pub const FOUR     : ValueId = 8;
    pub const EIGHT    : ValueId = 10;
    pub const TRUE     : ValueId = 12;
    pub const FALSE    : ValueId = 14;
    pub const EMPTY    : ValueId = 16;
    pub const USIZE    : ValueId = 17;
    pub const STATIC_VALUES_SIZE : u32 = 18;
}

use crate::program::Program;
use crate::errors::ErrorCtx;
use crate::location::Location;
use crate::operators::BinaryOp;
use crate::types::{self, IntTypeKind};
use std::collections::{hash_map, HashMap};
use std::mem;
use ustr::Ustr;
use crate::program::constant::ConstantRef;

mod explain;
pub use explain::{get_reasons, Reason, ReasonKind};

mod value_sets;
pub use value_sets::{ValueSets, ValueSetId, ValueSetHandles, ValueSet};

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

pub trait IntoValueArgs {
    type IntoIter: IntoIterator<Item = (ValueId, Reason)>;

    fn into_value_args(self) -> Option<Self::IntoIter>;
}

impl IntoValueArgs for () {
    type IntoIter = std::iter::Empty<(ValueId, Reason)>;

    fn into_value_args(self) -> Option<Self::IntoIter> {
        None
    }
}

pub struct Args<T>(pub T);
impl<T> IntoValueArgs for Args<T> where T: IntoIterator<Item = (ValueId, Reason)> {
    type IntoIter = T;

    fn into_value_args(self) -> Option<Self::IntoIter> {
        Some(self.0)
    }
}

pub trait IntoValueSet {
    fn add_set(&self, value_sets: &mut ValueSets) -> ValueSetHandles;
}

impl IntoValueSet for () {
    fn add_set(&self, _value_sets: &mut ValueSets) -> ValueSetHandles {
        ValueSetHandles::empty()
    }
}

impl IntoValueSet for &ValueSetHandles {
    fn add_set(&self, value_sets: &mut ValueSets) -> ValueSetHandles {
        (*self).clone(value_sets)
    }
}

impl IntoValueSet for ValueSetId {
    fn add_set(&self, value_sets: &mut ValueSets) -> ValueSetHandles {
        value_sets.with_one(*self)
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

// A struct that maps from value ids to Poly args / Ast node / Local / Label ids or vice versa
#[derive(Clone)]
pub struct IdMapper {
    pub poly_args: usize,
    pub ast_nodes: usize,
    pub locals: usize,
    pub labels: usize,
}

pub enum MappedId {
    PolyArg(usize),
    AstNode(crate::parser::NodeId),
    Local(crate::locals::LocalId),
    Label(crate::locals::LabelId),
    None,
}

impl IdMapper {
    pub fn map(&self, value: ValueId) -> MappedId {
        let mut id = value;
        if id < static_values::STATIC_VALUES_SIZE {
            return MappedId::None;
        }
        id -= static_values::STATIC_VALUES_SIZE;

        if id < self.poly_args as _ {
            return MappedId::PolyArg(id as usize);
        }
        id -= self.poly_args as ValueId;

        if id < self.ast_nodes as _ {
            return MappedId::AstNode(crate::parser::NodeId(id));
        }
        id -= self.ast_nodes as ValueId;

        if id < self.locals as _ {
            return MappedId::Local(crate::locals::LocalId(id as _));
        }
        id -= self.locals as ValueId;

        if id < self.labels as _ {
            return MappedId::Label(crate::locals::LabelId(id as _));
        }

        MappedId::None
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeKind {
    // bool, int size
    Int,
    // No arguments, the size of an integer, hidden type that the user cannot access
    IntSize,

    Bool,
    Empty,
    Type,

    // return, (arg0, arg1, arg2, ...)
    Function,
    // element: type, length: int
    Array,
    // + has variance
    // type
    Reference,
    // + has variance
    // type
    Buffer,
    // (type, type, type, type), in the same order as the strings.
    Struct(Box<[Ustr]>),

    // no fields
    ConstantValue(ConstantRef),
    // type, constant_ref(has to be a ConstantValue)
    // * layout is the layout of the type of the constant, even though a constant having a layout doesn't make sense
    Constant,
}

impl TypeKind {
    fn get_needed_children_for_layout<'a>(&self, children: &'a [ValueId]) -> &'a [ValueId] {
        match self {
            TypeKind::Type | TypeKind::IntSize | TypeKind::Bool | TypeKind::Empty | TypeKind::Function | TypeKind::Reference | TypeKind::Buffer | TypeKind::ConstantValue(_) => &[],
            TypeKind::Int => &children[1..2],
            TypeKind::Array => children,
            TypeKind::Struct(_) => children,
            // A constant pretends to care about the actual ConstantValue for the layout as well. This is not
            // because it "needs" to itself, but because things that need the constant, like the arrays layout,
            // does actually care about the value, so if it isn't required we get problems.
            TypeKind::Constant => children,
        }
    }
}

fn compute_type_layout(kind: &TypeKind, values: &Values, children: &[ValueId]) -> Layout {
    match kind {
        TypeKind::Int => {
            let size = extract_constant_from_value(values, children[1]).unwrap();
            // @Correctness: We want to make sure that the type actually is a u8 here
            let size_value = unsafe { *size.as_ptr().cast::<u8>() };
            let size_bytes = match size_value {
                0 => 8,
                1 => 1,
                2 => 2,
                4 => 4,
                8 => 8,
                _ => unreachable!("Invalid int size"),
            };
            Layout { size: size_bytes, align: size_bytes }
        }
        TypeKind::IntSize => Layout { size: 1, align: 1 },
        TypeKind::Bool => Layout { size: 1, align: 1 },
        TypeKind::Empty => Layout { size: 0, align: 1 },
        TypeKind::Buffer => Layout { size: 16, align: 8 },
        TypeKind::Type => Layout { size: 8, align: 8 },
        TypeKind::Reference | TypeKind::Function => Layout { size: 8, align: 8 },
        TypeKind::Array => {
            // @Correctness: We want to make sure that the type actually is a usize here
            let length = extract_constant_from_value(values, children[1]).unwrap();
            let length = unsafe { *length.as_ptr().cast::<usize>() };
            let inner_layout = values.get(children[0]).layout;
            debug_assert!(inner_layout.align != 0);
            Layout { size: length * inner_layout.size, align: inner_layout.align }
        }
        TypeKind::Struct(_) => {
            let mut size = 0;
            let mut align = 1;
            for &child in children {
                let child_layout = values.get(child).layout;
                debug_assert_ne!(child_layout.align, 0);
                size += child_layout.size;
                align = align.max(child_layout.align);
                size = crate::types::to_align(size, child_layout.align);
            }
            size = crate::types::to_align(size, align);
            Layout { size, align }
        }
        TypeKind::ConstantValue(_) => Layout { size: 0, align: 1 },
        TypeKind::Constant => *values.get(children[0]).layout,
    }
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

#[derive(Debug, Clone)]
pub struct Type {
    pub kind: TypeKind,
    pub args: Option<Box<[ValueId]>>,
}

impl Type {
    fn is_complete(&self) -> bool {
        self.args.is_some()
    }
}

type ConstraintId = usize;

#[derive(Debug, Clone, Copy)]
struct Constraint {
    kind: ConstraintKind,
    applied: bool,
    reason: Reason,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum Relation {
    Cast,
    BufferEqualsArray,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum ConstraintKind {
    Relation {
        kind: Relation,
        values: [ValueId; 2],
    },
    BinaryOp {
        op: BinaryOp,
        values: [ValueId; 3],
    },
    Equal {
        values: [ValueId; 2],
        creator: Option<ConstraintId>,
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
        hidden_subdivisions: u8,
    },
}

impl Constraint {
    /// Fixes the order of the fields, or sets the constraint to Dead if it becomes redundant.
    fn fix_order(&mut self) {
        match &mut self.kind {
            ConstraintKind::Equal {
                values: [a, b],
                variance,
                ..
            } => {
                if a == b {
                    self.applied = true;
                } else if a > b {
                    mem::swap(a, b);
                    *variance = variance.invert();
                }
            }
            ConstraintKind::EqualsField { .. }
            | ConstraintKind::EqualNamedField { .. }
            | ConstraintKind::BinaryOp { .. }
            | ConstraintKind::Relation { .. } => {}
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
            ConstraintKind::Relation { values, .. } => &*values,
            ConstraintKind::Equal { values, .. }
            | ConstraintKind::EqualsField { values, .. }
            | ConstraintKind::EqualNamedField { values, .. } => &*values,
            ConstraintKind::BinaryOp { values, .. } => &*values,
        }
    }

    fn values_mut(&mut self) -> &mut [ValueId] {
        match &mut self.kind {
            ConstraintKind::Relation { values, .. } => &mut *values,
            ConstraintKind::Equal { values, .. }
            | ConstraintKind::EqualsField { values, .. }
            | ConstraintKind::EqualNamedField { values, .. } => &mut *values,
            ConstraintKind::BinaryOp { values, .. } => &mut *values,
        }
    }

    fn variance_mut(&mut self) -> Option<&mut Variance> {
        match &mut self.kind {
            ConstraintKind::Equal { variance, .. }
            | ConstraintKind::EqualsField { variance, .. }
            | ConstraintKind::EqualNamedField { variance, .. } => Some(variance),
            ConstraintKind::BinaryOp { .. } | ConstraintKind::Relation { .. } => None,
        }
    }

    fn equal(a: ValueId, b: ValueId, variance: Variance, creator: Option<ConstraintId>, reason: Reason) -> Self {
        let kind = ConstraintKind::Equal {
            values: [a, b],
            variance,
            creator,
        };

        Self { kind, reason, applied: false }
    }
}

#[derive(Debug, Clone)]
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

#[derive(Debug, Clone)]
pub enum ErrorKind {
    NonexistantOperation,
    MixingTypesAndValues,
    IncompatibleTypes(ConstraintId),
    ValueAndTypesIntermixed,
    IndexOutOfBounds(usize),
    NonexistantName(Ustr),
}

pub fn extract_constant_from_value(values: &Values, value: ValueId) -> Option<ConstantRef> {
    let Some(Type { kind: TypeKind::Constant, args: Some(args) }) = values.get(value).kind else {
        return None
    };

    let Some(Type { kind: TypeKind::ConstantValue(constant_ref), .. }) = values.get(*args.get(1)?).kind else {
        return None;
    };

    Some(*constant_ref)
}

// Temporary, until we move to calling values.get immediately.
fn get_value(values: &Values, id: ValueId) -> ValueBorrow<'_> {
    values.get(id)
}

fn get_value_mut(values: &mut Values, id: ValueId) -> ValueBorrowMut<'_> {
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
        TypeKind::Type => write!(string, "type"),
        TypeKind::Constant => write!(string, "constant"),
        TypeKind::ConstantValue(_) => write!(string, "<constant value>"),
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

#[derive(Debug, Clone)]
struct Value {
    value_sets: ValueSetHandles,
    is_base_value: bool,
}

#[derive(Clone, Copy)]
pub struct ValueBorrow<'a> {
    pub kind: &'a Option<Type>,
    pub layout: &'a Layout,
    value_sets: &'a ValueSetHandles,
    is_base_value: &'a bool,
}

impl ValueBorrow<'_> {
    pub fn kind(&self) -> &TypeKind {
        &self.kind.as_ref().expect("Called kind on unknown type").kind
    }
}

pub struct ValueBorrowMut<'a> {
    pub kind: &'a mut Option<Type>,
    pub layout: &'a mut Layout,
    value_sets: &'a mut ValueSetHandles,
    pub is_base_value: &'a mut bool,
}

struct LookupElement {
    internal_id: u32,
    // u32::MAX is None
    next_in_lookup: u32,
}

// @Temporary: Should be replaced with the real value some day
#[derive(Clone)]
struct ValueWrapper {
    value: Value,
    structure_id: u32,
    // u32::MAX means that there is nothing.
    next_in_structure_group: u32,
}

#[derive(Default, Clone, Copy)]
pub struct Layout {
    pub size: usize,
    // An align of zero means that the size hasn't been calculated yet, and the number is how many children types
    // have to be known.
    pub align: usize,
}

#[derive(Clone, Default)]
struct StructureGroup {
    first_value: ValueId,
    kind: Option<Type>,
    layout: Layout,
    layout_dependants: Vec<ValueId>,
    num_values: u32,
}

#[derive(Clone)]
pub struct Values {
    structure: Vec<StructureGroup>,
    values: Vec<ValueWrapper>,
}

impl Values {
    fn new() -> Self {
        Self {
            structure: Vec::new(),
            values: Vec::with_capacity(32),
        }
    }

    fn iter_values_in_structure(&self, value_id: ValueId) -> impl Iterator<Item = ValueId> + '_ {
        let structure = &self.structure[self.values[value_id as usize].structure_id as usize];

        let values = &self.values;
        let mut value_id = structure.first_value;

        std::iter::from_fn(move || {
            if value_id == u32::MAX { return None; }
            let v = value_id;
            let value = &values[value_id as usize];
            value_id = value.next_in_structure_group;
            Some(v)
        })
    }
    
    fn structure_id_of_value(&self, value_id: ValueId) -> u32 {
        self.values[value_id as usize].structure_id
    }

    // @Cleanup: Move this out of function? It's going to get pretty situation specific I feel like
    fn structurally_combine(&mut self, computable_sizes: &mut Vec<ValueId>, value_sets: &mut ValueSets, a: ValueId, b: ValueId) {
        let a_value = &self.values[a as usize];
        let structure_id = a_value.structure_id;
        let a_value_is_complete = a_value.value.value_sets.is_complete();
        let b_value = &self.values[b as usize];
        let old_b_structure_id = b_value.structure_id;
        let b_value_is_complete = b_value.value.value_sets.is_complete();
        debug_assert!(!(b_value_is_complete && !a_value_is_complete), "b can't be complete while a isn't, because a will replace b, so it makes no sense for b not to be complete?");

        if structure_id == old_b_structure_id {
            return;
        }

        let b_structure = mem::take(&mut self.structure[old_b_structure_id as usize]);
        let a_structure = &mut self.structure[structure_id as usize];
        a_structure.num_values += b_structure.num_values;
        match (a_structure.layout.align > 0, b_structure.layout.align > 0) {
            (true, false) => {
                for dependant in b_structure.layout_dependants {
                    let dependant_structure_id = self.values[dependant as usize].structure_id;
                    let dependant_structure = &mut self.structure[dependant_structure_id as usize];

                    // This seems scary, but in the cases we're in right now, where a complete structure combines
                    // with an incomplete structure, and the incomplete structure _has children_, those children
                    // will still have the incomplete parent as a layout dependant. Those children will reach this
                    // point in the code, with the dependant structure align already being 0. The reason this works
                    // at all, is that the only case where the align isn't 0, is this case. In all other cases, we
                    // can combine the sizes of the two incomplete structures, and then the dependants are all happy.
                    if dependant_structure.layout.align == 0 {
                        dependant_structure.layout.size -= 1;
                        if dependant_structure.layout.size == 0 {
                            computable_sizes.push(dependant);
                        }
                    }
                }
            }
            (false, false) => {
                debug_assert_eq!(b_structure.layout.align, 0);
                a_structure.layout.size += b_structure.layout.size;
                a_structure.layout_dependants.extend(b_structure.layout_dependants);
            }
            (true, true) => {}
            (false, true) => unreachable!("This shouldn't happen"),
        }

        // Join the two linked lists together
        let mut value_id = a;
        loop {
            let value = &mut self.values[value_id as usize];
            if value.next_in_structure_group == u32::MAX {
                value.next_in_structure_group = b_structure.first_value;
                break;
            }
            value_id = value.next_in_structure_group;
        }

        // Convert the old structure list to the new structure
        let mut value_id = b_structure.first_value;
        loop {
            let value = &mut self.values[value_id as usize];
            if a_value_is_complete && !b_value_is_complete {
                value.value.value_sets.complete(value_sets);
            }
            value.structure_id = structure_id;
            if value.next_in_structure_group == u32::MAX {
                break;
            }
            value_id = value.next_in_structure_group;
        }
    }

    fn compute_size(&mut self, computable_sizes: &mut Vec<ValueId>, id: ValueId, value_sets: &mut ValueSets) {
        let id = self.values[id as usize].structure_id;
        let structure = &self.structure[id as usize];
        if structure.layout.align > 0 {
            // We already know what the layout
            return;
        }
        let Some(Type { kind, args: Some(args) }) = &structure.kind else {
            unreachable!("Cannot call compute_size on an incomplete value")
        };
        let layout = compute_type_layout(kind, self, args);

        let structure = &mut self.structure[id as usize];
        structure.layout = layout;

        // Because we've computed the layout, we can complete all the value sets.
        let mut value_id = structure.first_value;
        loop {
            let value = &mut self.values[value_id as usize];
            value.value.value_sets.complete(value_sets);
            if value.next_in_structure_group == u32::MAX {
                break;
            }
            value_id = value.next_in_structure_group;
        }

        let layout_dependants = mem::take(&mut structure.layout_dependants);
        for dependant in layout_dependants {
            let value = self.get_mut(dependant);
            if value.layout.align == 0 {
                value.layout.size -= 1;
                if value.layout.size == 0 {
                    computable_sizes.push(dependant);
                }
            }
        }
    }

    fn set(&mut self, id: ValueId, kind: Type, value_sets: &mut ValueSets, value_set_handles: ValueSetHandles) {
        let value = &mut self.values[id as usize];
        let structure_id = value.structure_id;

        value.value.value_sets.take_from(value_set_handles, value_sets);

        let mut layout = Layout::default();
        if let Type { args: Some(args), kind } = &kind {
            let mut number = 0;
            // @Improvement: We need to figure out how to recursively determine
            // type completion, for when we're going to insert it as a type
            // id.
            for &needed in args.iter() { // kind.get_needed_children_for_layout(&args) {
                let structure = &mut self.structure[self.values[needed as usize].structure_id as usize];
                if structure.layout.align == 0 {
                    number += 1;
                    structure.layout_dependants.push(id);
                }
            }

            if number == 0 {
                layout = compute_type_layout(kind, self, args);

                // Since there is only one value in the structure, this is fine
                let value = &mut self.values[id as usize];
                value.value.value_sets.complete(value_sets);
            } else {
                layout.size = number;
            }
        }

        let structure = &mut self.structure[structure_id as usize];
        debug_assert_eq!(structure.layout.size, 0);
        debug_assert_eq!(structure.layout.align, 0);
        debug_assert_eq!(structure.num_values, 1);
        // debug_assert!(structure.layout_dependants.is_empty());
        structure.kind = Some(kind);
        structure.layout = layout;
    }

    fn add(&mut self, kind: Option<Type>, value_sets: &mut ValueSets, value_set_handles: ValueSetHandles) -> ValueId {
        let structure_id = self.structure.len() as u32;
        let id = self.values.len() as u32;
        assert!(id < u32::MAX, "Too many values, overflows a u32");

        self.structure.push(StructureGroup {
            first_value: structure_id,
            kind: None,
            layout: Layout::default(),
            layout_dependants: Vec::new(),
            num_values: 1,
        });
        self.values.push(ValueWrapper {
            value: Value { value_sets: value_set_handles, is_base_value: false },
            structure_id,
            next_in_structure_group: u32::MAX,
        });
        if let Some(kind) = kind {
            self.set(id, kind, value_sets, ValueSetHandles::default());
        }
        id
    }

    fn iter(&self) -> impl Iterator<Item = &Value> {
        self.values.iter().map(|v| &v.value)
    }

    fn iter_mut(&mut self) -> impl Iterator<Item = &mut Value> {
        self.values.iter_mut().map(|v| &mut v.value)
    }

    pub fn get(&self, id: ValueId) -> ValueBorrow<'_> {
        let value = &self.values[id as usize];
        let structure = &self.structure[value.structure_id as usize];
        ValueBorrow {
            kind: &structure.kind,
            layout: &structure.layout,
            value_sets: &value.value.value_sets,
            is_base_value: &value.value.is_base_value,
        }
    }

    pub fn get_mut(&mut self, id: ValueId) -> ValueBorrowMut<'_> {
        let value = &mut self.values[id as usize];
        let structure = &mut self.structure[value.structure_id as usize];
        ValueBorrowMut {
            kind: &mut structure.kind,
            layout: &mut structure.layout,
            value_sets: &mut value.value.value_sets,
            is_base_value: &mut value.value.is_base_value,
        }
    }

    /// Returns the value id that will returned by the next call to `add`
    fn next_value_id(&self) -> ValueId {
        self.values.len() as u32
    }

    fn get_disjoint_mut(&mut self, a: ValueId, b: ValueId) -> Option<(ValueBorrowMut<'_>, ValueBorrowMut<'_>)> {
        let (a, b) = slice_get_two_mut(&mut self.values, a as usize, b as usize)?;

        let (structure_a, structure_b) = slice_get_two_mut(&mut self.structure, a.structure_id as usize, b.structure_id as usize)?;

        Some((
            ValueBorrowMut {
                kind: &mut structure_a.kind,
                layout: &mut structure_a.layout,
                value_sets: &mut a.value.value_sets,
                is_base_value: &mut a.value.is_base_value,
            },
            ValueBorrowMut {
                kind: &mut structure_b.kind,
                layout: &mut structure_b.layout,
                value_sets: &mut b.value.value_sets,
                is_base_value: &mut b.value.is_base_value,
            },
        ))
    }
}

fn slice_get_two_mut<T>(slice: &mut [T], a: usize, b: usize) -> Option<(&mut T, &mut T)> {
    if a == b { return None; }
    assert!(a < slice.len());
    assert!(b < slice.len());

    // Safety: We know they are different fields, so this is fine.
    unsafe {
        let ptr = slice.as_mut_ptr();
        Some((&mut *ptr.add(a), &mut *ptr.add(b)))
    }
}

fn get_loc_of_value(poly_args: &[crate::typer::PolyParam], ast: &crate::parser::Ast, locals: &crate::locals::LocalVariables, value: ValueId) -> Option<Location> {
    let mapper = IdMapper {
        poly_args: poly_args.len(),
        ast_nodes: ast.nodes.len(),
        locals: locals.num_locals(),
        labels: locals.num_labels(),
    };

    match mapper.map(value) {
        MappedId::PolyArg(id) => Some(poly_args[id].loc),
        MappedId::AstNode(id) => Some(ast.get(id).loc),
        MappedId::Local(id) => Some(locals.get(id).loc),
        MappedId::Label(id) => Some(locals.get_label(id).loc),
        MappedId::None => None,
    }
}

#[derive(Clone)]
pub struct TypeSystem {
    pub values: Values,

    pub value_sets: ValueSets,

    constraints: Vec<Constraint>,
    computable_value_sizes: Vec<ValueId>,

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
            constraints: Vec::new(),
            computable_value_sizes: Vec::new(),
            available_constraints: HashMap::new(),
            queued_constraints: Vec::new(),
            errors: Vec::new(),
        };

        this.add_type(TypeKind::IntSize, Args([]), ());
        this.add_type(TypeKind::Bool, Args([]), ());

        for i in [0, 1, 2, 4, 8_u8] {
            let buffer = program.insert_buffer(u8_type, &i);
            this.add_value(static_values::INT_SIZE, buffer, ());
        }

        for i in [1, 0_u8] {
            let buffer = program.insert_buffer(bool_type, &i);
            this.add_value(static_values::BOOL, buffer, ());
        }

        this.add_type(TypeKind::Empty, Args([]), ());
        this.add_int(IntTypeKind::Usize, ());

        this
    }

    // @TODO: We should deal with recursive types later on.
    fn map_value_from_other_typesystem_to_this(
        &mut self,
        other: &TypeSystem,
        other_id: ValueId,
        already_converted: &mut Vec<(u32, ValueId)>,
        set: ValueSetId,
    ) -> ValueId {
        // Static values are the same in both sets
        if other_id < static_values::STATIC_VALUES_SIZE {
            return other_id;
        }

        // Check if we've already converted the value
        let value_structure_id = other.values.structure_id_of_value(other_id);
        for &(from_structure_id, converted_value) in already_converted.iter() {
            if from_structure_id == value_structure_id {
                // @TODO: This does not deal with variance at all
                return converted_value;
            }
        }

        // We're going to need a new value
        let value_id = self.add_unknown_type_with_set(set);
        already_converted.push((value_structure_id, value_id));

        let other_value = other.values.get(other_id);
        match other_value.kind {
            Some(Type { kind, args: Some(ref args) }) => {
                let new_args = args.iter()
                    .map(|&v| (
                        self.map_value_from_other_typesystem_to_this(other, v, already_converted, set),
                        Reason::temp_zero(),
                    ))
                    .collect::<Vec<_>>();
                self.set_type(value_id, kind.clone(), Args(new_args), set);
            }
            Some(Type { kind, args: None }) => {
                self.set_type(value_id, kind.clone(), (), set);
            }
            None => {},
        }

        value_id
    }

    pub fn add_subtree_from_other_typesystem(
        &mut self,
        other: &TypeSystem,
        // The first one is the id of the this typesystem, the second one is the id in the other
        to_convert: impl IntoIterator<Item = (ValueId, ValueId, Reason)>,
        set: ValueSetId,
    ) {
        let mut already_converted = Vec::new();
        for (this_id, other_id, reason) in to_convert {
            let new_id = self.map_value_from_other_typesystem_to_this(other, other_id, &mut already_converted, set);
            // @TODO: Deal with variance
            self.set_equal(new_id, this_id, Variance::Invariant, reason);
        }
    }

    pub fn set_waiting_on_value_set(&mut self, value_set_id: ValueSetId, waiting_on: crate::typer::WaitingOnTypeInferrence) {
        let value_set = self.value_sets.get_mut(value_set_id);
        debug_assert!(matches!(value_set.waiting_on_completion, crate::typer::WaitingOnTypeInferrence::None), "Cannot use set_on_waiting_on_value_set to override a previous waiter");
        value_set.waiting_on_completion = waiting_on;
    }

    pub fn get(&self, id: ValueId) -> ValueBorrow<'_> {
        self.values.get(id)
    }

    /// Only to be used when generating incompleteness-errors
    pub fn flag_all_values_as_complete(&mut self) {
        for value in self.values.iter_mut() {
            value.value_sets.complete(&mut self.value_sets);
        }
    }

    pub fn output_incompleteness_errors(&self, errors: &mut ErrorCtx, poly_args: &[crate::typer::PolyParam], ast: &crate::parser::Ast, locals: &crate::locals::LocalVariables) {
        for node_id in 0..self.values.values.len() as ValueId {
            if !self.values.get(node_id).value_sets.is_complete() {
                // Generate an error
                if let Some(loc) = get_loc_of_value(poly_args, ast, locals, node_id) {
                    errors.error(loc, format!("Ambiguous type"));
                } else {
                    errors.global_error(format!("Ambiguous type"));
                }
            }
        }
    }

    pub fn output_errors(&self, errors: &mut ErrorCtx, poly_args: &[crate::typer::PolyParam], ast: &crate::parser::Ast, locals: &crate::locals::LocalVariables) -> bool {
        let mut has_errors = false;
        if self.value_sets.iter().any(|v| v.has_errors) {
            has_errors = true;
        }

        for error in &self.errors {
            has_errors = true;

            match *error {
                Error { a, b: _, kind: ErrorKind::NonexistantName(name) } => {
                    if let Some(loc) = get_loc_of_value(poly_args, ast, locals, a) {
                        errors.info(loc, format!("Here"));
                    }
                    errors.global_error(format!("Field '{}' doesn't exist on type {}", name, self.value_to_str(a, 0)));
                }
                Error { a, b, kind: ErrorKind::IncompatibleTypes(creator) } => {
                    let mut a_id = a;
                    let mut b_id = b;
                    let mut creator = Some(creator);
                    while let Some(c) = creator {
                        if let ConstraintKind::Equal { creator: c, values: [a, b], .. } = self.constraints[c].kind {
                            creator = c;
                            a_id = a;
                            b_id = b;
                        } else {
                            break;
                        }
                    }

                    // @TODO: This is not a very good way to print errors, but it's fine for nowj
                    let mapper = IdMapper {
                        poly_args: poly_args.len(),
                        ast_nodes: ast.nodes.len(),
                        locals: locals.num_locals(),
                        labels: locals.num_labels(),
                    };

                    for chain in explain::get_reasons_with_look_inside(a_id, a_id, self, &mapper, ast) {
                        chain.output(errors, ast, self);
                    }

                    for chain in explain::get_reasons_with_look_inside(a_id, b_id, self, &mapper, ast) {
                        chain.output(errors, ast, self);
                    }

                    errors.global_error(format!("Incompatible types, `{}` and `{}`", self.value_to_str(a_id, 0), self.value_to_str(b_id, 0)));
                },
                _ => errors.global_error(format!("Temporary type-inference error: {:?}", error)),
            }
        }

        has_errors
    }

    pub fn value_layout(&self, value_id: ValueId) -> Layout {
        let layout = *self.values.get(value_id).layout;
        debug_assert_ne!(layout.align, 0, "Tried to read an incomplete layout");
        layout
    }

    // @Completeness: This should also support converting type values into constants.
    pub fn extract_constant(&self, program: &Program, value_id: ValueId) -> (types::Type, ConstantRef) {
        match &get_value(&self.values, value_id).kind {
            Some(Type { kind: TypeKind::Constant, args: Some(type_args) }) => {
                let &[type_, constant_ref] = &**type_args else { panic!() };
                let &Some(Type { kind: TypeKind::ConstantValue(constant_ref), .. }) = get_value(&self.values, constant_ref).kind else { panic!() };

                let type_ = self.value_to_compiler_type(type_);

                (type_, constant_ref)
            }
            Some(_) => {
                let type_id = self.value_to_compiler_type(value_id);
                let type_ = types::Type::new(types::TypeKind::Type);
                let constant_ref = program.insert_buffer(type_, &type_id as *const _ as *const u8);
                (type_, constant_ref)
            }
            _ => unreachable!("Should not have called extract_constant on an incomplete value"),
        }
    }

    pub fn value_to_compiler_type(&self, value_id: ValueId) -> types::Type {
        let Some(Type { kind: type_kind, args: Some(type_args) }) = &get_value(&self.values, value_id).kind else {
            panic!("Cannot call value_to_compiler_type on incomplete value")
        };

        match *type_kind {
            TypeKind::Type => types::Type::new(types::TypeKind::Type),
            TypeKind::Constant | TypeKind::ConstantValue(_) => unreachable!("Constants aren't concrete types, cannot use them as node types"),
            TypeKind::IntSize => unreachable!("Int sizes are a hidden type for now, the user shouldn't be able to access them"),
            TypeKind::Int => {
                let [signed, size] = &**type_args else {
                    unreachable!("Invalid int size and sign")
                };

                let sign_value = extract_constant_from_value(&self.values, *signed).expect("Sign wasn't a value");
                let size_value = extract_constant_from_value(&self.values, *size).expect("Size wasn't a value");

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

                let length = extract_constant_from_value(&self.values, *length).expect("Array length isn't a value");

                let length = unsafe { usize::from_le_bytes(*length.as_ptr().cast::<[u8; 8]>()) };

                types::Type::new(types::TypeKind::Array(element_type, length))
            }
            TypeKind::Buffer => {
                let [pointee] = &**type_args else {
                    unreachable!("Invalid reference type")
                };

                let pointee = self.value_to_compiler_type(*pointee);

                types::Type::new(types::TypeKind::Buffer { pointee })
            }
            TypeKind::Reference => {
                let [pointee] = &**type_args else {
                    unreachable!("Invalid reference type")
                };

                let pointee = self.value_to_compiler_type(*pointee);

                types::Type::new(types::TypeKind::Reference { pointee })
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
    
    pub fn set_op_equal(&mut self, op: BinaryOp, a: ValueId, b: ValueId, result: ValueId, reason: Reason) {
        insert_active_constraint(
            &mut self.constraints,
            &mut self.available_constraints,
            &mut self.queued_constraints,
            Constraint {
                kind: ConstraintKind::BinaryOp {
                    values: [a, b, result],
                    op,
                },
                reason,
                applied: false,
            },
        );
    }

    pub fn set_cast(&mut self, to: ValueId, from: ValueId, reason: Reason) {
        insert_active_constraint(
            &mut self.constraints,
            &mut self.available_constraints,
            &mut self.queued_constraints,
            Constraint {
                kind: ConstraintKind::Relation { kind: Relation::Cast, values: [to, from] },
                applied: false,
                reason,
            }
        );
    }

    pub fn set_equal(&mut self, a: ValueId, b: ValueId, variance: Variance, reason: Reason) {
        if a == b {
            return;
        }
        insert_active_constraint(
            &mut self.constraints,
            &mut self.available_constraints,
            &mut self.queued_constraints,
            Constraint::equal(a, b, variance, None, reason),
        );
    }

    pub fn set_field_name_equal(
        &mut self,
        a: ValueId,
        field_name: Ustr,
        b: ValueId,
        variance: Variance,
        reason: Reason,
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
                    hidden_subdivisions: 0,
                },
                reason,
                applied: false,
            },
        );
    }

    pub fn solve(&mut self) {
        // @Performance: I think this might be more performant than not sorting, but not 100% sure.
        // self.queued_constraints.sort_unstable_by_key(|v| matches!(&self.constraints[*v], ConstraintKind::Equal { variance: Variance::Invariant, .. }));

        if DEBUG {
            self.print_state();
        }

        while let Some(available_id) = self.queued_constraints.pop() {
            if DEBUG {
                println!("Applied constraint: {}", self.constraint_to_string(&self.constraints[available_id]));
            }

            self.apply_constraint(available_id);

            if DEBUG {
                self.print_state();
            }
        }

        if DEBUG {
            self.print_state();
        }

        while let Some(computable_size) = self.computable_value_sizes.pop() {
            self.values.compute_size(&mut self.computable_value_sizes, computable_size, &mut self.value_sets);
        }

        // self.print_state();

        // let count = self.values.structure.iter().filter(|v| v.num_values > 0).count();
        // let length = self.values.structure.len();
        // println!("Conversion ratio: {}, {}, {:.4}", count, length, count as f64 / length as f64);
    }

    fn constant_to_str(&self, type_: ValueId, value: ConstantRef, rec: usize) -> String {
        match &get_value(&self.values, type_).kind {
            Some(Type { kind: TypeKind::Type, .. }) => {
                let compiler_type = unsafe { *value.as_ptr().cast::<types::Type>() };
                format!("{}", compiler_type)
            }
            Some(Type { kind: TypeKind::IntSize, .. }) => {
                let byte;
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
            Some(Type { kind: TypeKind::Int, args: Some(c) }) => {
                let [signed, size] = &**c else { panic!() };

                let Some(signed) = extract_constant_from_value(&self.values, *signed) else {
                    return "(?)".to_string()
                };

                let Some(size) = extract_constant_from_value(&self.values, *size) else {
                    return "(?)".to_string()
                };

                let signed = unsafe { *signed.as_ptr().cast::<bool>() };
                let size = unsafe { *size.as_ptr().cast::<u8>() } as usize;

                let mut big_int = [0; 16];
                unsafe {
                    std::ptr::copy_nonoverlapping(value.as_ptr(), big_int.as_mut_ptr(), size);
                }

                if signed && (big_int[size] & 0x80) > 0 {
                    big_int[size + 1..].fill(0xff);
                }

                format!("{}", i128::from_le_bytes(big_int))
            }
            Some(Type { kind: TypeKind::Bool, .. }) => {
                let byte = unsafe { *value.as_ptr() };
                match byte {
                    0 => "false".to_string(),
                    1 => "true".to_string(),
                    num => format!("<invalid bool value {}>", num),
                }
            }
            _ => {
                format!("(cannot format {})", self.value_to_str(type_, rec))
            }
        }
    }

    pub fn value_to_str(&self, value: ValueId, rec: usize) -> String {
        if rec > 7 {
            return "...".to_string();
        }
        match &self.values.get(value).kind {
            Some(Type { kind: TypeKind::Type, .. }) => "type".to_string(),
            Some(Type { kind: TypeKind::Bool, .. }) => "bool".to_string(),
            Some(Type { kind: TypeKind::Empty, .. }) => "Empty".to_string(),
            Some(Type { kind: TypeKind::IntSize, .. }) => "<size of int>".to_string(),
            Some(Type { kind: TypeKind::ConstantValue(_), .. }) => "<constant value>".to_string(),
            None => "_".to_string(),
            Some(Type { kind: TypeKind::Constant, args: Some(c) }) => match &**c {
                [type_, value] => {
                    let value = match &self.values.get(*value).kind {
                        Some(Type { kind: TypeKind::ConstantValue(constant_ref), .. }) => {
                            self.constant_to_str(*type_, *constant_ref, rec + 1)
                        }
                        _ => "_".to_string(),
                    };
                    let type_ = self.value_to_str(*type_, rec + 1);

                    format!("{} : {}", value, type_)
                }
                _ => unreachable!("A constant type node should always only have two arguments"),
            },
            Some(Type { kind, args: None, .. }) => format!("{:?}", kind),
            Some(Type { kind: TypeKind::Int, args: Some(c) }) => match &**c {
                [signed, size] => {
                    if let (Some(sign), Some(size)) = (extract_constant_from_value(&self.values, *signed), extract_constant_from_value(&self.values, *size)) {
                        let sign = unsafe { *sign.as_ptr().cast::<u8>() } > 0;
                        let size = unsafe { *size.as_ptr().cast::<u8>() };

                        match (sign, size) {
                            (true, 0) => "isize",
                            (true, 1) => "i8",
                            (true, 2) => "i16",
                            (true, 4) => "i32",
                            (true, 8) => "i64",
                            (false, 0) => "usize",
                            (false, 1) => "u8",
                            (false, 2) => "u16",
                            (false, 4) => "u32",
                            (false, 8) => "u64",
                            _ => "<int with invalid size>",
                        }.to_string()
                    } else {
                        format!(
                            "int({}, {})",
                            self.value_to_str(*signed, rec + 1),
                            self.value_to_str(*size, rec + 1),
                        )
                    }
                },
                _ => unreachable!("A function pointer type has to have at least a return type"),
            }
            Some(Type { kind: TypeKind::Function, args: Some(c) }) => match &**c {
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
            Some(Type { kind: TypeKind::Struct(names), args: Some(c), .. }) => {
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
            Some(Type { kind: TypeKind::Array, args: Some(c), .. }) => match &**c {
                [type_, length] => format!(
                    "[{}] {}",
                    self.value_to_str(*length, rec + 1),
                    self.value_to_str(*type_, rec + 1),
                ),
                _ => unreachable!("Arrays should only ever have two type parameters"),
            },
            Some(Type { kind: TypeKind::Buffer, args: Some(c), .. }) => match &**c {
                [type_] => format!(
                    "[] {}",
                    self.value_to_str(*type_, rec + 1)
                ),
                _ => unreachable!("Buffers should only ever have two type parameters"),
            },
            Some(Type { kind: TypeKind::Reference, args: Some(c), .. }) => match &**c {
                [type_] => format!(
                    "&{}",
                    self.value_to_str(*type_, rec + 1)
                ),
                _ => unreachable!("References should only ever have two type parameters"),
            },
        }
    }

    fn constraint_to_string(&self, constraint: &Constraint) -> String {
        match constraint.kind {
            ConstraintKind::Relation { kind, values: [a, b] } => {
                format!("{} == {:?} {}", self.value_to_str(a, 0), kind, self.value_to_str(b, 0))
            }
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
                creator: _,
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
                hidden_subdivisions: _,
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
            let value = self.values.get(i as u32);
            println!("{}, size: {}, align: {}: {}, {}", i, value.layout.size, value.layout.align, v.value_sets.is_complete(), self.value_to_str(i as u32, 0));
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
        if constraint.applied { return; }

        match constraint.kind {
            ConstraintKind::Relation { kind, values: [to_id, from_id] } => {
                let to = get_value(&self.values, to_id);
                let from = get_value(&self.values, from_id);

                match (kind, to.kind, from.kind) {
                    (
                        Relation::Cast,
                        Some(Type { kind: TypeKind::Buffer, args: Some(_) }),
                        Some(Type { kind: TypeKind::Reference, args: Some(from_args), .. }),
                    ) => {
                        let new_from = from_args[0];
                        insert_active_constraint(
                            &mut self.constraints,
                            &mut self.available_constraints,
                            &mut self.queued_constraints,
                            Constraint {
                                kind: ConstraintKind::Relation { kind: Relation::BufferEqualsArray, values: [to_id, new_from] },
                                applied: false,
                                reason: constraint.reason,
                            }
                        );
                    }
                    (
                        Relation::Cast,
                        Some(Type { kind: TypeKind::Int, args: _ }),
                        Some(Type { kind: TypeKind::Int, args: _ }),
                    ) => {}
                    (
                        Relation::Cast,
                        Some(Type { kind: TypeKind::Int, args: _ }),
                        None,
                    ) => {
                        let int_t = self.add_type(TypeKind::Int, (), ());
                        self.set_equal(from_id, int_t, Variance::Invariant, constraint.reason);
                    }
                    (
                        Relation::Cast,
                        None,
                        Some(Type { kind: TypeKind::Int, args: _ }),
                    ) => {
                        let int_t = self.add_type(TypeKind::Int, (), ());
                        self.set_equal(to_id, int_t, Variance::Invariant, constraint.reason);
                    }
                    (
                        Relation::Cast,
                        // @TODO: We could remove the `Some` here
                        Some(Type { kind: TypeKind::Reference, args: Some(_) }),
                        Some(Type { kind: TypeKind::Reference, args: Some(_), .. }),
                    ) => {
                        // Two references just cast to each other, no matter the type
                    }
                    (
                        Relation::BufferEqualsArray,
                        Some(Type { kind: TypeKind::Buffer, args: Some(to_args) }),
                        Some(Type { kind: TypeKind::Array, args: Some(from_args), .. }),
                    ) => {
                        let a = to_args[0];
                        let b = from_args[0];
                        self.set_equal(a, b, Variance::Invariant, constraint.reason);
                    }
                    (
                        _,
                        Some(Type { kind: to, args: Some(_), .. }),
                        Some(Type { kind: from, args: Some(_), .. }),
                    ) => unimplemented!("Temporary error: Cannot use relation {:?} from {:?} to {:?}", kind, from, to),
                    _ => return,
                }

                self.constraints[constraint_id].applied = true;
            }
            ConstraintKind::BinaryOp {
                values: [a_id, b_id, result_id],
                op,
            } => {
                let a = get_value(&self.values, a_id);
                let b = get_value(&self.values, b_id);
                let result = get_value(&self.values, result_id);

                let (a, b, result) = (&a.kind, &b.kind, &result.kind);

                match (op, (a.as_ref().map(|v| &v.kind), b.as_ref().map(|v| &v.kind), result.as_ref().map(|v| &v.kind))) {
                    (
                        BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mult | BinaryOp::Div | BinaryOp::BitAnd | BinaryOp::BitOr | BinaryOp::ShiftLeft | BinaryOp::ShiftRight | BinaryOp::Modulo,
                        (Some(TypeKind::Int), Some(TypeKind::Int), _),
                    ) => {
                        self.set_equal(a_id, b_id, Variance::Invariant, constraint.reason);
                        self.set_equal(a_id, result_id, Variance::Invariant, constraint.reason);
                    }
                    (
                        BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mult | BinaryOp::Div | BinaryOp::BitAnd | BinaryOp::BitOr,
                        (Some(TypeKind::Reference), Some(TypeKind::Int), Some(TypeKind::Reference)),
                    ) => {
                        // No reason given for why the type is a usize....
                        let usize = self.add_int(IntTypeKind::Usize, ());
                        self.set_equal(usize, b_id, Variance::Invariant, constraint.reason);
                        self.set_equal(a_id, result_id, Variance::Invariant, constraint.reason);
                    }
                    (
                        BinaryOp::And | BinaryOp::Or,
                        (_, _, _),
                    ) => {
                        // Temporary: No type validation, just equality :)
                        let bool = self.add_type(TypeKind::Bool, Args([]), ());
                        self.set_equal(bool, a_id, Variance::Invariant, constraint.reason);
                        self.set_equal(bool, b_id, Variance::Invariant, constraint.reason);
                        self.set_equal(bool, result_id, Variance::Invariant, constraint.reason);
                    }
                    (
                        BinaryOp::Equals | BinaryOp::NotEquals | BinaryOp::LargerThanEquals | BinaryOp::LargerThan | BinaryOp::LessThanEquals | BinaryOp::LessThan,
                        (Some(TypeKind::Int), Some(TypeKind::Int), _) | (Some(TypeKind::Reference), Some(TypeKind::Reference), _) | (Some(TypeKind::Bool), Some(TypeKind::Bool), _)
                    ) => {
                        let id = self.add_type(TypeKind::Bool, Args([]), ());

                        self.set_equal(result_id, id, Variance::Invariant, constraint.reason);
                        self.set_equal(a_id, b_id, Variance::DontCare, constraint.reason);
                    }
                    (
                        BinaryOp::Equals | BinaryOp::NotEquals,
                        (Some(TypeKind::Type), Some(TypeKind::Type), _),
                    ) => {
                        let id = self.add_type(TypeKind::Bool, Args([]), ());

                        self.set_equal(result_id, id, Variance::Invariant, constraint.reason);
                        self.set_equal(a_id, b_id, Variance::DontCare, constraint.reason);
                    }
                    (
                        _,
                        (Some(a), Some(b), Some(c)),
                    ) => unimplemented!("Operator {:?} with operands {:?}, {:?}, and returning {:?}, not supported in type inferrence yet", op, a, b, c),
                    _ => return,
                }

                self.constraints[constraint_id].applied = true;
            }
            ConstraintKind::EqualNamedField {
                values: [a_id, b_id],
                index: field_name,
                variance,
                hidden_subdivisions,
            } => {
                let a = get_value(&self.values, a_id);

                match &a.kind {
                    None => return,
                    Some(Type { kind: TypeKind::Reference, args, .. }) if hidden_subdivisions < 1 => {
                        if let Some(args) = args {
                            let inner = args[0];
                            let reason = constraint.reason;
                            insert_active_constraint(
                                &mut self.constraints,
                                &mut self.available_constraints,
                                &mut self.queued_constraints,
                                Constraint {
                                    kind: ConstraintKind::EqualNamedField {
                                        values: [inner, b_id],
                                        index: field_name,
                                        variance,
                                        hidden_subdivisions: hidden_subdivisions + 1,
                                    },
                                    reason,
                                    applied: false,
                                },
                            );
                            self.constraints[constraint_id].applied = true;
                        }
                    }
                    Some(Type { kind: TypeKind::Buffer, args, .. }) => {
                        match &*field_name {
                            "ptr" => {
                                if let Some(args) = args {
                                    let &[pointee] = &args[..] else {
                                        unreachable!("All buffer types should have two arguments")
                                    };

                                    // @Correctness: We want to reintroduce variances here after the rework
                                    let new_value_id = self.values.add(
                                        Some(Type {
                                            kind: TypeKind::Reference,
                                            args: Some(Box::new([pointee])),
                                        }),
                                        &mut self.value_sets,
                                        ValueSetHandles::empty(),
                                    );

                                    self.set_equal(new_value_id, b_id, variance, constraint.reason);
                                }
                            }
                            "len" => {
                                self.set_equal(static_values::USIZE, b_id, variance, constraint.reason);

                                self.constraints[constraint_id].applied = true;
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
                    Some(Type { kind: TypeKind::Struct(names), .. }) => {
                        if let Some(pos) = names.iter().position(|&v| v == field_name) {
                            let reason = constraint.reason;
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
                                    reason,
                                    applied: false,
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
                    Some(Type { kind: TypeKind::Array, .. }) => {
                        // @Correctness: We should have a check that the argument is in range
                        if let Some(_) = field_name.strip_prefix("_").and_then(|v| v.parse::<usize>().ok()) {
                            let reason = constraint.reason;
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
                                    reason,
                                    applied: false,
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
                    Some(_) => {
                        self.errors.push(Error::new(
                            a_id,
                            b_id,
                            ErrorKind::NonexistantName(field_name),
                        ));
                        return;
                    }
                }

                self.constraints[constraint_id].applied |= true;
            }
            ConstraintKind::EqualsField {
                values: [a_id, b_id],
                index: field_index,
                variance,
            } => {
                let a = &get_value(&self.values, a_id).kind;

                match a {
                    None | Some(Type { args: None, .. }) => {}
                    Some(Type { args: Some(fields), .. }) => {
                        if let Some(&field) = fields.get(field_index) {
                            let loc = constraint.reason.loc;
                            insert_active_constraint(
                                &mut self.constraints,
                                &mut self.available_constraints,
                                &mut self.queued_constraints,
                                Constraint::equal(field, b_id, variance, Some(constraint_id), Reason::new(loc, ReasonKind::Ignore)),
                            );
                        } else {
                            self.errors.push(Error::new(
                                a_id,
                                b_id,
                                ErrorKind::IndexOutOfBounds(field_index),
                            ));
                            return;
                        }

                        self.constraints[constraint_id].applied |= true;
                    }
                }
            }
            ConstraintKind::Equal {
                values: [a_id, b_id],
                variance: _,
                creator: _,
            } => {
                let Some((a_value, b_value)) = self.values.get_disjoint_mut(a_id, b_id) else {
                    return;
                };

                let a = &mut *a_value.kind;
                let b = &mut *b_value.kind;
                let (to, from) = match (a, b) {
                    (None, None) => (a_id, b_id),
                    (None, Some(_)) => (b_id, a_id),
                    (Some(_), None) => (a_id, b_id),
                    (Some(a_type), Some(b_type)) => {
                        if a_type.kind != b_type.kind {
                            self.errors.push(Error { a: a_id, b: b_id, kind: ErrorKind::IncompatibleTypes(constraint_id) });
                            self.constraints[constraint_id].applied = true;
                            return;
                        } else {
                            match (&a_type.args, &b_type.args) {
                                (None, None) => (a_id, b_id),
                                (None, Some(_)) => (b_id, a_id),
                                (Some(_), None) => (a_id, b_id),
                                (Some(a_args), Some(b_args)) => {
                                    if a_args.len() != b_args.len() {
                                        self.errors.push(Error { a: a_id, b: b_id, kind: ErrorKind::IncompatibleTypes(constraint_id) });
                                        self.constraints[constraint_id].applied = true;
                                        return;
                                    } else {
                                        for (a_arg, b_arg) in a_args.iter().zip(b_args.iter()) {
                                            let loc = self.constraints[constraint_id].reason.loc;
                                            insert_active_constraint(
                                                &mut self.constraints,
                                                &mut self.available_constraints,
                                                &mut self.queued_constraints,
                                                Constraint::equal(*a_arg, *b_arg, Variance::Variant, Some(constraint_id), Reason::new(loc, ReasonKind::Ignore)),
                                            );
                                        }
                                    }

                                    if self.values.get(b_id).layout.align > 0 {
                                        (b_id, a_id)
                                    } else {
                                        (a_id, b_id)
                                    }
                                }
                            }
                        }
                    }
                };

                // Actually, progress was made on the whole from set
                for id in self.values.iter_values_in_structure(from) {
                    self.queued_constraints.extend(
                        self.available_constraints
                            .get(&id)
                            .iter()
                            .flat_map(|v| v.iter())
                            .copied()
                            .filter(|v| v != &constraint_id),
                    );
                }

                self.values.structurally_combine(&mut self.computable_value_sizes, &mut self.value_sets, to, from);
            }
        }
    }

    pub fn params(&self, value: ValueId) -> Option<&[ValueId]> {
        match get_value(&self.values, value).kind {
            Some(Type { ref args, .. }) => args.as_deref(),
            _ => None,
        }
    }

    /// Adds a value set to a value. This value has to be an unknown type, otherwise it will panic
    /// in debug mode. It also cannot be an alias. This is solely intended for use by the building
    /// process of the typer.
    pub fn set_value_set(&mut self, value_id: ValueId, value_set_id: ValueSetId) {
        let value = self.values.get_mut(value_id);

        // There can be no children, this function shouldn't have to recurse.
        debug_assert!(matches!(value.kind, None));

        // We don't want to worry about sorting or binary searching
        value.value_sets.set_to(self.value_sets.with_one(value_set_id));
    }

    pub fn add_unknown_type_with_set(&mut self, set: ValueSetId) -> ValueId {
        let value_set_handles = self.value_sets.with_one(set);
        self.values.add(
            None,
            &mut self.value_sets,
            value_set_handles,
        )
    }

    pub fn set_compiler_type(&mut self, program: &Program, id: ValueId, type_: types::Type, set: impl IntoValueSet + Clone) -> ValueId {
        match *type_.kind() {
            types::TypeKind::Function { ref args, returns } => {
                let mut new_args = Vec::with_capacity(args.len() + 1);

                // @TODO: We should append the sub-expression used to the reason as well.
                new_args.push((self.add_compiler_type(program, returns, set.clone()), Reason::temp_zero()));

                for &arg in args {
                    new_args.push((self.add_compiler_type(program, arg, set.clone()), Reason::temp_zero()));
                }

                self.set_type(id, TypeKind::Function, Args(new_args), set.clone())
            }
            types::TypeKind::Type => {
                self.set_type(id, TypeKind::Type, Args([]), set.clone())
            }
            types::TypeKind::Int(int_type_kind) => {
                self.set_int(id, int_type_kind, set.clone());
                id
            }
            types::TypeKind::Empty => self.set_type(id, TypeKind::Empty, Args([]), set.clone()),
            types::TypeKind::Bool  => self.set_type(id, TypeKind::Bool, Args([]), set.clone()),
            types::TypeKind::Buffer { pointee } => {
                // @Cleanup: This is ugly!
                // @Correctness: We want to reintroduce these once the rework is complete
                // let permits = self.add_access(Some(Access::disallows(!permits.read(), !permits.write())), set);
                let pointee = self.add_compiler_type(program, pointee, set.clone());

                self.set_type(id, TypeKind::Buffer, Args([(pointee, Reason::temp_zero())]), set.clone())
            }
            types::TypeKind::Reference { pointee } => {
                // @Correctness: We want to reintroduce permits once the rework is complete
                // let permits = self.add_access(Some(Access::disallows(!permits.read(), !permits.write())), set);
                let pointee = self.add_compiler_type(program, pointee, set.clone());

                self.set_type(id, TypeKind::Reference, Args([(pointee, Reason::temp_zero())]), set.clone())
            }
            types::TypeKind::Array(type_, length) => {
                let inner = self.add_compiler_type(program, type_, set.clone());
                let usize_type = static_values::USIZE;
                let constant_ref_length = program.insert_buffer(
                    types::Type::new(types::TypeKind::Int(IntTypeKind::Usize)),
                    &length as *const _ as *const u8,
                );
                let length_value = self.add_value(usize_type, constant_ref_length, set.clone());
                self.set_type(id, TypeKind::Array, Args([(inner, Reason::temp_zero()), (length_value, Reason::temp_zero())]), set.clone())
            }
            types::TypeKind::Struct(ref fields) => {
                let field_names = fields.iter().map(|&(v, _)| v).collect();
                let field_types: Vec<_> = fields
                    .iter()
                    // @TODO: We should append the sub-expression used to the reason as well.
                    .map(|&(_, v)| (self.add_compiler_type(program, v, set.clone()), Reason::temp_zero()))
                    .collect();
                self.set_type(id, TypeKind::Struct(field_names), Args(field_types), set.clone())
            }
            _ => todo!("This compiler type is not done yet"),
        }
    }

    pub fn add_compiler_type(&mut self, program: &Program, type_: types::Type, set: impl IntoValueSet + Clone) -> ValueId {
        let id = self.add_unknown_type();
        self.set_compiler_type(program, id, type_, set)
    }

    #[track_caller]
    pub fn set_type(&mut self, value_id: ValueId, kind: TypeKind, args: impl IntoValueArgs, set: impl IntoValueSet) -> ValueId {
        let args = args
            .into_value_args()
            .map(|v|
                v.into_iter().enumerate().map(|(index, (v, reason))| {
                    insert_constraint(
                        &mut self.constraints,
                        &mut self.available_constraints,
                        Constraint {
                            kind: ConstraintKind::EqualsField { values: [value_id, v], index, variance: Variance::Invariant },
                            reason,
                            // It's not actually applied, but because we already have it as an argument, it never needs to be applied.
                            applied: true,
                        },
                    );
                    v
                })
                .collect()
            );
        let value_sets = set.add_set(&mut self.value_sets);
        self.values.set(value_id, Type { kind, args }, &mut self.value_sets, value_sets);
        *self.values.get_mut(value_id).is_base_value = true;

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

        self.set_type(value_id, TypeKind::Int, Args([(signed, Reason::temp_zero()), (size, Reason::temp_zero())]), set);
    }

    pub fn add_type(&mut self, kind: TypeKind, args: impl IntoValueArgs, set: impl IntoValueSet) -> ValueId {
        let value_id = self.add_unknown_type();
        self.set_type(value_id, kind, args, set);
        value_id
    }

    pub fn add_unknown_type(&mut self) -> ValueId {
        self.values.add(
            None,
            &mut self.value_sets,
            ValueSetHandles::empty(),
        )
    }

    pub fn set_value(&mut self, value_id: ValueId, type_: ValueId, value: impl IntoConstant, set: impl IntoValueSet) {
        let value = value.into_constant();
        let value_sets = set.add_set(&mut self.value_sets);
        let constant_value_id = self.values.add(
            value.map(|v| Type {
                kind: TypeKind::ConstantValue(v),
                args: Some(Box::new([])),
            }),
            &mut self.value_sets,
            value_sets,
        );
        *self.values.get_mut(constant_value_id).is_base_value = true;
        self.set_type(value_id, TypeKind::Constant, Args([(type_, Reason::temp_zero()), (constant_value_id, Reason::temp_zero())]), set);
    }

    pub fn add_value(&mut self, type_: ValueId, value: impl IntoConstant, set: impl IntoValueSet) -> ValueId {
        let type_id = self.add_unknown_type();
        self.set_value(type_id, type_, value, set);
        type_id
    }
}
