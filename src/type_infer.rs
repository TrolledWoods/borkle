use crate::types::{self, IntTypeKind};
use crate::errors::ErrorCtx;
use crate::location::Location;
use std::collections::HashMap;
use std::iter::repeat_with;
use std::hint::unreachable_unchecked;
use std::mem;
use std::sync::Arc;
use ustr::Ustr;

#[derive(Clone, Copy)]
pub struct CompilerType(pub types::Type);

#[derive(Clone, Copy)]
pub struct Empty;
#[derive(Clone, Copy)]
pub struct Var(pub usize);
#[derive(Clone, Copy)]
pub struct Unknown;
#[derive(Clone, Copy)]
pub struct Int(pub IntTypeKind);
#[derive(Clone, Copy)]
pub struct Array<T: IntoType, V: IntoValue>(pub T, pub V);
#[derive(Clone, Copy)]
pub struct Ref<V: IntoAccess, T: IntoType>(pub V, pub T);
#[derive(Clone, Copy)]
pub struct WithType<T: IntoType>(pub T);

pub trait IntoType {
    fn into_type(self, system: &mut TypeSystem, set: ValueSetId, reason: Reason) -> ValueId;
}

impl IntoType for CompilerType {
    fn into_type(self, system: &mut TypeSystem, set: ValueSetId, reason: Reason) -> ValueId {
        match self.0 .0.kind {
            types::TypeKind::Int(int_type_kind) => Int(int_type_kind).into_type(system, set, reason),
            types::TypeKind::Empty => {
                system.add(ValueKind::Type(Some((TypeKind::Empty, Some(Box::new([]))))), set, reason)
            }
            types::TypeKind::Bool => {
                system.add(ValueKind::Type(Some((TypeKind::Bool, Some(Box::new([]))))), set, reason)
            }
            types::TypeKind::Reference { pointee, permits } => Ref(
                Access::new(permits.read(), permits.write()),
                CompilerType(pointee),
            )
            .into_type(system, set, reason),
            types::TypeKind::Array(type_, length) => {
                Array(CompilerType(type_), length).into_type(system, set, reason)
            }
            types::TypeKind::Struct(ref fields) => {
                let field_names = fields.iter().map(|v| v.0).collect();
                let field_types = fields
                    .iter()
                    // @TODO: We should append the sub-expression used to the reason as well.
                    .map(|v| CompilerType(v.1).into_type(system, set, reason.clone()))
                    .collect();
                let value =
                    ValueKind::Type(Some((TypeKind::Struct(field_names), Some(field_types))));
                system.add(value, set, reason)
            }
            _ => todo!("This compiler type is not done yet"),
        }
    }
}

impl<T: IntoType, V: IntoValue> IntoType for Array<T, V> {
    fn into_type(self, system: &mut TypeSystem, set: ValueSetId, reason: Reason) -> ValueId {
        let inner_type = self.0.into_type(system, set, reason.clone());
        let inner_value = self.1.into_value(system, set, reason.clone());
        system.add(ValueKind::Type(Some((
            TypeKind::Array,
            Some(Box::new([inner_type, inner_value])),
        ))), set, reason)
    }
}

impl IntoType for Var {
    fn into_type(self, _: &mut TypeSystem, set: ValueSetId, reason: Reason) -> ValueId {
        self.0
    }
}

impl IntoType for Empty {
    fn into_type(self, system: &mut TypeSystem, set: ValueSetId, reason: Reason) -> ValueId {
        system.add(ValueKind::Type(Some((TypeKind::Empty, Some(Box::new([]))))), set, reason)
    }
}

impl IntoType for Int {
    fn into_type(self, system: &mut TypeSystem, set: ValueSetId, reason: Reason) -> ValueId {
        system.add(ValueKind::Type(Some((
            TypeKind::Int(self.0),
            Some(Box::new([])),
        ))), set, reason)
    }
}

impl IntoType for Unknown {
    fn into_type(self, system: &mut TypeSystem, set: ValueSetId, reason: Reason) -> ValueId {
        system.add_without_reason(ValueKind::Type(None), set)
    }
}

impl<T: IntoAccess, V: IntoType> IntoType for Ref<T, V> {
    fn into_type(self, system: &mut TypeSystem, set: ValueSetId, reason: Reason) -> ValueId {
        let inner_variance = self.0.into_variance(system, set, reason.clone());
        let inner_type = self.1.into_type(system, set, reason.clone());
        system.add(ValueKind::Type(Some((
            TypeKind::Reference,
            Some(Box::new([inner_variance, inner_type])),
        ))), set, reason)
    }
}

pub trait IntoAccess {
    fn into_variance(self, system: &mut TypeSystem, set: ValueSetId, reason: Reason) -> ValueId;
}

impl IntoAccess for Access {
    fn into_variance(self, system: &mut TypeSystem, set: ValueSetId, reason: Reason) -> ValueId {
        system.add_access(Some(self), set, reason)
    }
}

impl IntoAccess for Var {
    fn into_variance(self, _: &mut TypeSystem, _: ValueSetId, reason: Reason) -> ValueId {
        self.0
    }
}

impl IntoAccess for Unknown {
    fn into_variance(self, system: &mut TypeSystem, set: ValueSetId, reason: Reason) -> ValueId {
        system.add_access(None, set, reason)
    }
}

pub trait IntoValue {
    fn into_value(self, system: &mut TypeSystem, set: ValueSetId, reason: Reason) -> ValueId;
}

impl<T: IntoType> IntoValue for WithType<T> {
    fn into_value(self, system: &mut TypeSystem, set: ValueSetId, reason: Reason) -> ValueId {
        let type_ = self.0.into_type(system, set, reason.clone());
        system.add(ValueKind::Value(Some((type_, None))), set, reason)
    }
}

impl IntoValue for usize {
    fn into_value(self, system: &mut TypeSystem, set: ValueSetId, reason: Reason) -> ValueId {
        let int_type = system.add_type(Int(IntTypeKind::Usize), set, reason.clone());
        system.add(ValueKind::Value(Some((int_type, Some(self)))), set, reason)
    }
}

impl IntoValue for Var {
    // @Correctness: Should the set be added to the var here?
    fn into_value(self, _: &mut TypeSystem, _set: ValueSetId, reason: Reason) -> ValueId {
        self.0
    }
}

impl IntoValue for Unknown {
    fn into_value(self, system: &mut TypeSystem, set: ValueSetId, reason: Reason) -> ValueId {
        system.add(ValueKind::Value(None), set, reason)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeKind {
    // No arguments
    Int(IntTypeKind),
    Bool,
    Empty,

    // return, (arg0, arg1, arg2, ...)
    Function,
    // element: type, length: int
    Array,
    // inner element: type
    Reference,
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

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Access {
    pub read: bool,
    pub write: bool,
    pub needs_read: bool,
    pub needs_write: bool,
}

impl Default for Access {
    fn default() -> Self {
        Self {
            read: true,
            write: true,
            needs_read: false,
            needs_write: false,
        }
    }
}

impl Access {
    pub fn new(read: bool, write: bool) -> Self {
        Self {
            read: read,
            write: write,
            needs_read: read,
            needs_write: write,
        }
    }

    pub fn needs(read: bool, write: bool) -> Self {
        Self {
            read: true,
            write: true,
            needs_read: read,
            needs_write: write,
        }
    }

    pub fn is_complete(&self) -> bool {
        self.read <= self.needs_read && self.write <= self.needs_write
    }

    pub fn combine_with(&mut self, other: &mut Self, variance: Variance) {
        match variance {
            Variance::Variant => {
                other.read &= self.read;
                other.write &= self.write;
                self.needs_read |= other.needs_read;
                self.needs_write |= other.needs_write;
            }
            Variance::Covariant => {
                self.read &= other.read;
                self.write &= other.write;
                other.needs_read |= self.needs_read;
                other.needs_write |= self.needs_write;
            }
            Variance::Invariant => {
                self.read &= other.read;
                other.read = self.read;
                self.write &= other.write;
                other.write = self.write;
                self.needs_read |= other.needs_read;
                other.needs_read = self.needs_read;
                self.needs_write |= other.needs_write;
                other.needs_write = self.needs_write;
            }
            Variance::DontCare => {}
        }
    }
}

/// Combines two values into one.
/// **this does not recurse**, so beware.
fn combine_values(
    values: &mut Vec<MaybeMovedValue>,
    constraints: &mut Vec<Constraint>,
    available_constraints: &mut HashMap<ValueId, Vec<ConstraintId>>,
    from_id: ValueId,
    to_id: ValueId,
) {
}

pub enum ValueKind {
    Type(Option<(TypeKind, Option<Box<[ValueId]>>)>),

    /// For now values can only be usize, but you could theoretically have any value.
    Value(Option<(ValueId, Option<usize>)>),

    /// These are the only coerced values for now.
    Access(Option<Access>),
}

impl ValueKind {
    fn to_unknown(&self) -> Self {
        match self {
            Self::Type(_) => Self::Type(None),
            Self::Value(_) => Self::Value(None),
            Self::Access(_) => Self::Access(None),
        }
    }
}

/// This describes the reason why a value is the way it is.
/// For example, why is this a reference? Why is this a function? e.t.c.
/// This means we can give reasonable reporting when errors occur.
#[derive(Clone, PartialEq, Eq)]
pub struct Reason {
    pub loc: Location,
    pub message: Arc<String>,
}

impl Reason {
    pub fn new(loc: Location, message: impl ToString) -> Self {
        Self {
            loc,
            message: Arc::new(message.to_string()),
        }
    }
}

#[derive(Default, Clone)]
struct Reasons {
    buffer: [Option<Reason>; 4],
    /// A flag for if there were more reasons that we couldn't fit into the structure.
    omitted_reasons: bool,
}

impl Reasons {
    fn with_one(value: Reason) -> Self {
        let mut v = Self::default();
        v.insert(value);
        v
    }

    fn iter(&self) -> impl Iterator<Item = &Reason> {
        self.buffer.iter().filter_map(|v| v.as_ref())
    }

    fn insert(&mut self, value: Reason) {
        // @Robustness: We want a strict ordering so that errors are consistant, but temporarily this is fine.
        let mut none_index = None;
        for (i, v) in self.buffer.iter().enumerate() {
            match v {
                Some(v) if *v == value => return,
                Some(_) => {},
                None => {
                    none_index.get_or_insert(i);
                }
            }
        }

        if let Some(index) = none_index {
            self.buffer[index] = Some(value);
        } else {
            self.omitted_reasons = true;
        }
    }

    fn combine(&mut self, other: &mut Reasons) {
        self.take_reasons_from(other);
        other.buffer = self.buffer.clone();
    }

    fn take_reasons_from(&mut self, other: &Reasons) {
        for value in other.buffer.iter().filter_map(|v| v.clone()) {
            self.insert(value);
        }
    }
}

pub type ValueId = usize;

struct Value {
    kind: ValueKind,
    value_sets: Vec<ValueSetId>,
    reasons: Reasons,
    // /// If a value isn't known, it should generate an error, but if it's possible that it's not known because
    // /// an error occured, we don't want to generate an error, which is why this flag exists.
    // related_to_error: bool,
}

enum MaybeMovedValue {
    Value(Value),
    Moved(ValueId),
}

type ConstraintId = usize;

#[derive(Debug, Clone, Copy)]
struct Constraint {
    kind: ConstraintKind,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum ConstraintKind {
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
            ConstraintKind::Equal { values: [a, b], variance } => {
                if a == b {
                    self.kind = ConstraintKind::Dead;
                } else if a > b {
                    mem::swap(a, b);
                    *variance = variance.invert();
                }
            }
            ConstraintKind::EqualsField { .. } | ConstraintKind::EqualNamedField { .. } | ConstraintKind::Dead => {}
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
            ConstraintKind::Equal { values, .. } | ConstraintKind::EqualsField { values, .. } | ConstraintKind::EqualNamedField { values, .. } => {
                &*values
            }
            ConstraintKind::Dead => &[],
        }
    }

    fn values_mut(&mut self) -> &mut [ValueId] {
        match &mut self.kind {
            ConstraintKind::Equal { values, .. } | ConstraintKind::EqualsField { values, .. } | ConstraintKind::EqualNamedField { values, .. } => {
                &mut *values
            }
            ConstraintKind::Dead => &mut [],
        }
    }

    fn variance_mut(&mut self) -> Option<&mut Variance> {
        match &mut self.kind {
            ConstraintKind::Equal { variance, .. } | ConstraintKind::EqualsField { variance, .. } | ConstraintKind::EqualNamedField { variance, .. } => Some(variance),
            ConstraintKind::Dead => None,
        }
    }

    fn equal(a: ValueId, b: ValueId, variance: Variance) -> Self {
        let kind = if a == b {
            ConstraintKind::Dead
        } else if b > a {
            ConstraintKind::Equal { values: [a, b], variance }
        } else {
            ConstraintKind::Equal {
                values: [b, a],
                variance: variance.invert(),
            }
        };

        Self { kind }
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

fn get_real_value_id(values: &Vec<MaybeMovedValue>, mut id: ValueId) -> ValueId {
    while let MaybeMovedValue::Moved(new_id) = values[id] {
        id = new_id;
    }

    id
}

fn get_value(values: &Vec<MaybeMovedValue>, mut id: ValueId) -> &Value {
    let MaybeMovedValue::Value(v) = &values[get_real_value_id(values, id)] else {
        // Safety: Because we called `get_real_value_id` we know that it's not an alias
        unsafe { unreachable_unchecked() }
    };
    v
}

fn get_value_mut(values: &mut Vec<MaybeMovedValue>, mut id: ValueId) -> &mut Value {
    let id = get_real_value_id(values, id);
    let MaybeMovedValue::Value(v) = &mut values[id] else {
        // Safety: Because we called `get_real_value_id` we know that it's not an alias
        unsafe { unreachable_unchecked() }
    };
    v
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

            let vec = available_constraints.entry(a).or_insert_with(Vec::new);
            vec.push(id);

            let vec = available_constraints.entry(b).or_insert_with(Vec::new);
            vec.push(id);
        }
        ConstraintKind::EqualsField { values: [a, b], .. }
        | ConstraintKind::EqualNamedField { values: [a, b], .. } => {
            let vec = available_constraints.entry(a).or_insert_with(Vec::new);
            vec.push(id);

            let vec = available_constraints.entry(b).or_insert_with(Vec::new);
            vec.push(id);
        }
        ConstraintKind::Dead => {},
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

            let vec = available_constraints.entry(a).or_insert_with(Vec::new);
            vec.push(id);

            let vec = available_constraints.entry(b).or_insert_with(Vec::new);
            vec.push(id);
        }
        ConstraintKind::EqualsField { values: [a, b], .. }
        | ConstraintKind::EqualNamedField { values: [a, b], .. } => {
            let vec = available_constraints.entry(a).or_insert_with(Vec::new);
            vec.push(id);

            let vec = available_constraints.entry(b).or_insert_with(Vec::new);
            vec.push(id);
        }
        ConstraintKind::Dead => {},
    }

    queued_constraints.push(id);
}

pub type ValueSetId = usize;

pub struct ValueSet {
    pub related_nodes: Vec<crate::parser::ast::NodeId>,

    pub uncomputed_values: i32,
    pub has_errors: bool,

    pub ast_node: crate::parser::ast::NodeId,
    pub has_been_computed: bool,
}

pub struct TypeSystem {
    /// The first few values are always primitive values, with a fixed position, to make them trivial to create.
    /// 0 - Int
    values: Vec<MaybeMovedValue>,

    value_sets: Vec<ValueSet>,

    constraints: Vec<Constraint>,

    /// When the access level of certain things determine the variance of constraints, those constraints are put into here.
    variance_updates: HashMap<(ValueId, ValueId), VarianceConstraint>,

    available_constraints: HashMap<ValueId, Vec<ConstraintId>>,
    queued_constraints: Vec<ConstraintId>,

    pub errors: Vec<Error>,
}

impl TypeSystem {
    pub fn new() -> Self {
        Self {
            values: vec![],
            value_sets: Vec::new(),
            variance_updates: HashMap::new(),
            constraints: Vec::new(),
            available_constraints: HashMap::new(),
            queued_constraints: Vec::new(),
            errors: Vec::new(),
        }
    }

    pub fn output_errors(&self, errors: &mut ErrorCtx) {
        for error in &self.errors {
            match *error {
                Error { a, b, kind: ErrorKind::IncompatibleTypes } => {
                    let a_type = self.value_to_str(a, 7);
                    let b_type = self.value_to_str(b, 7);

                    let a = get_value(&self.values, a);
                    let b = get_value(&self.values, b);

                    let mut reasons = a.reasons.iter();
                    if let Some(reason) = reasons.next() {
                        errors.info(
                            reason.loc,
                            format!("'{}' because {}", a_type, reason.message),
                        );
                    }

                    for reason in reasons {
                        errors.info(
                            reason.loc,
                            format!(".. and because {}", reason.message),
                        );
                    }

                    let mut reasons = b.reasons.iter();
                    if let Some(reason) = reasons.next() {
                        errors.info(
                            reason.loc,
                            format!("'{}' because {}", b_type, reason.message),
                        );
                    }

                    for reason in reasons {
                        errors.info(
                            reason.loc,
                            format!(".. and because {}", reason.message),
                        );
                    }

                    errors.global_error(format!("Conflicting types '{}' and '{}'", a_type, b_type));
                }
                _ => errors.global_error(format!("Temporary type-inference error: {:?}", error)),
            }
        }
    }

    pub fn value_sets(&self) -> impl Iterator<Item = ValueSetId> {
        0..self.value_sets.len()
    }

    pub fn get_value_set(&self, value_set: ValueSetId) -> &ValueSet {
        &self.value_sets[value_set]
    }

    pub fn get_value_set_mut(&mut self, value_set: ValueSetId) -> &mut ValueSet {
        &mut self.value_sets[value_set]
    }

    pub fn add_node_to_set(&mut self, value_set: ValueSetId, node: crate::parser::ast::NodeId) {
        self.value_sets[value_set].related_nodes.push(node);
    }

    pub fn lock_value_set(&mut self, value_set: ValueSetId) {
        self.value_sets[value_set].uncomputed_values += 1;
    }

    pub fn unlock_value_set(&mut self, value_set: ValueSetId) {
        self.value_sets[value_set].uncomputed_values -= 1;
    }

    pub fn make_value_set_erroneous(&mut self, value_set: ValueSetId) {
        self.value_sets[value_set].has_errors = true;
    }

    pub fn add_value_set(&mut self, ast_node: crate::parser::ast::NodeId) -> ValueSetId {
        let id = self.value_sets.len();
        self.value_sets.push(ValueSet {
            uncomputed_values: 0,
            has_errors: false,
            related_nodes: Vec::new(),
            ast_node,
            has_been_computed: false,
        });
        id
    }

    pub fn value_is_in_set(&self, value_id: ValueId, set_id: ValueSetId) -> bool {
        get_value(&self.values, value_id).value_sets.binary_search(&set_id).is_ok()
    }

    pub fn value_to_compiler_type(&self, value_id: ValueId) -> types::Type {
        let ValueKind::Type(Some((type_kind, Some(type_args)))) = &get_value(&self.values, value_id).kind else {
            panic!("Cannot call value_to_compiler_type on incomplete value")
        };

        match *type_kind {
            TypeKind::Int(int_type_kind) => types::Type::new(types::TypeKind::Int(int_type_kind)),
            TypeKind::Bool => types::Type::new(types::TypeKind::Bool),
            TypeKind::Empty => types::Type::new(types::TypeKind::Empty),
            TypeKind::Function => {
                let [return_type, arg_types @ ..] = &**type_args else {
                    unreachable!("Invalid function type")
                };

                let returns = self.value_to_compiler_type(*return_type);
                let args = arg_types.iter().map(|v| self.value_to_compiler_type(*v)).collect();

                types::Type::new(types::TypeKind::Function { args, returns })
            }
            TypeKind::Array => {
                unimplemented!("Not yet, arrays")
            },
            TypeKind::Reference => {
                let [mutability, pointee] = &**type_args else {
                    unreachable!("Invalid reference type")
                };

                let ValueKind::Access(Some(access)) = &get_value(&self.values, *mutability).kind else {
                    unreachable!("Requires access")
                };

                let pointee = self.value_to_compiler_type(*pointee);
                let permits = types::PtrPermits::from_read_write(access.needs_read, access.needs_write);

                types::Type::new(types::TypeKind::Reference { pointee, permits })
            },
            TypeKind::Struct(ref fields) => {
                todo!("Not yet, structs!")
            },
        }
    }

    pub fn set_equal(&mut self, a: ValueId, b: ValueId, variance: Variance) {
        let a = get_real_value_id(&self.values, a);
        let b = get_real_value_id(&self.values, b);
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
        let a = get_real_value_id(&self.values, a);
        let b = get_real_value_id(&self.values, b);
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
        let a = get_real_value_id(&self.values, a);
        let b = get_real_value_id(&self.values, b);
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

        self.print_state();

        let mut i = 1;
        while let Some(available_id) = self.queued_constraints.pop() {
            i += 1;
            // println!("Applied constraint: {}", self.constraint_to_string(&self.constraints[available_id]));

            self.apply_constraint(available_id);

            // self.print_state();
        }

        self.print_state();

        println!("-- Number of steps required: {}", i);
    }

    pub fn value_to_str(&self, value: ValueId, rec: usize) -> String {
        use ValueKind::*;
        if rec > 7 {
            return "...".to_string();
        }
        match &self.values[value] {
            &MaybeMovedValue::Moved(new_index) => self.value_to_str(new_index, rec),
            MaybeMovedValue::Value(v) => match &v.kind {
                Access(None) => format!("_"),
                Access(Some(access)) => {
                    format!(
                        "{}{}",
                        match (access.needs_read, access.needs_write) {
                            (true, true) => "rw",
                            (true, false) => "r",
                            (false, true) => "w",
                            (false, false) => "!!",
                        },
                        // match (access.read && !access.needs_read, access.write && !access.needs_write) {
                        //     (true, true) => "+rw",
                        //     (true, false) => "+r",
                        //     (false, true) => "+w",
                        //     (false, false) => "",
                        // },
                        match (
                            !access.read && access.needs_read,
                            !access.write && access.needs_write
                        ) {
                            (true, true) => "-rw",
                            (true, false) => "-r",
                            (false, true) => "-w",
                            (false, false) => "",
                        },
                    )
                }
                Type(Some((TypeKind::Bool, _))) => "bool".to_string(),
                Type(Some((TypeKind::Empty, _))) => "Empty".to_string(),
                Type(None) => "_".to_string(),
                Value(None) => "_(value)".to_string(),
                Value(Some((type_, None))) => format!("(_: {})", self.value_to_str(*type_, rec + 1)),
                Value(Some((type_, Some(value)))) => {
                    format!("({}: {})", value, self.value_to_str(*type_, rec + 1))
                }
                Type(Some((TypeKind::Int(int_type_kind), _))) => format!("{:?}", int_type_kind),
                Type(Some((kind, None))) => format!("{:?}", kind),
                Type(Some((TypeKind::Function, Some(c)))) => match &**c {
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
                Type(Some((TypeKind::Struct(names), Some(c)))) => {
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
                Type(Some((TypeKind::Array, Some(c)))) => match &**c {
                    [type_, length] => format!(
                        "[{}; {}]",
                        self.value_to_str(*type_, rec + 1),
                        self.value_to_str(*length, rec + 1)
                    ),
                    _ => unreachable!("Arrays should only ever have two type parameters"),
                },
                Type(Some((TypeKind::Reference, Some(c)))) => match &**c {
                    [mutability, type_] => format!(
                        "&{} {}",
                        self.value_to_str(*mutability, rec + 1),
                        self.value_to_str(*type_, rec + 1)
                    ),
                    _ => unreachable!("References should only ever have one type parameter"),
                },
            },
        }
    }

    fn constraint_to_string(&self, constraint: &Constraint) -> String {
        match constraint.kind {
            ConstraintKind::Dead => format!("< removed >"),
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
        for i in 0..self.values.len() {
            println!("{}: {}", i, self.value_to_str(i, 0));
        }
        println!();

        println!("Queued constraints:");

        for &constraint in &self.queued_constraints {
            let constraint = &self.constraints[constraint];
            println!("{}", self.constraint_to_string(constraint));
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
            ConstraintKind::Dead => {},
            ConstraintKind::EqualNamedField {
                values: [a_id, b_id],
                index: field_name,
                variance,
            } => {
                let a = &get_value(&self.values, a_id).kind;

                use ValueKind::*;
                match a {
                    Type(None) => {}
                    Type(Some((TypeKind::Struct(names), _))) => {
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
                    Type(Some((_, _))) => {
                        self.errors.push(Error::new(
                            a_id,
                            b_id,
                            ErrorKind::NonexistantName(field_name),
                        ));
                        return;
                    }
                    Access(_) | Value(_) => {
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

                use ValueKind::*;
                match a {
                    Type(None) | Type(Some((_, None))) => {}
                    Type(Some((_, Some(fields)))) => {
                        if let Some(&field) = fields.get(field_index) {
                            let field = get_real_value_id(&self.values, field);
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
                    Access(_) | Value(_) => {
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
                debug_assert!(a_id < b_id);

                let values_len = self.values.len();
                let (a_slice, b_slice) = self.values.split_at_mut(b_id);
                // @Performance: Could be unreachable_unchecked in the future....
                let MaybeMovedValue::Value(Value { kind: a, value_sets: a_value_sets, .. }) = &mut a_slice[a_id] else {
                    unreachable!("It shouldn't be possible for the value of an equal constraint to be aliased")
                };
                let MaybeMovedValue::Value(Value { kind: b, value_sets: b_value_sets, .. }) = &mut b_slice[0] else {
                    unreachable!("It shouldn't be possible for the value of an equal constraint to be aliased")
                };

                use ErrorKind::*;
                match (a, b) {
                    (ValueKind::Type(a), ValueKind::Type(b)) => {
                        if false && variance == Variance::Invariant {
                            // @Performance: We can assume that it's not referenced.
                            let ValueKind::Type(a) = &get_value(&self.values, a_id).kind else { unreachable!() };
                            let ValueKind::Type(b) = &get_value(&self.values, b_id).kind else { unreachable!() };

                            let (from_id, to_id) = match (a, a_id, b, b_id) {
                                (None, from_id, None, to_id) |
                                (Some(_), to_id, None, from_id) |
                                (None, from_id, Some(_), to_id) => {
                                    (from_id, to_id)
                                }
                                (Some((to_head, Some(_))), to_id, Some((from_head, None)), from_id) |
                                (Some((from_head, None)), from_id, Some((to_head, Some(_))), to_id) |
                                (Some((to_head, None)), to_id, Some((from_head, None)), from_id) => {
                                    if *from_head != *to_head {
                                        self.errors
                                            .push(Error::new(a_id, b_id, ErrorKind::IncompatibleTypes));
                                        return;
                                    }

                                    (from_id, to_id)
                                }
                                (
                                    Some((a_head, Some(a_fields))), a_id,
                                    Some((b_head, Some(b_fields))), b_id,
                                ) => {
                                    if *a_head != *b_head || a_fields.len() != b_fields.len() {
                                        self.errors
                                            .push(Error::new(a_id, b_id, ErrorKind::IncompatibleTypes));
                                        return;
                                    }

                                    for (&a_field, &b_field) in a_fields.iter().zip(b_fields.iter()) {
                                        let a_field = get_real_value_id(&self.values, a_field);
                                        let b_field = get_real_value_id(&self.values, b_field);
                                        insert_active_constraint(
                                            &mut self.constraints,
                                            &mut self.available_constraints,
                                            &mut self.queued_constraints,
                                            Constraint::equal(a_field, b_field, Variance::Invariant),
                                        );
                                    }

                                    (a_id, b_id)
                                }
                            };

                            let from = &mut self.values[from_id];
                            let MaybeMovedValue::Value(from_value) = mem::replace(from, MaybeMovedValue::Moved(to_id)) else {
                                unreachable!("Cannot call combine_values on aliases")
                            };

                            // Combine the value sets together. (this should happen for children too!!!!!)
                            // @Speed: Could be a direct access, since to_id isn't aliased
                            let to_value = get_value_mut(&mut self.values, to_id);
                            for value_set in from_value.value_sets {
                                if let Err(index) = to_value.value_sets.binary_search(&value_set) {
                                    to_value.value_sets.insert(index, value_set);
                                }
                            }

                            // @TODO: Combine the reasons for the values e.t.c.

                            // Any constraints with the value should have the values id changed.
                            // This sets the current equality constraint to dead as well.
                            if let Some(affected_constraints) = self.available_constraints.remove(&from_id) {
                                for affected_constraint_id in affected_constraints {
                                    let affected_constraint = &mut self.constraints[affected_constraint_id];
                                    for value in affected_constraint.values_mut() {
                                        if *value == from_id {
                                            *value = to_id;
                                            self.available_constraints
                                                .entry(to_id)
                                                .or_insert_with(Vec::new)
                                                .push(affected_constraint_id);
                                        }
                                    }

                                    affected_constraint.fix_order();

                                    if !matches!(affected_constraint.kind, ConstraintKind::Dead) {
                                        self.queued_constraints.push(affected_constraint_id);
                                    }
                                }
                            }
                        } else {
                            let ((_, a_fields), (_, b_fields)) = match (a, b) {
                                (None, None) => return,
                                (Some(a), b @ None) => {
                                    progress[1] = true;
                                    let b = b.insert((a.0.clone(), None));
                                    (a, b)
                                }
                                (a @ None, Some(b)) => {
                                    progress[0] = true;
                                    (a.insert((b.0.clone(), None)), b)
                                }
                                (Some(a), Some(b)) => (a, b),
                            };

                            let [a_progress, b_progress, ..] = &mut progress;
                            match (a_fields, a_id, a_progress, b_fields, b_id, b_progress) {
                                (None, _, _, None, _, _) => return,
                                (Some(known), _, _, unknown @ None, unknown_id, unknown_progress)
                                | (unknown @ None, unknown_id, unknown_progress, Some(known), _, _) => {
                                    *unknown_progress = true;

                                    // We do this weird thing so we can utilize the mutable reference to unknown
                                    // before writing to values. After that we have to recompute the references
                                    // since they may have moved if the vector grew (one of the cases where
                                    // the borrow checker was right!)
                                    *unknown =
                                        Some((0..known.len()).map(|v| v + values_len).collect());

                                    let variant_fields = known.clone();

                                    // @Speed: Could be a direct access of the value.
                                    let base_value = get_value(&self.values, unknown_id);
                                    // @Speed: Allocation :(
                                    let base_value_sets = base_value.value_sets.clone();
                                    for &value_set in base_value_sets.iter() {
                                        self.value_sets[value_set].uncomputed_values += variant_fields.len() as i32 - 1;
                                    }

                                    for &v in variant_fields.iter() {
                                        let variant_value = get_value(&self.values, v);
                                        let kind = variant_value.kind.to_unknown();
                                        let new_value = Value {
                                            kind,
                                            reasons: Reasons::default(),
                                            value_sets: base_value_sets.clone(),
                                        };
                                        self.values.push(MaybeMovedValue::Value(new_value));
                                    }
                                }
                                (Some(_), _, _, Some(_), _, _) => {}
                            };

                            // @Duplicate code from above.
                            let a = &get_value(&self.values, a_id).kind;
                            let b = &get_value(&self.values, b_id).kind;
                            let (ValueKind::Type(Some((base_a, Some(a_fields)))), ValueKind::Type(Some((base_b, Some(b_fields))))) = (a, b) else {
                                // @Speed: Could be replaced with unreachable_unchecked in the real version.
                                unreachable!("Because of computations above, this is always true")
                            };

                            if *base_a != *base_b || a_fields.len() != b_fields.len() {
                                self.errors
                                    .push(Error::new(a_id, b_id, ErrorKind::IncompatibleTypes));
                                return;
                            }

                            // Ugly special case for references. This would apply for anything that has a
                            // mutability parameter that controls the variance of another field, because that behaviour
                            // is quite messy and complex.
                            if *base_a == TypeKind::Reference {
                                // @Cleanup: This has to be done because a has to be less than b, otherwise
                                // the lookups don't work properly. However, this is messy. So it would be nice if it
                                // could be factored out to something else.
                                let (a_access_id, a_inner, b_access_id, b_inner, variance) =
                                    if a_fields[0] < b_fields[0] {
                                        (a_fields[0], a_fields[1], b_fields[0], b_fields[1], variance)
                                    } else {
                                        (
                                            b_fields[0],
                                            b_fields[1],
                                            a_fields[0],
                                            a_fields[1],
                                            variance.invert(),
                                        )
                                    };

                                let a_access_id = get_real_value_id(&self.values, a_access_id);
                                let b_access_id = get_real_value_id(&self.values, b_access_id);
                                let a_inner = get_real_value_id(&self.values, a_inner);
                                let b_inner = get_real_value_id(&self.values, b_inner);

                                let &ValueKind::Access(a_access) = &get_value(&self.values, a_access_id).kind else { panic!() };
                                let &ValueKind::Access(b_access) = &get_value(&self.values, b_access_id).kind else { panic!() };

                                let guaranteed_variance = biggest_guaranteed_variance_of_operation(a_access.unwrap_or_default(), b_access.unwrap_or_default(), variance);
                                let variance_constraint = self
                                    .variance_updates
                                    .entry((a_access_id, b_access_id))
                                    .or_insert_with(|| VarianceConstraint {
                                        variance,
                                        last_variance_applied: guaranteed_variance,
                                        constraints: Vec::new(),
                                    });
                                // We use guaranteed_variance instead of last_variance_applied here, since if they are different
                                // it just means the VarianceConstraint has more work to do in the future to catch up, so we may as well
                                // do that work right now, and save some work in the future.
                                let inner_constraint = Constraint::equal(a_inner, b_inner, guaranteed_variance.apply_to(variance));
                                if let Some(inner_constraint_id) = insert_constraint(&mut self.constraints, &mut self.available_constraints, inner_constraint) {
                                    if !variance_constraint
                                        .constraints
                                        .iter()
                                        .any(|(v, _)| v == &inner_constraint_id)
                                    {
                                        variance_constraint.constraints.push((inner_constraint_id, variance));
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
                                    Constraint::equal(get_real_value_id(&self.values, a_fields[0]),get_real_value_id(&self.values, b_fields[0]), variance),
                                );
                                for (&a_field, &b_field) in a_fields[1..].iter().zip(&b_fields[1..]) {
                                    let a_field = get_real_value_id(&self.values, a_field);
                                    let b_field = get_real_value_id(&self.values, b_field);
                                    insert_active_constraint(
                                        &mut self.constraints,
                                        &mut self.available_constraints,
                                        &mut self.queued_constraints,
                                        Constraint::equal(
                                            a_field,
                                            b_field,
                                            variance.invert(),
                                        ),
                                    );
                                }
                            } else {
                                // Now, we want to apply equality to all the fields as well.
                                for (&a_field, &b_field) in a_fields.iter().zip(&**b_fields) {
                                    let a_field = get_real_value_id(&self.values, a_field);
                                    let b_field = get_real_value_id(&self.values, b_field);
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

                            // @Duplicate code: with stuff above.
                            // @Performance: Could be unreachable_unchecked in the future....
                            let (a_slice, b_slice) = self.values.split_at_mut(b_id);
                            let MaybeMovedValue::Value(Value { reasons: a_reasons, .. }) = &mut a_slice[a_id] else {
                                unreachable!("It shouldn't be possible for the value of an equal constraint to be aliased")
                            };
                            let MaybeMovedValue::Value(Value { reasons: b_reasons, .. }) = &mut b_slice[0] else {
                                unreachable!("It shouldn't be possible for the value of an equal constraint to be aliased")
                            };
                            // Combine the error message reasons for why these values are the way they are.
                            // It has to be down here so that it doesn't happen if there are any errors with the
                            // equality.
                            a_reasons.combine(b_reasons);
                        }
                    }

                    // @Cleanup: Clean up the whole value system.
                    // Shouldn't do it until I can test it though, right?
                    // Nothing is known, keep the constraint
                    (ValueKind::Value(None), ValueKind::Value(None))
                    | (ValueKind::Value(Some((_, None))), ValueKind::Value(Some((_, None)))) => {
                        return;
                    }
                    (ValueKind::Value(Some(known)), ValueKind::Value(unknown @ None))
                    | (ValueKind::Value(unknown @ None), ValueKind::Value(Some(known))) => {
                        progress[0] = true;
                        progress[1] = true;
                        *unknown = Some(*known);
                    }
                    (ValueKind::Value(Some((type_a, unknown @ None))), ValueKind::Value(Some((type_b, Some(known)))))
                    | (ValueKind::Value(Some((type_a, Some(known)))), ValueKind::Value(Some((type_b, unknown @ None)))) =>
                    {
                        if *type_a != *type_b {
                            self.errors.push(Error::new(a_id, b_id, IncompatibleTypes));
                            return;
                        }

                        *unknown = Some(*known);
                        progress[0] = true;
                        progress[1] = true;
                    }
                    (
                        ValueKind::Value(Some((type_a, Some(value_a)))),
                        ValueKind::Value(Some((type_b, Some(value_b)))),
                    ) => {
                        if *type_a != *type_b {
                            self.errors.push(Error::new(a_id, b_id, IncompatibleTypes));
                        }

                        if *value_a != *value_b {
                            self.errors.push(Error::new(a_id, b_id, IncompatibleValues));
                        }

                        progress[0] = true;
                        progress[1] = true;
                    }
                    (ValueKind::Access(a), ValueKind::Access(b)) => {
                        let a = a.get_or_insert_with(|| {
                            for &set_id in a_value_sets.iter() {
                                self.value_sets[set_id].uncomputed_values -= 1;
                            }
                            Access::default()
                        });
                        let b = b.get_or_insert_with(|| {
                            for &set_id in b_value_sets.iter() {
                                self.value_sets[set_id].uncomputed_values -= 1;
                            }
                            Access::default()
                        });

                        let old_a = *a;
                        let old_b = *b;
                        a.combine_with(b, variance);

                        progress[0] = old_a != *a;
                        progress[1] = old_b != *b;

                        if let Some(variance_constraint) =
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
                        self.errors
                            .push(Error::new(a_id, b_id, MixingTypesAndValues));
                    }
                }
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
                kind: ValueKind::Type(Some((_, ref params))),
                ..
            } => params.as_deref(),
            _ => None,
        }
    }

    pub fn add(&mut self, value: ValueKind, set: ValueSetId, reason: Reason) -> ValueId {
        let id = self.values.len();
        // TODO: Support values here too.
        if matches!(value, ValueKind::Type(None) | ValueKind::Type(Some((_, None)))) {
            self.value_sets[set].uncomputed_values += 1;
        }
        self.values.push(MaybeMovedValue::Value(Value {
            kind: value,
            reasons: Reasons::with_one(reason),
            value_sets: vec![set],
        }));
        id
    }

    fn add_without_reason(&mut self, value: ValueKind, set: ValueSetId) -> ValueId {
        // TODO: Support values here too.
        if matches!(value, ValueKind::Type(None) | ValueKind::Type(Some((_, None)))) {
            self.value_sets[set].uncomputed_values += 1;
        }
        let id = self.values.len();
        self.values.push(MaybeMovedValue::Value(Value {
            kind: ValueKind::Type(None),
            reasons: Reasons::default(),
            value_sets: vec![set],
        }));
        id
    }

    /// Adds a value set to a value. This value has to be an unknown type, otherwise it will panic
    /// in debug mode. It also cannot be an alias. This is solely intended for use by the building
    /// process of the typer.
    #[track_caller]
    pub fn set_value_set(&mut self, value_id: ValueId, value_set_id: ValueSetId) {
        println!("{}: put value {} in set {}", std::panic::Location::caller(), value_id, value_set_id);

        let MaybeMovedValue::Value(value) = &mut self.values[value_id] else {
            unreachable!("Cannot call set_value_set on an alias")
        };

        // There can be no children, this function shouldn't have to recurse.
        debug_assert!(matches!(value.kind, ValueKind::Type(None)));

        // We don't want to worry about sorting or binary searching
        debug_assert!(value.value_sets.is_empty());
        value.value_sets = vec![value_set_id];
        self.value_sets[value_set_id].uncomputed_values += 1;
    }

    pub fn add_unknown_type(&mut self) -> ValueId {
        let id = self.values.len();
        self.values.push(MaybeMovedValue::Value(Value {
            kind: ValueKind::Type(None),
            reasons: Reasons::default(),
            value_sets: Vec::new(),
        }));
        id
    }

    pub fn add_value(&mut self, value: impl IntoValue, set: ValueSetId, reason: Reason) -> ValueId {
        value.into_value(self, set, reason)
    }

    pub fn add_empty_access(&mut self, set: ValueSetId) -> ValueId {
        let id = self.values.len();
        self.values.push(MaybeMovedValue::Value(Value {
            kind: ValueKind::Access(None),
            reasons: Reasons::default(),
            value_sets: vec![set],
        }));
        id
    }

    pub fn add_access(&mut self, access: Option<Access>, set: ValueSetId, reason: Reason) -> ValueId {
        if access.is_none() {
            self.value_sets[set].uncomputed_values += 1;
        }
        self.add(ValueKind::Access(access), set, reason)
    }

    pub fn add_type(&mut self, type_: impl IntoType, set: ValueSetId, reason: Reason) -> ValueId {
        type_.into_type(self, set, reason)
    }
}

/// If a and b are accesses permissions used to determine the variance of an operation, and they are "equal" with a variance
/// relationship, what variance is the operation required to have at least?
///
/// Variances are seen as constraints, so if the operation _could_ be Invariant, this function may still return Covariant or
/// Variant, because applying both Covariant "equality" and Invariant "equality" is the same as just applying Invariant "equality".
fn biggest_guaranteed_variance_of_operation(a: Access, b: Access, variance: Variance) -> Variance {
    let (needs_read, needs_write) = match variance {
        Variance::Variant => (b.needs_read, b.needs_write),
        Variance::Covariant => (a.needs_read, a.needs_write),
        Variance::Invariant => (a.needs_read || b.needs_read, a.needs_write || b.needs_write),
        Variance::DontCare => (a.needs_read && b.needs_read, a.needs_write && b.needs_write),
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
    values: &Vec<MaybeMovedValue>,
    constraints: &mut Vec<Constraint>,
    available_constraints: &mut HashMap<ValueId, Vec<ConstraintId>>,
    queued_constraints: &mut Vec<ConstraintId>,
) {
    let &ValueKind::Access(a_access) = &get_value(&values, a).kind else { panic!() };
    let &ValueKind::Access(b_access) = &get_value(&values, b).kind else { panic!() };

    let new_variance =
        biggest_guaranteed_variance_of_operation(a_access.unwrap_or_default(), b_access.unwrap_or_default(), constraint.variance);

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
