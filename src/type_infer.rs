use crate::types::{self, IntTypeKind};
use crate::location::Location;
use std::collections::HashMap;
use std::iter::repeat_with;
use std::hint::unreachable_unchecked;
use std::mem;
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
    fn into_type(self, system: &mut TypeSystem) -> ValueId;
}

impl IntoType for CompilerType {
    fn into_type(self, system: &mut TypeSystem) -> ValueId {
        match self.0 .0.kind {
            types::TypeKind::Int(int_type_kind) => Int(int_type_kind).into_type(system),
            types::TypeKind::Empty => {
                system.add(ValueKind::Type(Some((TypeKind::Empty, Some(Box::new([]))))))
            }
            types::TypeKind::Bool => {
                system.add(ValueKind::Type(Some((TypeKind::Bool, Some(Box::new([]))))))
            }
            types::TypeKind::Reference { pointee, permits } => Ref(
                Access::new(permits.read(), permits.write()),
                CompilerType(pointee),
            )
            .into_type(system),
            types::TypeKind::Array(type_, length) => {
                Array(CompilerType(type_), length).into_type(system)
            }
            types::TypeKind::Struct(ref fields) => {
                let field_names = fields.iter().map(|v| v.0).collect();
                let field_types = fields
                    .iter()
                    .map(|v| CompilerType(v.1).into_type(system))
                    .collect();
                let value =
                    ValueKind::Type(Some((TypeKind::Struct(field_names), Some(field_types))));
                system.add(value)
            }
            _ => todo!("This compiler type is not done yet"),
        }
    }
}

impl<T: IntoType, V: IntoValue> IntoType for Array<T, V> {
    fn into_type(self, system: &mut TypeSystem) -> ValueId {
        let inner_type = self.0.into_type(system);
        let inner_value = self.1.into_value(system);
        system.add(ValueKind::Type(Some((
            TypeKind::Array,
            Some(Box::new([inner_type, inner_value])),
        ))))
    }
}

impl IntoType for Var {
    fn into_type(self, _: &mut TypeSystem) -> ValueId {
        self.0
    }
}

impl IntoType for Empty {
    fn into_type(self, system: &mut TypeSystem) -> ValueId {
        system.add(ValueKind::Type(Some((TypeKind::Empty, Some(Box::new([]))))))
    }
}

impl IntoType for Int {
    fn into_type(self, system: &mut TypeSystem) -> ValueId {
        system.add(ValueKind::Type(Some((
            TypeKind::Int(self.0),
            Some(Box::new([])),
        ))))
    }
}

impl IntoType for Unknown {
    fn into_type(self, system: &mut TypeSystem) -> ValueId {
        system.add_unknown_type()
    }
}

impl<T: IntoAccess, V: IntoType> IntoType for Ref<T, V> {
    fn into_type(self, system: &mut TypeSystem) -> ValueId {
        let inner_variance = self.0.into_variance(system);
        let inner_type = self.1.into_type(system);
        system.add(ValueKind::Type(Some((
            TypeKind::Reference,
            Some(Box::new([inner_variance, inner_type])),
        ))))
    }
}

pub trait IntoAccess {
    fn into_variance(self, system: &mut TypeSystem) -> ValueId;
}

impl IntoAccess for Access {
    fn into_variance(self, system: &mut TypeSystem) -> ValueId {
        system.add_access(self)
    }
}

impl IntoAccess for Var {
    fn into_variance(self, _: &mut TypeSystem) -> ValueId {
        self.0
    }
}

impl IntoAccess for Unknown {
    fn into_variance(self, system: &mut TypeSystem) -> ValueId {
        system.add_access(Access::default())
    }
}

pub trait IntoValue {
    fn into_value(self, system: &mut TypeSystem) -> ValueId;
}

impl<T: IntoType> IntoValue for WithType<T> {
    fn into_value(self, system: &mut TypeSystem) -> ValueId {
        let type_ = self.0.into_type(system);
        system.add(ValueKind::Value(Some((type_, None))))
    }
}

impl IntoValue for usize {
    fn into_value(self, system: &mut TypeSystem) -> ValueId {
        let int_type = system.add_type(Int(IntTypeKind::Usize));
        system.add(ValueKind::Value(Some((int_type, Some(self)))))
    }
}

impl IntoValue for Var {
    fn into_value(self, _: &mut TypeSystem) -> ValueId {
        self.0
    }
}

impl IntoValue for Unknown {
    fn into_value(self, system: &mut TypeSystem) -> ValueId {
        system.add(ValueKind::Value(None))
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
    // (type, type, type, ....)
    Tuple,
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

/*
/// Combines two values into one.
/// **this does not recurse**, so beware.
fn combine_values(
    values: &mut Vec<MaybeMovedValue>,
    constraints: &mut Vec<Constraint>,
    constraint_map: &mut HashMap<ValueId, Vec<ConstraintId>>,
    from_id: ValueId,
    to_id: ValueId,
) {
    let from = &mut values[from_id];
    let old_kind = mem::replace(&mut from.kind, ValueKind::Alias(to_id));

    // @TODO: Combine the reasons for the values e.t.c.

    // Any constraints with the value should have the values id changed.
    if let Some(affected_constraints) = constraint_map.get(&from_id) {
        for &affected_constraint_id in affected_constraints {
            let affected_constraint = &mut constraints[affected_constraint_id];
            for value in affected_constraint.values_mut() {
                if *value == from_id {
                    *value = to_id;
                }
            }

            affected_constraint.fix_order();
        }
    }
}
*/

pub enum ValueKind {
    Type(Option<(TypeKind, Option<Box<[ValueId]>>)>),

    /// For now values can only be usize, but you could theoretically have any value.
    Value(Option<(ValueId, Option<usize>)>),

    /// These are the only coerced values for now.
    Access(Access),
}

impl ValueKind {
    fn to_unknown(&self) -> Self {
        match self {
            Self::Type(_) => Self::Type(None),
            Self::Value(_) => Self::Value(None),
            Self::Access(_) => Self::Access(Access::default()),
        }
    }
}

/// This describes the reason why a value is the way it is.
/// For example, why is this a reference? Why is this a function? e.t.c.
/// This means we can give reasonable reporting when errors occur.
#[derive(Clone, Copy, PartialEq, Eq)]
struct ValueReason {
    pub location: Location,
    pub reason: &'static str,
}

#[derive(Default, Clone)]
struct ValueReasons {
    buffer: [Option<ValueReason>; 4],
    /// A flag for if there were more reasons that we couldn't fit into the structure.
    omitted_reasons: bool,
}

impl ValueReasons {
    fn insert(&mut self, value: ValueReason) {
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

    fn take_reasons_from(&mut self, other: ValueReasons) {
        for value in other.buffer.into_iter().filter_map(|v| v) {
            self.insert(value);
        }
    }
}

pub type ValueId = usize;

struct Value {
    kind: ValueKind,
    // reasons: ValueReasons,
    // /// If a value isn't known, it should generate an error, but if it's possible that it's not known because
    // /// an error occured, we don't want to generate an error, which is why this flag exists.
    // related_to_error: bool,
}

impl From<ValueKind> for Value {
    fn from(kind: ValueKind) -> Self {
        Self { kind }
    }
}

enum MaybeMovedValue {
    Value(Value),
    Moved(ValueId),
}

type ConstraintId = usize;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum Constraint {
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
        match self {
            Self::Equal { values: [a, b], variance } => {
                if a == b {
                    *self = Constraint::Dead;
                } else if a > b {
                    mem::swap(a, b);
                    *variance = variance.invert();
                }
            }
            Self::EqualsField { .. } | Self::EqualNamedField { .. } | Self::Dead => {}
        }
    }

    fn apply_variance(mut self, from: Variance) -> Self {
        if let Some(variance) = self.variance_mut() {
            *variance = from.apply_to(*variance);
        }

        self
    }

    fn values(&self) -> &[ValueId] {
        match self {
            Self::Equal { values, .. } | Self::EqualsField { values, .. } | Self::EqualNamedField { values, .. } => {
                &*values
            }
            Self::Dead => &[],
        }
    }

    fn values_mut(&mut self) -> &mut [ValueId] {
        match self {
            Self::Equal { values, .. } | Self::EqualsField { values, .. } | Self::EqualNamedField { values, .. } => {
                &mut *values
            }
            Self::Dead => &mut [],
        }
    }

    fn variance_mut(&mut self) -> Option<&mut Variance> {
        match self {
            Self::Equal { variance, .. } | Self::EqualsField { variance, .. } | Self::EqualNamedField { variance, .. } => Some(variance),
            Self::Dead => None,
        }
    }

    fn equal(a: ValueId, b: ValueId, variance: Variance) -> Self {
        if a == b {
            Self::Dead
        } else if b > a {
            Self::Equal { values: [a, b], variance }
        } else {
            Self::Equal {
                values: [b, a],
                variance: variance.invert(),
            }
        }
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
    if let Some(id) = constraints.iter().position(|v| v == &constraint) {
        return Some(id);
    }

    let id = constraints.len();
    constraints.push(constraint);

    match constraint {
        Constraint::Equal { values: [a, b], .. } => {
            if a == b {
                return None;
            };

            let vec = available_constraints.entry(a).or_insert_with(Vec::new);
            vec.push(id);

            let vec = available_constraints.entry(b).or_insert_with(Vec::new);
            vec.push(id);
        }
        Constraint::EqualsField { values: [a, _], .. }
        | Constraint::EqualNamedField { values: [a, _], .. } => {
            let vec = available_constraints.entry(a).or_insert_with(Vec::new);
            vec.push(id);
        }
        Constraint::Dead => {},
    }

    Some(id)
}

fn insert_active_constraint(
    constraints: &mut Vec<Constraint>,
    available_constraints: &mut HashMap<ValueId, Vec<ConstraintId>>,
    queued_constraints: &mut Vec<ConstraintId>,
    constraint: Constraint,
) {
    // @TODO: We want to check for equality things with just different variances here too, but I think
    // I have to change how constraints are represented first as well.
    if let Some(_) = constraints.iter().position(|v| v == &constraint) {
        return;
    }

    let id = constraints.len();
    constraints.push(constraint);

    match constraint {
        Constraint::Equal { values: [a, b], .. } => {
            if a == b {
                return;
            };

            let vec = available_constraints.entry(a).or_insert_with(Vec::new);
            vec.push(id);

            let vec = available_constraints.entry(b).or_insert_with(Vec::new);
            vec.push(id);
        }
        Constraint::EqualsField { values: [a, _], .. }
        | Constraint::EqualNamedField { values: [a, _], .. } => {
            let vec = available_constraints.entry(a).or_insert_with(Vec::new);
            vec.push(id);
        }
        Constraint::Dead => {},
    }

    queued_constraints.push(id);
}

pub struct TypeSystem {
    /// The first few values are always primitive values, with a fixed position, to make them trivial to create.
    /// 0 - Int
    values: Vec<MaybeMovedValue>,

    constraints: Vec<Constraint>,

    /// When the access level of certain things determine the variance of constraints, those constraints are put into here.
    variance_updates: HashMap<(ValueId, ValueId), VarianceConstraint>,

    available_constraints: HashMap<ValueId, Vec<ConstraintId>>,
    queued_constraints: Vec<ConstraintId>,

    errors: Vec<Error>,
}

impl TypeSystem {
    pub fn new() -> Self {
        Self {
            values: vec![],
            variance_updates: HashMap::new(),
            constraints: Vec::new(),
            available_constraints: HashMap::new(),
            queued_constraints: Vec::new(),
            errors: Vec::new(),
        }
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
            Constraint::EqualsField {
                values: [a, b],
                index: field_index,
                variance,
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
            Constraint::EqualNamedField {
                values: [a, b],
                index: field_name,
                variance,
            },
        );
    }

    pub fn solve(&mut self) {
        while let Some(available_id) = self.queued_constraints.pop() {
            // println!("Applied constraint: {}", self.constraint_to_string(&self.constraints[available_id]));

            self.apply_constraint(available_id);

            // self.print_state();
        }
    }

    pub fn value_to_str(&self, value: ValueId, rec: usize) -> String {
        use ValueKind::*;
        if rec > 7 {
            return "...".to_string();
        }
        match &self.values[value] {
            MaybeMovedValue::Moved(new_index) => format!("moved -> {}", new_index),
            MaybeMovedValue::Value(v) => match &v.kind {
                Access(access) => {
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
                Type(Some((TypeKind::Tuple, Some(arr)))) => format!(
                    "({})",
                    arr.iter()
                        .map(|&v| self.value_to_str(v, rec + 1))
                        .collect::<Vec<_>>()
                        .join(", ")
                ),
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
        match *constraint {
            Constraint::Dead => format!("< removed >"),
            Constraint::Equal {
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
            Constraint::EqualsField {
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
            Constraint::EqualNamedField {
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

        match constraint {
            Constraint::Dead => {},
            Constraint::EqualNamedField {
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
                                Constraint::EqualsField {
                                    values: [a_id, b_id],
                                    index: pos,
                                    variance,
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
            Constraint::EqualsField {
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
            Constraint::Equal {
                values: [a_id, b_id],
                variance,
            } => {
                debug_assert!(a_id < b_id);

                let values_len = self.values.len();
                let (a_slice, b_slice) = self.values.split_at_mut(b_id);
                // @Performance: Could be unreachable_unchecked in the future....
                let MaybeMovedValue::Value(Value { kind: a, .. }) = &mut a_slice[a_id] else {
                    unreachable!("It shouldn't be possible for the value of an equal constraint to be aliased")
                };
                let MaybeMovedValue::Value(Value { kind: b, .. }) = &mut b_slice[0] else {
                    unreachable!("It shouldn't be possible for the value of an equal constraint to be aliased")
                };

                use ErrorKind::*;
                match (a, b) {
                    // Nothing is known, keep the constraint
                    (ValueKind::Type(None), ValueKind::Type(None)) | (ValueKind::Type(Some((_, None))), ValueKind::Type(Some((_, None)))) => {
                        return;
                    }
                    (ValueKind::Type(a), ValueKind::Type(b)) => {
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
                        match (a_fields, a_progress, b_fields, b_progress) {
                            (None, _, None, _) => return,
                            (Some(known), _, unknown @ None, unknown_progress)
                            | (unknown @ None, unknown_progress, Some(known), _) => {
                                *unknown_progress = true;

                                if variance == Variance::Invariant {
                                    // In the invariant case it's much simpler.
                                    *unknown = Some(known.clone());
                                } else {
                                    // We do this weird thing so we can utilize the mutable reference to unknown
                                    // before writing to values. After that we have to recompute the references
                                    // since they may have moved if the vector grew (one of the cases where
                                    // the borrow checker was right!)
                                    *unknown =
                                        Some((0..known.len()).map(|v| v + values_len).collect());
                                    for &v in known.clone().iter() {
                                        let base_value = get_value_mut(&mut self.values, v).kind.to_unknown();
                                        self.values.push(MaybeMovedValue::Value(base_value.into()));
                                    }
                                }
                            }
                            (Some(_), _, Some(_), _) => {}
                        };

                        // @Duplicate code from above.
                        let (a_slice, b_slice) = self.values.split_at_mut(b_id);
                        let MaybeMovedValue::Value(Value { kind: a, .. }) = &mut a_slice[a_id] else {
                            unreachable!("It shouldn't be possible for the value of an equal constraint to be aliased")
                        };
                        let MaybeMovedValue::Value(Value { kind: b, .. }) = &mut b_slice[0] else {
                            unreachable!("It shouldn't be possible for the value of an equal constraint to be aliased")
                        };
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
                            let &ValueKind::Access(a_access) = &get_value(&self.values, a_access_id).kind else { panic!() };
                            let &ValueKind::Access(b_access) = &get_value(&self.values, b_access_id).kind else { panic!() };

                            let variance_constraint = self
                                .variance_updates
                                .entry((a_access_id, b_access_id))
                                .or_insert_with(|| VarianceConstraint {
                                    variance,
                                    last_variance_applied: biggest_guaranteed_variance_of_operation(a_access, b_access, variance),
                                    constraints: Vec::new(),
                                });
                            let inner_constraint = Constraint::equal(a_inner, b_inner, variance_constraint.last_variance_applied.apply_to(variance));
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
                                Constraint::equal(a_fields[0], b_fields[0], variance),
                            );
                            for (&a_field, &b_field) in a_fields[1..].iter().zip(&b_fields[1..]) {
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

                    // @Cleanup: Clean up the whole value system.
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
                        let old_a = *a;
                        let old_b = *b;
                        a.combine_with(b, variance);

                        progress[0] = old_a != *a;
                        progress[1] = old_b != *b;

                        if let Some(variance_constraint) =
                            self.variance_updates.get_mut(&(a_id, b_id))
                        {
                            variance_constraint.variance.combine(variance);
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

    pub fn add(&mut self, value: ValueKind) -> ValueId {
        let id = self.values.len();
        self.values.push(MaybeMovedValue::Value(value.into()));
        id
    }

    pub fn add_unknown_type(&mut self) -> ValueId {
        self.add(ValueKind::Type(None).into())
    }

    pub fn add_value(&mut self, value: impl IntoValue) -> ValueId {
        value.into_value(self)
    }

    pub fn add_access(&mut self, access: Access) -> ValueId {
        self.add(ValueKind::Access(access).into())
    }

    pub fn add_type(&mut self, type_: impl IntoType) -> ValueId {
        type_.into_type(self)
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
        biggest_guaranteed_variance_of_operation(a_access, b_access, constraint.variance);

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
