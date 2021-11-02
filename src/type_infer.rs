use std::collections::HashMap;
use std::iter::repeat_with;
use ustr::Ustr;
use crate::types::{self, IntTypeKind};

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
        match self.0.0.kind {
            types::TypeKind::Int(int_type_kind) => Int(int_type_kind).into_type(system),
            types::TypeKind::Empty => system.add(ValueKind::Type(Some((TypeKind::Empty, Some(Box::new([])))))),
            types::TypeKind::Bool => system.add(ValueKind::Type(Some((TypeKind::Bool, Some(Box::new([])))))),
            types::TypeKind::Reference { pointee, permits } =>
                Ref(Access::new(permits.read(), permits.write()), CompilerType(pointee)).into_type(system),
            types::TypeKind::Array(type_, length) =>
                Array(CompilerType(type_), length).into_type(system),
            types::TypeKind::Struct(ref fields) => {
                let field_names = fields.iter().map(|v| v.0).collect();
                let field_types = fields
                    .iter()
                    .map(|v| CompilerType(v.1).into_type(system))
                    .collect();
                let value = ValueKind::Type(Some((TypeKind::Struct(field_names), Some(field_types))));
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
        system.add(ValueKind::Type(Some((TypeKind::Array, Some(Box::new([inner_type, inner_value]))))))
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
        system.add(ValueKind::Type(Some((TypeKind::Int(self.0), Some(Box::new([]))))))
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
        system.add(ValueKind::Type(Some((TypeKind::Reference, Some(Box::new([inner_variance, inner_type]))))))
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
                (Variance::Covariant, Variance::Variant) | (Variance::Variant, Variance::Covariant) =>
                    *self = Variance::Invariant,
                (_, Variance::Invariant) => *self = Variance::Invariant,
                (_, Variance::DontCare) |
                    (Variance::Invariant, _) |
                    (Variance::Variant, Variance::Variant) |
                    (Variance::Covariant, Variance::Covariant) => {}
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

pub type ValueId = usize;

struct Value {
kind: ValueKind,
}

impl From<ValueKind> for Value {
    fn from(kind: ValueKind) -> Self {
        Self { kind }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum Constraint {
    /// Equal is almost equality, unless the is_variant field is set, then a will be variant to b.
    Equal { a: ValueId, b: ValueId, variance: Variance },
    EqualsField { a: (ValueId, usize), b: ValueId, variance: Variance },
    EqualNamedField { a: (ValueId, Ustr), b: ValueId, variance: Variance },
}

impl Constraint {
    fn apply_variance(self, from: Variance) -> Self {
        match self {
            Self::Equal { a, b, variance } => Self::Equal { a, b, variance: from.apply_to(variance) },
            Self::EqualsField { a, b, variance } => Self::EqualsField { a, b, variance: from.apply_to(variance) },
            Self::EqualNamedField { a, b, variance } => Self::EqualNamedField { a, b, variance: from.apply_to(variance) },
        }
    }

    fn equal(a: ValueId, b: ValueId, variance: Variance) -> Self {
        if b > a {
            Self::Equal { a, b, variance }
        } else {
            Self::Equal { a: b, b: a, variance: variance.invert() }
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
              constraints: Vec<Constraint>,
}

fn add_constraint(available_constraints: &mut HashMap<ValueId, Vec<Constraint>>, queued_constraints: &mut Vec<Constraint>, constraint: Constraint) {
    match constraint {
        Constraint::Equal { a, b, .. } => {
            if a == b { return };

            let vec = available_constraints.entry(a).or_insert_with(Vec::new);
            vec.push(constraint);

            let vec = available_constraints.entry(b).or_insert_with(Vec::new);
            vec.push(constraint);

            queued_constraints.push(constraint);
        }
        Constraint::EqualsField { a: (a, _), .. } | Constraint::EqualNamedField { a: (a, _), .. } => {
            let vec = available_constraints.entry(a).or_insert_with(Vec::new);
            vec.push(constraint);

            queued_constraints.push(constraint);
        }
    }
}

pub struct TypeSystem {
    /// The first few values are always primitive values, with a fixed position, to make them trivial to create.
    /// 0 - Int
values: Vec<Value>,

            /// When the access level of certain things determine the variance of constraints, those constraints are put into here.
            variance_updates: HashMap<(ValueId, ValueId), VarianceConstraint>,

            available_constraints: HashMap<ValueId, Vec<Constraint>>,
            queued_constraints: Vec<Constraint>,

            errors: Vec<Error>,
}

impl TypeSystem {
    pub fn new() -> Self {
        Self {
values: vec![],
        variance_updates: HashMap::new(),
        available_constraints: HashMap::new(),
        queued_constraints: Vec::new(),
        errors: Vec::new(),
        }
    }

    pub fn set_equal(&mut self, a: ValueId, b: ValueId, variance: Variance) {
        if a == b { return; }
        add_constraint(&mut self.available_constraints, &mut self.queued_constraints, Constraint::equal(a, b, variance));
    }

    pub fn set_field_equal(&mut self, a: ValueId, field_index: usize, b: ValueId, variance: Variance) {
        add_constraint(&mut self.available_constraints, &mut self.queued_constraints, Constraint::EqualsField { a: (a, field_index), b, variance });
    }

    pub fn set_field_name_equal(&mut self, a: ValueId, field_name: Ustr, b: ValueId, variance: Variance) {
        add_constraint(&mut self.available_constraints, &mut self.queued_constraints, Constraint::EqualNamedField { a: (a, field_name), b, variance });
    }

    pub fn solve(&mut self) {
        while let Some(available) = self.queued_constraints.pop() {
            self.apply_constraint(available);
            // self.print_state();
        }
    }

    pub fn value_to_str(&self, value: ValueId, rec: usize) -> String {
        use ValueKind::*;
        if rec > 7 { return "...".to_string(); }
        match &self.values[value].kind {
            Access(access) => {
                format!(
                    "{}{}{}",
                    match (access.needs_read, access.needs_write) {
                        (true, true) => "rw",
                        (true, false) => "r",
                        (false, true) => "w",
                        (false, false) => "[]",
                    },
                    match (access.read && !access.needs_read, access.write && !access.needs_write) {
                        (true, true) => "+rw",
                        (true, false) => "+r",
                        (false, true) => "+w",
                        (false, false) => "",
                    },
                    match (!access.read && access.needs_read, !access.write && access.needs_write) {
                        (true, true) => "!rw",
                        (true, false) => "!r",
                        (false, true) => "!w",
                        (false, false) => "",
                    },
                )
            }
            Type(Some((TypeKind::Bool, _))) => "bool".to_string(),
            Type(Some((TypeKind::Empty, _))) => "Empty".to_string(),
            Type(None) => "_".to_string(),
            Value(None) => "_(value)".to_string(),
            Value(Some((type_, None))) => format!("(_: {})", self.value_to_str(*type_, rec + 1)),
            Value(Some((type_, Some(value)))) => format!("({}: {})", value, self.value_to_str(*type_, rec + 1)),
            Type(Some((TypeKind::Int(int_type_kind), _))) => format!("{:?}", int_type_kind),
            Type(Some((kind, None))) => format!("{:?}", kind),
            Type(Some((TypeKind::Function, Some(c)))) => match &**c {
                [return_, args @ ..] => format!(
                    "({}) -> {}",
                    args.iter().map(|&v| self.value_to_str(v, rec + 1)).collect::<Vec<_>>().join(", "),
                    self.value_to_str(*return_, rec + 1),
                ),
                _ => unreachable!("A function pointer type has to have at least a return type"),
            },
            Type(Some((TypeKind::Struct(names), Some(c)))) => {
                let list = names.iter()
                    .zip(c.iter())
                    .map(|(name, type_)| format!("{}: {}", name, self.value_to_str(*type_, rec + 1)))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("{{ {} }}", list)
            }
            Type(Some((TypeKind::Array, Some(c)))) => match &**c {
                [type_, length] => format!("[{}; {}]", self.value_to_str(*type_, rec + 1), self.value_to_str(*length, rec + 1)),
                _ => unreachable!("Arrays should only ever have two type parameters"),
            },
            Type(Some((TypeKind::Tuple, Some(arr)))) => format!("({})", arr.iter().map(|&v| self.value_to_str(v, rec + 1)).collect::<Vec<_>>().join(", ")),
            Type(Some((TypeKind::Reference, Some(c)))) => match &**c {
                [mutability, type_] => format!("&{} {}", self.value_to_str(*mutability, rec + 1), self.value_to_str(*type_, rec + 1)),
                _ => unreachable!("References should only ever have one type parameter"),
            },
        }
    }

    fn constraint_to_string(&self, constraint: &Constraint) -> String {
        match *constraint {
            Constraint::Equal { a: a_id, b: b_id, variance } => {
                format!("{}({}) {} {}({})", a_id, self.value_to_str(a_id, 0), variance.to_string(), b_id, self.value_to_str(b_id, 0))
            }
            Constraint::EqualsField { a: (a_id, field_index), b: b_id, variance } => {
                format!("{}({}).{} {} {}({})", a_id, self.value_to_str(a_id, 0), field_index, variance.to_string(), b_id, self.value_to_str(b_id, 0))
            }
            Constraint::EqualNamedField { a: (a_id, field_name), b: b_id, variance } => {
                format!("{}({}).{} {} {}({})", a_id, self.value_to_str(a_id, 0), field_name, variance.to_string(), b_id, self.value_to_str(b_id, 0))
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

        for constraint in &self.queued_constraints {
            println!("{}", self.constraint_to_string(constraint));
        }
        println!();
    }

    pub fn finish(&self) {
        if !self.errors.is_empty() {
            println!("There were errors:");

            for error in &self.errors {
                println!("{}, {}\n{:?}", self.value_to_str(error.a, 0), self.value_to_str(error.b, 0), error.kind);
            }
        }
    }

    fn apply_constraint(&mut self, constraint: Constraint) {
        let mut a_progress = false;
        let mut b_progress = false;

        let mut add_constraint = |constraint: Constraint| {
            add_constraint(&mut self.available_constraints, &mut self.queued_constraints, constraint);
        };

        // @HACK: Later, we want arbitrary child-count constraints, and then this won't work.
        let (a_id, b_id) = match constraint {
            Constraint::Equal { a: a_id, b: b_id, .. } => (a_id, b_id),
            Constraint::EqualsField { a: (a_id, _), b: b_id, .. } => (a_id, b_id),
            Constraint::EqualNamedField { a: (a_id, _), b: b_id, .. } => (a_id, b_id),
        };

        match constraint {
            Constraint::EqualNamedField { a: (a_id, field_name), b: b_id, variance } => {
                let a = &self.values[a_id].kind;

                use ValueKind::*;
                match a {
                    Type(None) => {}
                    Type(Some((TypeKind::Struct(names), _))) => {
                        if let Some(pos) = names.iter().position(|&v| v == field_name) {
                            add_constraint(Constraint::EqualsField { a: (a_id, pos), b: b_id, variance });
                        } else {
                            self.errors.push(Error::new(a_id, b_id, ErrorKind::NonexistantName(field_name)));
                            return;
                        }
                    }
                    Type(Some((_, _))) => {
                        self.errors.push(Error::new(a_id, b_id, ErrorKind::NonexistantName(field_name)));
                        return;
                    }
                    Access(_) | Value(_) => {
                        self.errors.push(Error::new(a_id, b_id, ErrorKind::ValueAndTypesIntermixed));
                        return;
                    }
                }
            }
            Constraint::EqualsField { a: (a_id, field_index), b: b_id, variance } => {
                let a = &self.values[a_id].kind;

                use ValueKind::*;
                match a {
                    Type(None) | Type(Some((_, None))) => {}
                    Type(Some((_, Some(fields)))) => {
                        if let Some(&field) = fields.get(field_index) {
                            add_constraint(Constraint::equal(field, b_id, variance));
                        } else {
                            self.errors.push(Error::new(a_id, b_id, ErrorKind::IndexOutOfBounds(field_index)));
                            return;
                        }
                    }
                    Access(_) | Value(_) => {
                        self.errors.push(Error::new(a_id, b_id, ErrorKind::ValueAndTypesIntermixed));
                        return;
                    }
                }
            }
            Constraint::Equal { a: a_id, b: b_id, variance } => {
                if a_id == b_id { return; }

                debug_assert!(a_id < b_id);

                let values_len = self.values.len();
                let (a_slice, b_slice) = self.values.split_at_mut(b_id);
                let a = &mut a_slice[a_id].kind;
                let b = &mut b_slice[0].kind;

                use ValueKind::*;
                use ErrorKind::*;
                match (a, b) {
                    // Nothing is known, keep the constraint
                    (Type(None), Type(None)) | (Type(Some((_, None))), Type(Some((_, None)))) => {
                        return;
                    }
                    (Type(a), Type(b)) => {
                        let ((_, a_fields), (_, b_fields)) = match (a, b) {
                            (None, None) => return,
                            (Some(a), b @ None) => {
                                b_progress = true;
                                let b = b.insert((a.0.clone(), None));
                                (a, b)
                            }
                            (a @ None, Some(b)) => {
                                a_progress = true;
                                (a.insert((b.0.clone(), None)), b)
                            }
                            (Some(a), Some(b)) => (a, b),
                        };

                        match (a_fields, &mut a_progress, b_fields, &mut b_progress) {
                            (None, _, None, _) => return,
                            (Some(known), _, unknown @ None, unknown_progress) |
                            (unknown @ None, unknown_progress, Some(known), _) => {
                                *unknown_progress = true;

                                if variance == Variance::Invariant {
                                    // In the invariant case it's much simpler.
                                    *unknown = Some(known.clone());
                                } else {
                                    // We do this weird thing so we can utilize the mutable reference to unknown
                                    // before writing to values. After that we have to recompute the references
                                    // since they may have moved if the vector grew (one of the cases where
                                    // the borrow checker was right!)
                                    *unknown = Some((0..known.len()).map(|v| v + values_len).collect());
                                    for &v in known.clone().iter() {
                                        let base_value = self.values[v].kind.to_unknown();
                                        self.values.push(base_value.into());
                                    }
                                }
                            }
                            (Some(_), _, Some(_), _) => {}
                        };

                        // @Duplicate code from above.
                        let (a_slice, b_slice) = self.values.split_at_mut(b_id);
                        let a = &mut a_slice[a_id].kind;
                        let b = &mut b_slice[0].kind;
                        let (Type(Some((base_a, Some(a_fields)))), Type(Some((base_b, Some(b_fields))))) = (a, b) else {
                            // @Speed: Could be replaced with unreachable_unchecked in the real version.
                            unreachable!("Because of computations above, this is always true")
                        };

                        if *base_a != *base_b || a_fields.len() != b_fields.len() {
                            self.errors.push(Error::new(a_id, b_id, ErrorKind::IncompatibleTypes));
                            return;
                        }
                        
                        // Ugly special case for references. This would apply for anything that has a
                        // mutability parameter that controls the variance of another field, because that behaviour
                        // is quite messy and complex.
                        if *base_a == TypeKind::Reference {
                            let a_access_id = a_fields[0];
                            let b_access_id = b_fields[0];
                            let a_inner = a_fields[1];
                            let b_inner = b_fields[1];
                            let &ValueKind::Access(a_access) = &self.values[a_access_id].kind else { panic!() };
                            let &ValueKind::Access(b_access) = &self.values[b_access_id].kind else { panic!() };

                            let variance_constraint = self.variance_updates
                                .entry((a_access_id, b_access_id))
                                .or_insert_with(|| VarianceConstraint {
                                    variance,
                                    last_variance_applied: biggest_guaranteed_variance_of_operation(a_access, b_access, variance),
                                    constraints: Vec::new(),
                                });
                            let constraint = Constraint::equal(a_inner, b_inner, variance);
                            if !variance_constraint.constraints.iter().any(|v| v == &constraint) {
                                variance_constraint.constraints.push(constraint);
                                add_constraint(Constraint::equal(a_inner, b_inner, variance_constraint.last_variance_applied.apply_to(variance)));
                            }
                            add_constraint(Constraint::equal(a_access_id, b_access_id, variance));
                            // run_variance_constraint(variance_constraint, a_access_id, b_access_id, &self.values, &mut self.constraints);
                        } else {
                            // Now, we want to apply equality to all the fields as well.
                            for (&a_field, &b_field) in a_fields.iter().zip(&**b_fields) {
                                // @Improvement: Later, variance should be definable in a much more generic way(for generic types).
                                // In a generic type, you could paramaterize the mutability of something, which might then influence
                                // the variance of other parameters.
                                add_constraint(Constraint::equal(a_field, b_field, variance));
                            }
                        }
                    }

                    // @Cleanup: Clean up the whole value system.
                    // Nothing is known, keep the constraint
                    (Value(None), Value(None)) | (Value(Some((_, None))), Value(Some((_, None)))) => {
                        return;
                    }
                    (Value(Some(known)), Value(unknown @ None)) |
                    (Value(unknown @ None), Value(Some(known))) => {
                        a_progress = true;
                        b_progress = true;
                        *unknown = Some(*known);
                    }
                    (
                        Value(Some((type_a, unknown @ None))),
                        Value(Some((type_b, Some(known))))
                    ) |
                    (
                        Value(Some((type_a, Some(known)))),
                        Value(Some((type_b, unknown @ None))),
                    ) => {
                        if *type_a != *type_b {
                            self.errors.push(Error::new(a_id, b_id, IncompatibleTypes));
                            return;
                        }

                        *unknown = Some(*known);
                        a_progress = true;
                        b_progress = true;
                    }
                    (Value(Some((type_a, Some(value_a)))), Value(Some((type_b, Some(value_b))))) => {
                        if *type_a != *type_b {
                            self.errors.push(Error::new(a_id, b_id, IncompatibleTypes));
                        }

                        if *value_a != *value_b {
                            self.errors.push(Error::new(a_id, b_id, IncompatibleValues));
                        }

                        a_progress = true;
                        b_progress = true;
                    }
                    (Access(a), Access(b)) => {
                        let old_a = *a;
                        let old_b = *b;
                        a.combine_with(b, variance);

                        a_progress = old_a != *a;
                        b_progress = old_b != *b;

                        if let Some(variance_constraint) = self.variance_updates.get_mut(&(a_id, b_id)) {
                            variance_constraint.variance.combine(variance);
                            run_variance_constraint(variance_constraint, a_id, b_id, &self.values, &mut self.available_constraints, &mut self.queued_constraints);
                        }
                    }
                    _ => {
                        self.errors.push(Error::new(a_id, b_id, MixingTypesAndValues));
                    }
                }
            }
        }

        if a_progress {
            self.queued_constraints.extend(
                self.available_constraints
                    .get(&a_id)
                    .iter()
                    .flat_map(|v| v.iter())
                    .copied()
                    .filter(|v| v != &constraint)
            );
        }

        if b_progress {
            self.queued_constraints.extend(
                self.available_constraints
                    .get(&b_id)
                    .iter()
                    .flat_map(|v| v.iter())
                    .copied()
                    .filter(|v| v != &constraint)
            );
        }
    }

    pub fn params(&self, value: ValueId) -> Option<&[ValueId]> {
        match self.values[value] {
            Value {
                kind: ValueKind::Type(Some((_, ref params))),
                ..
            } => params.as_deref(),
            _ => None,
        }
    }

    pub fn add(&mut self, value: ValueKind) -> ValueId {
        let id = self.values.len();
        self.values.push(value.into());
        id
    }

    pub fn add_unknown_type(&mut self) -> ValueId {
        let id = self.values.len();
        self.values.push(ValueKind::Type(None).into());
        id
    }
    
    pub fn add_value(&mut self, value: impl IntoValue) -> ValueId {
        value.into_value(self)
    }

    pub fn add_access(&mut self, access: Access) -> ValueId {
        let id = self.values.len();
        self.values.push(ValueKind::Access(access).into());
        id
    }

    pub fn add_tuple(&mut self, length: usize) -> ValueId {
        let value = ValueKind::Type(Some((
            TypeKind::Tuple,
            Some(repeat_with(|| self.add_unknown_type()).take(length).collect()),
        )));
        let id = self.values.len();
        self.values.push(value.into());
        id
    }

    pub fn add_array(&mut self) -> ValueId {
        let inner_type = self.add_unknown_type();
        let length = self.add_value(WithType(Int(IntTypeKind::Usize)));

        let id = self.values.len();
        self.values.push(ValueKind::Type(Some((TypeKind::Array, Some(Box::new([inner_type, length]))))).into());
        id
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

fn run_variance_constraint(constraint: &mut VarianceConstraint, a: ValueId, b: ValueId, values: &[Value], available_constraints: &mut HashMap<ValueId, Vec<Constraint>>, queued_constraints: &mut Vec<Constraint>) {
    let &ValueKind::Access(a_access) = &values[a].kind else { panic!() };
    let &ValueKind::Access(b_access) = &values[b].kind else { panic!() };

    let new_variance = biggest_guaranteed_variance_of_operation(a_access, b_access, constraint.variance);

    if new_variance != constraint.last_variance_applied {
        for &constraint in &constraint.constraints {
            add_constraint(
                available_constraints,
                queued_constraints, 
                constraint.apply_variance(new_variance),
            );
        }
        constraint.last_variance_applied = new_variance;
    }
}
