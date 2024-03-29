//! Type inferrence system

/*

// Stores Values and Constraints  (Structures for now too)
{
    next_queued_constraint

    add_constraint

    // Adds value.
    add_dynamic_value

    // Adds a group of values for a subtree
    add_subtree_group

    // Gets a handle to a value
    get_value

    // Gets a mutable handle to a value, and marks it as updated.
    get_value_mut
}

*/

use crate::layout::StructLayout;
use crate::program::Program;
use crate::errors::ErrorCtx;
use crate::location::Location;
use crate::operators::BinaryOp;
use crate::types::{self, IntTypeKind, UniqueTypeMarker};
use crate::ast::{NodeId as AstNodeId};
use std::collections::HashMap;
use std::mem;
use ustr::Ustr;
use crate::program::constant::ConstantRef;

mod explain;
pub use explain::{get_reasons, Reason, ReasonKind};

mod value_sets;
pub use value_sets::{ValueSets, ValueSetId, ValueSet};
pub use crate::types::TypeKind;

const DEBUG: bool = false;

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

fn get_needed_children_for_layout<'a>(type_: &TypeKind, children: &'a [ValueId]) -> &'a [ValueId] {
    match type_ {
        TypeKind::Target { .. } | TypeKind::IntSize(_) | TypeKind::IntSigned(_) | TypeKind::Bool | TypeKind::Empty | TypeKind::Function | TypeKind::Reference | TypeKind::Buffer | TypeKind::ConstantValue(_) | TypeKind::CompareUnspecified => &[],
        TypeKind::Any { .. } => &children[0..1],
        // TODO: This can't have a size, we need some way to represent this.
        TypeKind::RuntimeGeneric { .. } => children,
        // TODO: This can't have a size, we need some way to represent this.
        TypeKind::MonomorphedRuntimeGeneric { .. } => children,
        TypeKind::Enum { .. } => &children[0..1],
        TypeKind::Float => &children[0..1],
        TypeKind::Int => &children[1..2],
        TypeKind::Array => children,
        TypeKind::Struct(_) => children,
        TypeKind::Tuple => children,
        TypeKind::Unique(_) => children,
        // A constant pretends to care about the actual ConstantValue for the layout as well. This is not
        // because it "needs" to itself, but because things that need the constant, like the arrays layout,
        // does actually care about the value, so if it isn't required we get problems.
        TypeKind::Constant => children,
    }
}

fn compute_type_layout(kind: &TypeKind, structures: &Structures, values: &Values, children: &[ValueId]) -> Layout {
    match kind {
        TypeKind::CompareUnspecified => Layout { size: 1, align: 0 },
        // TODO: This shouldn't even have a Layout, but I have no way of representing this yet.
        // Even worse, it _may_ have a runtime layout if the `any`/`all` type has the layout
        // tag on the generic.
        TypeKind::RuntimeGeneric { .. } => Layout { size: 0, align: 1 },
        // TODO: This shouldn't even have a Layout, but I have no way of representing this yet.
        // Even worse, it _may_ have a runtime layout if the `any`/`all` type has the layout
        // tag on the generic.
        TypeKind::MonomorphedRuntimeGeneric { .. } => Layout { size: 0, align: 1 },
        TypeKind::Any { .. } => *get_value(structures, values, children[0]).layout.unwrap(),
        TypeKind::Float => {
            let Some(&Type { kind: TypeKind::IntSize(size_value), .. }) = get_value(structures, values, children[0]).kind else { panic!() };
            let size_bytes = size_value as usize;
            Layout { size: size_bytes, align: size_bytes }
        }
        TypeKind::Int => {
            let Some(&Type { kind: TypeKind::IntSize(size_value), .. }) = get_value(structures, values, children[1]).kind else { panic!() };
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
        TypeKind::Enum { .. } => *get_value(structures, values, children[0]).layout.unwrap(),
        TypeKind::Unique(_) => *get_value(structures, values, children[0]).layout.unwrap(),
        TypeKind::IntSize(_) => Layout { size: 1, align: 1 },
        TypeKind::IntSigned(_) => Layout { size: 1, align: 1 },
        TypeKind::Bool => Layout { size: 1, align: 1 },
        TypeKind::Empty => Layout { size: 0, align: 1 },
        TypeKind::Buffer => Layout { size: 16, align: 8 },
        TypeKind::Reference | TypeKind::Function => Layout { size: 8, align: 8 },
        TypeKind::Array => {
            // @Correctness: We want to make sure that the type actually is a usize here
            let length = extract_constant_from_value(structures, values, children[1]).unwrap();
            let length = unsafe { *length.as_ptr().cast::<usize>() };
            let inner_layout = get_value(structures, values, children[0]).layout.unwrap();
            debug_assert!(inner_layout.align != 0);
            Layout { size: length * inner_layout.size, align: inner_layout.align }
        }
        TypeKind::Struct(_) | TypeKind::Tuple => {
            let mut size = 0;
            let mut align = 1;
            for &child in children {
                let child_layout = get_value(structures, values, child).layout.unwrap();
                debug_assert_ne!(child_layout.align, 0);
                size += child_layout.size;
                align = align.max(child_layout.align);
                size = crate::types::to_align(size, child_layout.align);
            }
            size = crate::types::to_align(size, align);
            Layout { size, align }
        }
        TypeKind::Target { .. } | TypeKind::ConstantValue(_) => Layout { size: 0, align: 1 },
        TypeKind::Constant => *get_value(structures, values, children[0]).layout.unwrap(),
    }
}

#[derive(Debug, Clone)]
pub struct Type {
    pub kind: TypeKind,
    pub args: Option<Box<[ValueId]>>,
}

type ConstraintId = usize;
pub type ComparisonId = usize;

#[derive(Debug, Clone, Copy)]
struct Constraint {
    kind: ConstraintKind,
    applied: bool,
    reason: Reason,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum Relation {
    NamedConstField(Ustr),
    InnerConstant,
    Pack {
        unpacking: bool,
    },
    Cast,
    BufferEqualsArray,
    ForIterator { by_reference: bool },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum ConstraintKind {
    RequireSize {
        value_id: ValueId,
        value_set_id: ValueSetId,
    },
    DynMonomorph {
        values: [ValueId; 2],
        monomorph_id: u32,
        marker: UniqueTypeMarker,
    },
    Compare {
        values: [ValueId; 2],
        comparison: ComparisonId,
    },
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
    },
    EqualsField {
        values: [ValueId; 2],
        index: usize,
    },
    EqualNamedField {
        values: [ValueId; 2],
        index: Ustr,
        hidden_subdivisions: u8,
    },
}

impl Constraint {
    fn values(&self) -> &[ValueId] {
        match &self.kind {
            ConstraintKind::RequireSize { value_id, .. } => std::slice::from_ref(value_id),
            ConstraintKind::Relation { values, .. } => &*values,
            ConstraintKind::Equal { values, .. }
            | ConstraintKind::Compare { values, .. }
            | ConstraintKind::DynMonomorph { values, .. }
            | ConstraintKind::EqualsField { values, .. }
            | ConstraintKind::EqualNamedField { values, .. } => &*values,
            ConstraintKind::BinaryOp { values, .. } => &*values,
        }
    }

    fn equal(a: ValueId, b: ValueId, creator: Option<ConstraintId>, reason: Reason) -> Self {
        let kind = ConstraintKind::Equal {
            values: [a, b],
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
    PackingNonUnique,
    IncompatibleTypes,
    IndexOutOfBounds(usize),
    NonexistantName(Ustr),
}

fn extract_constant_from_value(structures: &Structures, values: &Values, value: ValueId) -> Option<ConstantRef> {
    let Some(Type { kind: TypeKind::Constant, args: Some(args) }) = get_value(structures, values, value).kind else {
        return None
    };

    let Some(Type { kind: TypeKind::ConstantValue(constant_ref), .. }) = get_value(structures, values, *args.get(1)?).kind else {
        return None;
    };

    Some(*constant_ref)
}

fn get_value<'a>(structures: &'a Structures, values: &'a Values, id: ValueId) -> ValueBorrow<'a> {
    let value = values.get(id);
    match value.structure_id {
        Some(id) => {
            let structure = &structures.structure[id as usize];
            ValueBorrow {
                structure_id: value.structure_id,
                kind: structure.kind.as_ref(),
                layout: Some(&structure.layout),
                is_base_value: &value.value.is_base_value,
            }
        }
        None => ValueBorrow {
            structure_id: value.structure_id,
            kind: None,
            layout: None,
            is_base_value: &value.value.is_base_value,
        }
    }
}

fn get_value_mut<'a>(structures: &'a mut Structures, values: &'a mut Values, id: ValueId) -> ValueBorrowMut<'a> {
    let value = values.get_mut(id);
    match value.structure_id {
        Some(id) => {
            let structure = &mut structures.structure[id as usize];
            ValueBorrowMut {
                kind: structure.kind.as_mut(),
                layout: Some(&mut structure.layout),
                is_base_value: &mut value.value.is_base_value,
            }
        }
        None => {
            ValueBorrowMut {
                kind: None,
                layout: None,
                is_base_value: &mut value.value.is_base_value,
            }
        }
    }
}

fn get_or_define_structure_of_value<'a>(structures: &'a mut Structures, values: &mut Values, id: ValueId) -> &'a mut StructureGroup {
    let value = values.get_mut(id);
    match value.structure_id {
        Some(id) => &mut structures.structure[id as usize],
        None => {
            let structure_id = structures.structure.len() as u32;
            structures.structure.push(StructureGroup::with_single(id));
            value.structure_id = Some(structure_id);
            structures.structure.last_mut().unwrap()
        }
    }
}

fn insert_constraint(
    constraints: &mut Vec<Constraint>,
    available_constraints: &mut HashMap<ValueId, Vec<ConstraintId>>,
    constraint: Constraint,
) -> Option<ConstraintId> {
    // @Performance: We can do a faster lookup using available_constraints.
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
) -> bool {
    // @Performance: We can do a faster lookup using available_constraints
    if !matches!(constraint.kind, ConstraintKind::Compare { .. }) {
        if let Some(_) = constraints.iter().position(|v| v.kind == constraint.kind) {
            return false;
        }
    }

    // We probably want to find a dead constraint to slot things into? Should we have a list of dead constraints that are available, or is that getting too overkill?
    let id = constraints.len();
    constraints.push(constraint);

    match constraint.kind {
        ConstraintKind::Equal { values: [a, b], .. } => {
            if a == b {
                return false;
            };
        }
        _ => {}
    }

    for &value in constraint.values() {
        let vec = available_constraints.entry(value).or_insert_with(Vec::new);
        vec.push(id);
    }

    queued_constraints.push(id);

    true
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct AstVariantId(u32);

impl AstVariantId {
    pub fn root() -> Self {
        AstVariantId(0)
    }

    pub fn invalid() -> Self {
        AstVariantId(u32::MAX)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ValueId {
    None,
    Dynamic(u32),
    Node(AstVariantId, AstNodeId),
}

impl Default for ValueId {
    fn default() -> Self {
        Self::None
    }
}

impl ValueId {
    pub const NONE: Self = Self::None;
}

#[derive(Default, Debug, Clone)]
struct Value {
    is_base_value: bool,
}

#[derive(Clone, Copy)]
pub struct ValueBorrow<'a> {
    structure_id: Option<u32>,
    pub kind: Option<&'a Type>,
    pub layout: Option<&'a Layout>,
    is_base_value: &'a bool,
}

impl ValueBorrow<'_> {
    pub fn kind(&self) -> &TypeKind {
        &self.kind.as_ref().expect("Called kind on unknown type").kind
    }

    pub fn args(&self) -> &[ValueId] {
        &self.kind.as_ref().unwrap().args.as_ref().unwrap()
    }

    pub fn layout(&self) -> Layout {
        *self.layout.unwrap()
    }
}

pub struct ValueBorrowMut<'a> {
    pub kind: Option<&'a mut Type>,
    pub layout: Option<&'a mut Layout>,
    pub is_base_value: &'a mut bool,
}

// @Temporary: Should be replaced with the real value some day
#[derive(Default, Clone)]
pub struct ValueWrapper {
    value: Value,
    structure_id: Option<u32>,
    next_in_structure_group: ValueId,
}

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Layout {
    pub size: usize,
    // An align of zero means that the size hasn't been calculated yet, and the number is how many children types
    // have to be known.
    pub align: usize,
}

impl Layout {
    pub const ZST: Self = Self { size: 0, align: 1 };
    pub const PTR: Self = Self { size: 8, align: 8 };
    pub const U64: Self = Self { size: 8, align: 8 };
    pub const U8: Self = Self { size: 1, align: 1 };
    pub const USIZE: Self = Self { size: 8, align: 8 };

    pub const BOOL: Self = Self { size: 1, align: 1 };
}

#[derive(Clone, Default)]
struct StructureGroup {
    first_value: ValueId,
    kind: Option<Type>,
    layout: Layout,
    layout_dependants: Vec<ValueId>,
    num_values: u32,
}

impl StructureGroup {
    fn with_single(first_value: ValueId) -> Self {
        Self {
            first_value,
            kind: None,
            layout: Layout::default(),
            layout_dependants: Vec::new(),
            num_values: 1,
        }
    }
}

#[derive(Default, Clone)]
struct Structures {
    structure: Vec<StructureGroup>,
}

fn iter_values_in_structure<'a>(structures: &Structures, values: &'a Values, value_id: ValueId) -> impl Iterator<Item = ValueId> + 'a {
    let value = values.get(value_id);
    let mut value_id = match value.structure_id {
        Some(id) => structures.structure[id as usize].first_value,
        None => value_id,
    };
    std::iter::from_fn(move || {
        if value_id == ValueId::NONE { return None; }
        let v = value_id;
        let value = values.get(value_id);
        value_id = value.next_in_structure_group;
        Some(v)
    })
}

fn structurally_combine(structures: &mut Structures, values: &mut Values, computable_sizes: &mut Vec<ValueId>, a: ValueId, b: ValueId) {
    let a_value = values.get(a);
    let structure_id = a_value.structure_id;
    let b_value = values.get(b);
    let old_b_structure_id = b_value.structure_id;

    if structure_id.is_some() && structure_id == old_b_structure_id {
        return;
    }

    let b_structure = match old_b_structure_id {
        Some(id) => mem::take(&mut structures.structure[id as usize]),
        None => StructureGroup::with_single(b),
    };

    let structure_id = structure_id.unwrap_or_else(|| {
        let id = structures.structure.len() as u32;
        structures.structure.push(StructureGroup::with_single(a));
        values.get_mut(a).structure_id = Some(id);
        id
    });

    let a_structure = &mut structures.structure[structure_id as usize];

    a_structure.num_values += b_structure.num_values;
    match (a_structure.layout.align > 0, b_structure.layout.align > 0) {
        (true, false) => {
            for dependant in b_structure.layout_dependants {
                let dependant_structure_id = values.get(dependant).structure_id.expect("If you depend on the size of another value, you have to have a structure");
                let dependant_structure = &mut structures.structure[dependant_structure_id as usize];

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
        let value = values.get_mut(value_id);
        if value.next_in_structure_group == ValueId::None {
            value.next_in_structure_group = b_structure.first_value;
            break;
        }
        value_id = value.next_in_structure_group;
    }

    // Convert the old structure list to the new structure
    let mut value_id = b_structure.first_value;
    loop {
        let value = values.get_mut(value_id);
        value.structure_id = Some(structure_id);
        if value.next_in_structure_group == ValueId::None {
            break;
        }
        value_id = value.next_in_structure_group;
    }
}

fn compute_size(structures: &mut Structures, values: &mut Values, computable_sizes: &mut Vec<ValueId>, id: ValueId) {
    let id = values.get(id).structure_id.expect("Cannot compute the size of something that doesn't even have a kind");
    let structure = &structures.structure[id as usize];
    if structure.layout.align > 0 {
        // We already know what the layout
        return;
    }
    let Some(Type { kind, args: Some(args) }) = &structure.kind else {
        unreachable!("Cannot call compute_size on an incomplete value")
    };
    let layout = compute_type_layout(kind, structures, values, args);

    let structure = &mut structures.structure[id as usize];
    structure.layout = layout;

    // @Hack! Maybe?
    if layout.align == 0 {
        return;
    }

    // Because we've computed the layout, we can complete all the value sets.
    let mut value_id = structure.first_value;
    loop {
        let value = values.get_mut(value_id);
        if value.next_in_structure_group == ValueId::NONE {
            break;
        }
        value_id = value.next_in_structure_group;
    }

    let layout_dependants = mem::take(&mut structure.layout_dependants);
    for dependant in layout_dependants {
        let value = get_value_mut(structures, values, dependant);
        let mut layout = value.layout.expect("Dependant of a layout has to have a defined structure, how else could it depend on a layout?");
        if layout.align == 0 {
            layout.size -= 1;
            if layout.size == 0 {
                computable_sizes.push(dependant);
            }
        }
    }
}

fn set_value(structures: &mut Structures, values: &mut Values, id: ValueId, kind: Type) {
    let mut layout = Layout::default();
    if let Type { args: Some(args), kind } = &kind {
        let mut number = 0;
        // @Improvement: We need to figure out how to recursively determine
        // type completion, for when we're going to insert it as a type
        // id.
        for &needed in args.iter() { // get_needed_children_for_layout(kind, &args)
            let structure = get_or_define_structure_of_value(structures, values, needed);
            if structure.layout.align == 0 {
                number += 1;
                structure.layout_dependants.push(id);
            }
        }

        if number == 0 {
            layout = compute_type_layout(kind, structures, values, args);
        } else {
            layout.size = number;
        }
    }

    let structure = get_or_define_structure_of_value(structures, values, id);
    debug_assert_eq!(structure.layout.size, 0);
    debug_assert_eq!(structure.layout.align, 0);
    debug_assert_eq!(structure.num_values, 1);
    // debug_assert!(structure.layout_dependants.is_empty());
    structure.kind = Some(kind);
    structure.layout = layout;
}

fn add_value(structures: &mut Structures, values: &mut Values, kind: Option<Type>) -> ValueId {
    let id = ValueId::Dynamic(values.values.len() as u32);

    if let Some(kind) = kind {
        let structure_id = structures.structure.len() as u32;
        structures.structure.push(StructureGroup::with_single(id));
        values.values.push(ValueWrapper {
            value: Value { is_base_value: false },
            structure_id: Some(structure_id),
            next_in_structure_group: ValueId::NONE,
        });
        set_value(structures, values, id, kind);
    } else {
        values.values.push(ValueWrapper {
            value: Value { is_base_value: false },
            structure_id: None,
            next_in_structure_group: ValueId::NONE,
        });
    }
    id
}

#[derive(Clone, Default)]
struct AstValues {
    parent: Option<AstVariantId>,
    base_id: u32,
    nodes: Box<[ValueWrapper]>,
}

#[derive(Clone)]
pub struct Values {
    values: Vec<ValueWrapper>,
    ast_values: Vec<AstValues>,
}

impl Values {
    fn new(ast_size: usize) -> Self {
        Self {
            values: Vec::with_capacity(32),
            ast_values: vec![
                AstValues {
                    parent: None,
                    base_id: 0,
                    nodes: vec![ValueWrapper::default(); ast_size].into_boxed_slice(),
                },
            ],
        }
    }

    pub fn add_ast_variant(&mut self, parent_id: AstVariantId, (base_id, size): (AstNodeId, usize)) -> AstVariantId {
        let id = self.ast_values.len();
        self.ast_values.push(AstValues {
            parent: Some(parent_id),
            base_id: base_id.0,
            nodes: vec![ValueWrapper::default(); size].into_boxed_slice(),
        });
        AstVariantId(id as u32)
    }
    
    fn structure_id_of_value(&self, value_id: ValueId) -> Option<u32> {
        self.get(value_id).structure_id
    }

    fn get(&self, id: ValueId) -> &ValueWrapper {
        match id {
            ValueId::None => unreachable!("Tried reading from a ValueId::None"),
            ValueId::Dynamic(id) => &self.values[id as usize],
            ValueId::Node(variant_id, id) => {
                let mut variant = &self.ast_values[variant_id.0 as usize];
                while variant.base_id > id.0 || variant.base_id + variant.nodes.len() as u32 <= id.0 {
                    let parent_id = variant.parent.expect("The node id seems to be out of bounds");
                    variant = &self.ast_values[parent_id.0 as usize];
                }
                let base_id = variant.base_id;
                &variant.nodes[usize::from(id) - base_id as usize]
            }
        }
    }

    fn get_mut(&mut self, id: ValueId) -> &mut ValueWrapper {
        match id {
            ValueId::None => unreachable!("Tried reading from a ValueId::None"),
            ValueId::Dynamic(id) => &mut self.values[id as usize],
            ValueId::Node(mut variant_id, id) => {
                let mut variant = &self.ast_values[variant_id.0 as usize];
                while variant.base_id > id.0 || variant.base_id + variant.nodes.len() as u32 <= id.0 {
                    variant_id = variant.parent.expect("The node id seems to be out of bounds");
                    variant = &self.ast_values[variant_id.0 as usize];
                }
                let base_id = variant.base_id;
                &mut self.ast_values[variant_id.0 as usize].nodes[usize::from(id) - base_id as usize]
            }
        }
    }
}

pub fn get_loc_of_value(ast: &crate::parser::Ast, value: ValueId) -> Option<Location> {
    match value {
        ValueId::Node(_, id) => Some(ast.get(id).loc),
        _ => None,
    }
}

#[derive(Clone)]
struct Comparison {
    left_to_do: u32,
    value: Option<bool>,
    value_set: ValueSetId,
}

#[derive(Clone)]
struct Monomorph {
    // TODO: We can probably get away with just using a single type id and generating an array of them.
    arg_types: Vec<ValueId>,
}

#[derive(Clone)]
pub struct TypeSystem {
    comparisons: Vec<Comparison>,
    structures: Structures,
    pub values: Values,

    pub value_sets: ValueSets,

    constraints: Vec<Constraint>,
    computable_value_sizes: Vec<ValueId>,

    available_constraints: HashMap<ValueId, Vec<ConstraintId>>,
    queued_constraints: Vec<ConstraintId>,

    monomorphs: Vec<Monomorph>,

    pub errors: Vec<Error>,
}

impl TypeSystem {
    pub fn new(ast_size: usize) -> Self {
        Self {
            comparisons: Vec::new(),
            structures: Structures::default(),
            values: Values::new(ast_size),
            value_sets: ValueSets::default(),
            constraints: Vec::new(),
            computable_value_sizes: Vec::new(),
            available_constraints: HashMap::new(),
            queued_constraints: Vec::new(),
            errors: Vec::new(),
            monomorphs: Vec::new(),
        }
    }

    pub fn members(&self, type_id: ValueId, mut callback: impl FnMut(MemberInfo) -> bool) {
        let type_ = self.get(type_id);

        match type_.kind() {
            TypeKind::Struct(names) => {
                let mut struct_layout = StructLayout::new(0);
                for (index, (&name, &arg)) in names.iter().zip(type_.args()).enumerate() {
                    let arg_type = self.get(arg);
                    let arg_layout = arg_type.layout();
                    let offset = struct_layout.next(arg_layout);
                    
                    if !callback(MemberInfo { name, index, offset, layout: arg_layout }) {
                        break;
                    }
                }
            }
            TypeKind::Buffer => {
                if !callback(MemberInfo { name: "ptr".into(), index: 0, offset: 0, layout: Layout::PTR }) {
                    return;
                }

                if !callback(MemberInfo { name: "len".into(), index: 1, offset: 8, layout: Layout::USIZE }) {
                    return;
                }
            }
            TypeKind::Tuple => {
                let mut struct_layout = StructLayout::new(0);
                for (index, &arg) in type_.args().iter().enumerate() {
                    let arg_type = self.get(arg);
                    let arg_layout = arg_type.layout();
                    let offset = struct_layout.next(arg_layout);
                    // @Speed!
                    let name = format!("_{}", index).into();
                    
                    if !callback(MemberInfo { name, index, offset, layout: arg_layout }) {
                        break;
                    }
                }
            }
            TypeKind::Array => {
                let &[element, len] = type_.args() else { panic!() };
                let element_layout = self.get(element).layout();

                // @Safety: This can be safer with future checks.
                let length_ptr = self.extract_constant_temp(len).unwrap();
                let length = unsafe { *length_ptr.as_ptr().cast::<usize>() };

                let mut struct_layout = StructLayout::new(0);
                for index in 0..length {
                    // @Speed!
                    let name = format!("_{}", index).into();
                    let offset = struct_layout.next(element_layout);

                    if !callback(MemberInfo { name, index, offset, layout: element_layout }) {
                        break;
                    }
                }
            }
            _ => {}
        };
    }

    pub fn get_member_by_name(&self, on: ValueId, name: Ustr) -> Option<MemberInfo> {
        let mut info = None;

        self.members(on, |member_info| {
            if member_info.name == name {
                info = Some(member_info);
                false
            } else {
                true
            }
        });

        info
    }

    pub fn get_member_by_index(&self, on: ValueId, index: usize) -> Option<MemberInfo> {
        let mut info = None;

        self.members(on, |member_info| {
            if member_info.index == index {
                info = Some(member_info);
                false
            } else {
                true
            }
        });

        info
    }

    fn resolve_comparison(&mut self, comparison: ComparisonId, result: bool) {
        let comparison = &mut self.comparisons[comparison];

        debug_assert!(comparison.left_to_do > 0);
        comparison.left_to_do -= 1;

        if result == false {
            comparison.value = Some(false);
        }

        if comparison.left_to_do == 0 {
            comparison.value.get_or_insert(result);
            self.value_sets.unlock(comparison.value_set);
        }
    }

    pub fn get_comparison_result(&self, id: ComparisonId) -> bool {
        self.comparisons[id].value.unwrap()
    }

    pub fn add_comparison(&mut self, value_set: ValueSetId, from: ValueId, to: ValueId) -> ComparisonId {
        let id = self.comparisons.len();
        self.comparisons.push(Comparison {
            left_to_do: 1,
            value: None,
            value_set,
        });

        self.value_sets.lock(value_set);

        insert_active_constraint(
            &mut self.constraints,
            &mut self.available_constraints,
            &mut self.queued_constraints,
            Constraint {
                kind: ConstraintKind::Compare { values: [from, to], comparison: id, },
                applied: false,
                // We don't need reasoning for comparisons.... At least for now
                reason: Reason::temp_zero(),
            },
        );

        id
    }

    // @TODO: We should deal with recursive types later on.
    fn map_value_from_other_typesystem_to_this(
        &mut self,
        other: &TypeSystem,
        other_id: ValueId,
        already_converted: &mut Vec<(u32, ValueId)>,
        source_location: Location,
    ) -> ValueId {
        // Check if we've already converted the value
        let value_structure_id = other.values.structure_id_of_value(other_id);
        if let Some(value_structure_id) = value_structure_id {
            for &(from_structure_id, converted_value) in already_converted.iter() {
                if from_structure_id == value_structure_id {
                    return converted_value;
                }
            }
        }

        // We're going to need a new value
        let value_id = self.add_unknown_type();
        if let Some(value_structure_id) = value_structure_id {
            already_converted.push((value_structure_id, value_id));
        }

        let other_value = get_value(&other.structures, &other.values, other_id);
        match other_value.kind {
            Some(Type { kind, args: Some(ref args) }) => {
                let new_args = args.iter()
                    .map(|&v| (
                        self.map_value_from_other_typesystem_to_this(other, v, already_converted, source_location),
                        Reason::temp(source_location),
                    ))
                    .collect::<Vec<_>>();
                self.set_type(value_id, kind.clone(), Args(new_args));
            }
            Some(Type { kind, args: None }) => {
                self.set_type(value_id, kind.clone(), ());
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
        source_location: Location,
    ) {
        let mut already_converted = Vec::new();
        for (this_id, other_id, reason) in to_convert {
            let new_id = self.map_value_from_other_typesystem_to_this(other, other_id, &mut already_converted, source_location);
            self.set_equal(new_id, this_id, reason);
        }
    }

    pub fn set_waiting_on_value_set(&mut self, value_set_id: ValueSetId, waiting_on: crate::typer::WaitingOnTypeInferrence) {
        let value_set = self.value_sets.get_mut(value_set_id);
        debug_assert!(matches!(value_set.waiting_on_completion, crate::typer::WaitingOnTypeInferrence::None), "Cannot use set_on_waiting_on_value_set to override a previous waiter");
        value_set.waiting_on_completion = waiting_on;
    }

    pub fn get(&self, id: ValueId) -> ValueBorrow<'_> {
        get_value(&self.structures, &self.values, id)
    }

    pub fn get_mut(&mut self, id: ValueId) -> ValueBorrowMut<'_> {
        get_value_mut(&mut self.structures, &mut self.values, id)
    }

    pub fn output_incompleteness_errors(&self, errors: &mut ErrorCtx, ast: &crate::parser::Ast) {
        for id in ast.root().iter_all_ids() {
            // @Correctness: This won't generate all incompleteness errors, and will have some duds!
            // We need to fix this for real later on
            let value = get_value(&self.structures, &self.values, ValueId::Node(AstVariantId::root(), id));

            if value.layout.map_or(0, |v| v.align) == 0 {
                errors.error(ast.get(id).loc, format!("Unknown type"));
            }
        }
    }

    pub fn output_errors(&self, errors: &mut ErrorCtx, ast: &crate::parser::Ast) -> bool {
        let mut has_errors = false;
        if self.value_sets.iter().any(|v| v.has_errors) {
            has_errors = true;
        }

        for error in &self.errors {
            has_errors = true;

            match *error {
                Error { a, b, kind: ErrorKind::NonexistantName(name) } => {
                    if let Some(loc) = get_loc_of_value(ast, a) {
                        errors.info(loc, format!(""));
                    } else if let Some(loc) = get_loc_of_value(ast, b) {
                        errors.info(loc, format!(""));
                    }

                    errors.global_error(format!("Field '{}' doesn't exist on `{}`", name, self.value_to_str(b, 0)));
                }
                Error { a, b: _, kind: ErrorKind::PackingNonUnique } => {
                    if let Some(loc) = get_loc_of_value(ast, a) {
                        errors.info(loc, format!("Here"));
                    }
                    errors.global_error(format!("Cannot pack/unpack a `{}`", self.value_to_str(a, 0)));
                }
                Error { a, b, kind: ErrorKind::IncompatibleTypes } => {
                    let a_id = a;
                    let b_id = b;

                    for chain in explain::get_reasons_with_look_inside(a_id, a_id, self, ast) {
                        chain.output(errors, ast, self);
                    }

                    for chain in explain::get_reasons_with_look_inside(a_id, b_id, self, ast) {
                        chain.output(errors, ast, self);
                    }

                    errors.global_error(format!("Incompatible types, `{}` and `{}`", self.value_to_str(a_id, 0), self.value_to_str(b_id, 0)));
                },
                _ => errors.global_error(format!("Temporary type-inference error: {:?}", error)),
            }
        }

        has_errors
    }

    pub fn extract_constant_temp(&self, value_id: ValueId) -> Option<ConstantRef> {
        extract_constant_from_value(&self.structures, &self.values, value_id)
    }

    pub fn value_to_compiler_type(&self, value_id: ValueId) -> types::Type {
        self.value_to_compiler_type_inner(value_id, 0)
    }

    fn value_to_compiler_type_inner(&self, value_id: ValueId, rec: u32) -> types::Type {
        debug_assert!(rec < 60);

        let Some(Type { kind: type_kind, args: Some(type_args) }) = &self.get(value_id).kind else {
            panic!("Cannot call value_to_compiler_type on incomplete value")
        };

        let args: Box<[_]> = type_args.iter().map(|&v| self.value_to_compiler_type_inner(v, rec + 1)).collect();
        types::Type::new_with_args(type_kind.clone(), args)
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

    pub fn set_pack(&mut self, to: ValueId, from: ValueId, unpacking: bool, reason: Reason) {
        insert_active_constraint(
            &mut self.constraints,
            &mut self.available_constraints,
            &mut self.queued_constraints,
            Constraint {
                kind: ConstraintKind::Relation { kind: Relation::Pack { unpacking }, values: [to, from] },
                applied: false,
                reason,
            }
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

    pub fn set_for_relation(&mut self, arg: ValueId, iterator: ValueId, reason: Reason) {
        insert_active_constraint(
            &mut self.constraints,
            &mut self.available_constraints,
            &mut self.queued_constraints,
            Constraint {
                kind: ConstraintKind::Relation { kind: Relation::ForIterator { by_reference: false }, values: [iterator, arg] },
                applied: false,
                reason,
            }
        );
    }

    pub fn set_equal(&mut self, a: ValueId, b: ValueId, reason: Reason) {
        if a == b {
            return;
        }
        insert_active_constraint(
            &mut self.constraints,
            &mut self.available_constraints,
            &mut self.queued_constraints,
            Constraint::equal(a, b, None, reason),
        );
    }

    pub fn set_constant_field(
        &mut self,
        a: ValueId,
        field_name: Ustr,
        b: ValueId,
        reason: Reason,
    ) {
        insert_active_constraint(
            &mut self.constraints,
            &mut self.available_constraints,
            &mut self.queued_constraints,
            Constraint {
                kind: ConstraintKind::Relation {
                    kind: Relation::NamedConstField(field_name),
                    values: [a, b],
                },
                reason,
                applied: false,
            },
        );
    }

    pub fn set_field_name_equal(
        &mut self,
        a: ValueId,
        field_name: Ustr,
        b: ValueId,
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
                    hidden_subdivisions: 0,
                },
                reason,
                applied: false,
            },
        );
    }

    pub fn solve(&mut self) {
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
            compute_size(&mut self.structures, &mut self.values, &mut self.computable_value_sizes, computable_size);
        }

        // self.print_state();

        // let count = self.values.structure.iter().filter(|v| v.num_values > 0).count();
        // let length = self.values.structure.len();
        // println!("Conversion ratio: {}, {}, {:.4}", count, length, count as f64 / length as f64);
    }

    fn constant_to_str(&self, type_: ValueId, value: ConstantRef, rec: usize) -> String {
        match &self.get(type_).kind {
            Some(Type { kind: TypeKind::IntSize(size), .. }) => {
                match size {
                    0 => "ptr".to_string(),
                    1 => "1".to_string(),
                    2 => "2".to_string(),
                    4 => "4".to_string(),
                    8 => "8".to_string(),
                    num => format!("<invalid int size value {}>", num),
                }
            }
            Some(Type { kind: TypeKind::IntSigned(signed), .. }) => {
                format!("{}", signed)
            }
            Some(Type { kind: TypeKind::Int, args: Some(c) }) => {
                let [signed, size] = &**c else { panic!() };

                let Some(&Type { kind: TypeKind::IntSigned(signed), .. }) = self.get(*signed).kind else { panic!() };
                let Some(&Type { kind: TypeKind::IntSize(size), .. }) = self.get(*size).kind else { panic!() };

                let size = match size {
                    0 => 8,
                    1 => 1,
                    2 => 2,
                    4 => 4,
                    8 => 8,
                    _ => unreachable!("Invalid int size"),
                };

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
        let kind = self.get(value).kind;
        let inner = match kind {
            Some(&Type { kind: TypeKind::Target { min: value, .. }, .. }) => {
                if value == crate::typer::TARGET_ALL {
                    "All".to_string()
                } else if value == 0 {
                    "None".to_string()
                } else {
                    let values = [
                        ((value & crate::typer::TARGET_COMPILER) > 0).then(|| "Compiler"),
                        ((value & crate::typer::TARGET_NATIVE) > 0).then(|| "Native"),
                    ];

                    let mut output = String::new();
                    for (i, name) in values.into_iter().flatten().enumerate() {
                        if i > 0 { output.push_str(" | "); }
                        output.push_str(name);
                    }
                    output
                }
            }
            Some(Type { kind: TypeKind::CompareUnspecified, .. }) => "_(intentionally unspecified)".to_string(),
            Some(Type { kind: TypeKind::Bool, .. }) => "bool".to_string(),
            Some(Type { kind: TypeKind::Empty, .. }) => "Empty".to_string(),
            Some(Type { kind: TypeKind::IntSize(s), .. }) => format!("size {}", s),
            Some(Type { kind: TypeKind::IntSigned(s), .. }) => format!("int sign {}", s),
            Some(Type { kind: TypeKind::ConstantValue(_), .. }) => "<constant value>".to_string(),
            None => "_".to_string(),
            Some(Type { kind: TypeKind::Any { marker, .. }, args: _ }) => {
                // TODO: We want to print the generic parameters too, somehow.
                if let Some(name) = marker.name {
                    name.to_string()
                } else {
                    format!("<anonymous {}>", marker.loc)
                }
            }
            Some(Type { kind: TypeKind::MonomorphedRuntimeGeneric { id, number }, args: _ }) => {
                format!("<monomorphed {}.{}>", id, number)
            }
            Some(Type { kind: TypeKind::RuntimeGeneric { id, number }, args: _ }) => {
                // TODO: We want to print the generic parameters too, somehow.
                if let Some(name) = id.name {
                    format!("arg {} of {}", number, name)
                } else {
                    format!("arg {} of <anonymous {}>", number, id.loc)
                }
            }
            Some(Type { kind: TypeKind::Unique(marker), args: _ }) => {
                // TODO: We want to print the generic parameters too, somehow.
                if let Some(name) = marker.name {
                    name.to_string()
                } else {
                    format!("<anonymous {}>", marker.loc)
                }
            }
            Some(Type { kind: TypeKind::Constant, args: Some(c) }) => match &**c {
                [type_, value] => {
                    let value = match &self.get(*value).kind {
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
            Some(Type { kind: TypeKind::Float, args: Some(c) }) => match &**c {
                [size] => {
                    if let Some(&Type { kind: TypeKind::IntSize(size), .. }) = self.get(*size).kind {
                        match size {
                            4 => "f32",
                            8 => "f64",
                            _ => "<float with invalid size>",
                        }.to_string()
                    } else {
                        format!(
                            "Float({})",
                            self.value_to_str(*size, rec + 1),
                        )
                    }
                },
                _ => unreachable!("A float type has no children"),
            }
            Some(Type { kind: TypeKind::Int, args: Some(c) }) => match &**c {
                [signed, size] => {
                    if let (Some(&Type { kind: TypeKind::IntSigned(sign), .. }), Some(&Type { kind: TypeKind::IntSize(size), .. })) = (self.get(*signed).kind, self.get(*size).kind) {
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
                _ => unreachable!("An int type has no children"),
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
            Some(Type { kind: TypeKind::Tuple, args: Some(c), .. }) => {
                let list = c
                    .iter()
                    .map(|type_| {
                        format!("{}", self.value_to_str(*type_, rec + 1))
                    })
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("({})", list)
            }
            Some(Type { kind: TypeKind::Enum(marker, _), args: Some(_), .. }) => {
                if let Some(name) = marker.name {
                    format!("{}", name)
                } else {
                    format!("<anonymous {}>", marker.loc)
                }
            }
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
        };

        inner
    }

    fn constraint_to_string(&self, constraint: &Constraint) -> String {
        match constraint.kind {
            ConstraintKind::RequireSize { value_id, value_set_id } => {
                format!("{:?} requires size of {}", value_set_id, self.value_to_str(value_id, 0))
            }
            ConstraintKind::DynMonomorph { values: [a, b], .. } => {
                format!("{} monomorphed from {}", self.value_to_str(a, 0), self.value_to_str(b, 0))
            }
            ConstraintKind::Compare { values: [a, b], .. } => {
                format!("{} is {}?", self.value_to_str(a, 0), self.value_to_str(b, 0))
            }
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
                creator: _,
            } => {
                format!(
                    "{:?}({}) == {:?}({})",
                    a_id,
                    self.value_to_str(a_id, 0),
                    b_id,
                    self.value_to_str(b_id, 0)
                )
            }
            ConstraintKind::EqualsField {
                values: [a_id, b_id],
                index: field_index,
            } => {
                format!(
                    "{:?}({}).{} == {:?}({})",
                    a_id,
                    self.value_to_str(a_id, 0),
                    field_index,
                    b_id,
                    self.value_to_str(b_id, 0)
                )
            }
            ConstraintKind::EqualNamedField {
                values: [a_id, b_id],
                index: field_name,
                hidden_subdivisions: _,
            } => {
                format!(
                    "{:?}({}).{} == {:?}({})",
                    a_id,
                    self.value_to_str(a_id, 0),
                    field_name,
                    b_id,
                    self.value_to_str(b_id, 0)
                )
            }
        }
    }

    pub fn print_state(&self) {
        println!("Queued constraints:");
        for &constraint_id in &self.queued_constraints {
            let constraint = &self.constraints[constraint_id];
            println!("({}) {}", constraint_id, self.constraint_to_string(constraint));
        }
        println!();
    }

    fn apply_constraint(&mut self, constraint_id: ConstraintId) {
        let constraint = self.constraints[constraint_id];
        if constraint.applied { return; }

        match constraint.kind {
            ConstraintKind::RequireSize { value_set_id, value_id } => {
                let value = get_value(&self.structures, &self.values, value_id);

                if let Some(type_) = value.kind {
                    if let Some(ref args) = type_.args {
                        if DEBUG {
                            println!("Recursive sizes!");
                        }

                        for &arg in args.iter() {
                            if insert_active_constraint(
                                &mut self.constraints,
                                &mut self.available_constraints,
                                &mut self.queued_constraints,
                                Constraint {
                                    kind: ConstraintKind::RequireSize { value_set_id, value_id: arg },
                                    applied: false,
                                    reason: constraint.reason,
                                }
                            ) {
                                self.value_sets.lock(value_set_id);
                            }
                        }

                        self.value_sets.unlock(value_set_id);

                        self.constraints[constraint_id].applied = true;
                    }
                }
            }
            ConstraintKind::Relation { kind, values: [to_id, from_id] } => {
                let to = get_value(&self.structures, &self.values, to_id);
                let from = get_value(&self.structures, &self.values, from_id);

                match (kind, to.kind, from.kind) {
                    (
                        Relation::Pack { .. },
                        Some(Type { kind: TypeKind::Unique(_), args: Some(to_args) }),
                        _,
                    ) => {
                        let to_arg = to_args[0];
                        self.set_equal(to_arg, from_id, constraint.reason);
                    }
                    (
                        Relation::Pack { .. },
                        Some(Type { kind: TypeKind::Enum { .. }, args: Some(args) }),
                        _,
                    ) => {
                        let to_arg = args[0];
                        self.set_equal(to_arg, from_id, constraint.reason);
                    }
                    (
                        Relation::Pack { unpacking, .. },
                        Some(&Type { kind: TypeKind::Any { marker, num_args }, args: Some(ref args) }),
                        _,
                    ) => {
                        let to_arg = args[0];

                        let monomorph_id = self.monomorphs.len() as u32;
                        let arg_types = (0..num_args).map(|number| {
                            if unpacking {
                                self.add_type(TypeKind::MonomorphedRuntimeGeneric { id: monomorph_id, number }, Args([]))
                            } else {
                                self.add_unknown_type()
                            }
                        }).collect();
                        self.monomorphs.push(Monomorph {
                            arg_types,
                        });

                        insert_active_constraint(
                            &mut self.constraints,
                            &mut self.available_constraints,
                            &mut self.queued_constraints,
                            Constraint {
                                kind: ConstraintKind::DynMonomorph {
                                    values: [to_arg, from_id],
                                    monomorph_id,
                                    marker,
                                },
                                applied: false,
                                reason: constraint.reason,
                            }
                        );
                    }
                    (
                        Relation::Pack { .. },
                        Some(Type { kind: _, args: _ }),
                        _,
                    ) => {
                        self.errors.push(Error {
                            a: to_id,
                            b: from_id,
                            kind: ErrorKind::PackingNonUnique,
                        });
                        self.constraints[constraint_id].applied = true;
                        self.make_erroneous(to_id);
                        self.make_erroneous(from_id);
                        return;
                    }
                    (
                        Relation::NamedConstField(name),
                        _,
                        Some(Type { kind: TypeKind::Enum(_, field_names), args: Some(args) }),
                    ) => {
                        if let Some(index) = field_names.iter().position(|v| *v == name) {
                            let from_arg = args[index + 1];
                            self.set_equal(to_id, from_arg, constraint.reason);
                        } else {
                            self.errors.push(Error {
                                a: to_id,
                                b: from_id,
                                kind: ErrorKind::NonexistantName(name),
                            });
                            self.constraints[constraint_id].applied = true;
                            self.make_erroneous(to_id);
                            self.make_erroneous(from_id);
                            return;
                        }
                    }
                    (
                        Relation::InnerConstant,
                        _,
                        Some(Type { kind: TypeKind::Constant, args: Some(args) }),
                    ) => {
                        let inner = args[1];
                        self.set_equal(to_id, inner, constraint.reason);
                    }
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
                        let int_t = self.add_type(TypeKind::Int, ());
                        self.set_equal(from_id, int_t, constraint.reason);
                    }
                    (
                        Relation::Cast,
                        None,
                        Some(Type { kind: TypeKind::Int, args: _ }),
                    ) => {
                        let int_t = self.add_type(TypeKind::Int, ());
                        self.set_equal(to_id, int_t, constraint.reason);
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
                        self.set_equal(a, b, constraint.reason);
                    }
                    (
                        Relation::ForIterator { by_reference: _ },
                        Some(Type { kind: TypeKind::Buffer | TypeKind::Array, args: Some(to_args) }),
                        _,
                    ) => {
                        let inner = to_args[0];
                        self.set_equal(inner, from_id, constraint.reason);
                    }
                    (
                        Relation::ForIterator { by_reference: false },
                        Some(Type { kind: TypeKind::Reference, args: Some(to_args) }),
                        _,
                    ) => {
                        let inner = to_args[0];

                        let to_inner = self.add_unknown_type();

                        insert_active_constraint(
                            &mut self.constraints,
                            &mut self.available_constraints,
                            &mut self.queued_constraints,
                            Constraint {
                                kind: ConstraintKind::Relation { kind: Relation::ForIterator { by_reference: true }, values: [inner, to_inner] },
                                applied: false,
                                reason: constraint.reason,
                            },
                        );

                        let to = self.add_type(TypeKind::Reference, Args([(to_inner, Reason::temp_zero())]));
                        self.set_equal(from_id, to, constraint.reason);
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
                let a = get_value(&self.structures, &self.values, a_id);
                let b = get_value(&self.structures, &self.values, b_id);
                let result = get_value(&self.structures, &self.values, result_id);

                let (a, b, result) = (&a.kind, &b.kind, &result.kind);

                match (op, (a.as_ref().map(|v| &v.kind), b.as_ref().map(|v| &v.kind), result.as_ref().map(|v| &v.kind))) {
                    (
                        BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mult | BinaryOp::Div | BinaryOp::BitAnd | BinaryOp::BitOr | BinaryOp::ShiftLeft | BinaryOp::ShiftRight | BinaryOp::Modulo,
                        (Some(TypeKind::Int), Some(TypeKind::Int), _),
                    ) => {
                        self.set_equal(a_id, b_id, constraint.reason);
                        self.set_equal(a_id, result_id, constraint.reason);
                    }
                    (
                        BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mult | BinaryOp::Div | BinaryOp::Modulo,
                        (Some(TypeKind::Float), Some(TypeKind::Float), _),
                    ) => {
                        self.set_equal(a_id, b_id, constraint.reason);
                        self.set_equal(a_id, result_id, constraint.reason);
                    }
                    (
                        BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mult | BinaryOp::Div | BinaryOp::BitAnd | BinaryOp::BitOr,
                        (Some(TypeKind::Reference), Some(TypeKind::Int), Some(TypeKind::Reference)),
                    ) => {
                        // No reason given for why the type is a usize....
                        let usize = self.add_int(IntTypeKind::Usize);
                        self.set_equal(usize, b_id, constraint.reason);
                        self.set_equal(a_id, result_id, constraint.reason);
                    }
                    (
                        BinaryOp::And | BinaryOp::Or,
                        (_, _, _),
                    ) => {
                        // Temporary: No type validation, just equality :)
                        let bool = self.add_type(TypeKind::Bool, Args([]));
                        self.set_equal(bool, a_id, constraint.reason);
                        self.set_equal(bool, b_id, constraint.reason);
                        self.set_equal(bool, result_id, constraint.reason);
                    }
                    (
                        BinaryOp::BitOr,
                        (Some(TypeKind::Enum(_, _)), Some(TypeKind::Enum(_, _)), _) |
                        (_, _, Some(TypeKind::Enum(_, _))),
                    ) => {
                        // TODO: Type validation!!
                        self.set_equal(a_id, b_id, constraint.reason);
                        self.set_equal(a_id, result_id, constraint.reason);
                    }
                    (
                        BinaryOp::BitAnd,
                        (Some(TypeKind::Enum(_, _)), Some(TypeKind::Enum(_, _)), Some(TypeKind::Bool)),
                    ) => {
                        self.set_equal(a_id, b_id, constraint.reason);

                        let bool = self.add_type(TypeKind::Bool, Args([]));
                        self.set_equal(bool, result_id, constraint.reason);
                    }
                    (
                        BinaryOp::BitAnd,
                        (Some(TypeKind::Enum(_, _)), Some(TypeKind::Enum(_, _)), Some(TypeKind::Enum(_, _))) |
                        (_, _, Some(TypeKind::Enum(_, _))),
                    ) => {
                        // TODO: Type validation!!
                        self.set_equal(a_id, b_id, constraint.reason);
                        self.set_equal(a_id, result_id, constraint.reason);
                    }
                    (
                        BinaryOp::Equals | BinaryOp::NotEquals | BinaryOp::LargerThanEquals | BinaryOp::LargerThan | BinaryOp::LessThanEquals | BinaryOp::LessThan,
                        (Some(TypeKind::Enum(a_marker, _)), Some(TypeKind::Enum(b_marker, _)), _),
                    ) if a_marker == b_marker => {
                        if let (Some(Some(args_a)), Some(Some(args_b))) = (a.as_ref().map(|v| v.args.as_ref()), b.as_ref().map(|v| v.args.as_ref())) {
                            let inner_a = args_a[0];
                            let inner_b = args_b[0];
                            self.set_op_equal(op, inner_a, inner_b, result_id, constraint.reason);
                        } else {
                            return;
                        }
                    }
                    (
                        BinaryOp::Equals | BinaryOp::NotEquals | BinaryOp::LargerThanEquals | BinaryOp::LargerThan | BinaryOp::LessThanEquals | BinaryOp::LessThan,
                        (Some(TypeKind::Unique(a_marker)), Some(TypeKind::Unique(b_marker)), _),
                    ) if a_marker == b_marker => {
                        if let (Some(Some(args_a)), Some(Some(args_b))) = (a.as_ref().map(|v| v.args.as_ref()), b.as_ref().map(|v| v.args.as_ref())) {
                            let inner_a = args_a[0];
                            let inner_b = args_b[0];
                            self.set_op_equal(op, inner_a, inner_b, result_id, constraint.reason);
                        } else {
                            return;
                        }
                    }
                    (
                        BinaryOp::Equals | BinaryOp::NotEquals | BinaryOp::LargerThanEquals | BinaryOp::LargerThan | BinaryOp::LessThanEquals | BinaryOp::LessThan,
                        (Some(TypeKind::Int), Some(TypeKind::Int), _) | (Some(TypeKind::Reference), Some(TypeKind::Reference), _) | (Some(TypeKind::Bool), Some(TypeKind::Bool), _) | (Some(TypeKind::Float), Some(TypeKind::Float), _)
                    ) => {
                        let id = self.add_type(TypeKind::Bool, Args([]));

                        self.set_equal(result_id, id, constraint.reason);
                        self.set_equal(a_id, b_id, constraint.reason);
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
                hidden_subdivisions,
            } => {
                let a = get_value(&self.structures, &self.values, a_id);

                match &a.kind {
                    None => return,
                    Some(Type { kind: TypeKind::Unique(_), args, .. }) => {
                        // TODO: This could cause infinite recursion...
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
                                        hidden_subdivisions,
                                    },
                                    reason,
                                    applied: false,
                                },
                            );
                            self.constraints[constraint_id].applied = true;
                        }
                    }
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

                                    let new_value_id = add_value(
                                        &mut self.structures,
                                        &mut self.values,
                                        Some(Type {
                                            kind: TypeKind::Reference,
                                            args: Some(Box::new([pointee])),
                                        }),
                                    );

                                    self.set_equal(new_value_id, b_id, constraint.reason);
                                }
                            }
                            "len" => {
                                let usize_type = self.add_int(IntTypeKind::Usize);
                                self.set_equal(usize_type, b_id, constraint.reason);

                                self.constraints[constraint_id].applied = true;
                            }
                            _ => {
                                self.errors.push(Error::new(
                                    a_id,
                                    b_id,
                                    ErrorKind::NonexistantName(field_name),
                                ));
                                self.make_erroneous(a_id);
                                self.make_erroneous(b_id);
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
                            self.make_erroneous(a_id);
                            self.make_erroneous(b_id);
                            return;
                        }
                    }
                    Some(Type { kind: TypeKind::Tuple, .. }) => {
                        if let Some(number) = field_name.strip_prefix("_").and_then(|v| v.parse::<usize>().ok()) {
                            let reason = constraint.reason;
                            insert_active_constraint(
                                &mut self.constraints,
                                &mut self.available_constraints,
                                &mut self.queued_constraints,
                                Constraint {
                                    kind: ConstraintKind::EqualsField {
                                        values: [a_id, b_id],
                                        index: number,
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
                            self.make_erroneous(a_id);
                            self.make_erroneous(b_id);
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
                            self.make_erroneous(a_id);
                            self.make_erroneous(b_id);
                            return;
                        }
                    }
                    Some(_) => {
                        self.errors.push(Error::new(
                            a_id,
                            b_id,
                            ErrorKind::NonexistantName(field_name),
                        ));
                        self.make_erroneous(a_id);
                        self.make_erroneous(b_id);
                        return;
                    }
                }

                self.constraints[constraint_id].applied |= true;
            }
            ConstraintKind::EqualsField {
                values: [a_id, b_id],
                index: field_index,
            } => {
                let a = &get_value(&self.structures, &self.values, a_id).kind;

                match a {
                    None | Some(Type { args: None, .. }) => {}
                    Some(Type { args: Some(fields), .. }) => {
                        if let Some(&field) = fields.get(field_index) {
                            let loc = constraint.reason.loc;
                            insert_active_constraint(
                                &mut self.constraints,
                                &mut self.available_constraints,
                                &mut self.queued_constraints,
                                Constraint::equal(field, b_id, Some(constraint_id), Reason::new(loc, ReasonKind::Ignore)),
                            );
                        } else {
                            self.errors.push(Error::new(
                                a_id,
                                b_id,
                                ErrorKind::IndexOutOfBounds(field_index),
                            ));
                            self.make_erroneous(a_id);
                            self.make_erroneous(b_id);
                            return;
                        }

                        self.constraints[constraint_id].applied |= true;
                    }
                }
            }
            ConstraintKind::DynMonomorph {
                values: [a_id, b_id],
                marker,
                monomorph_id,
            } => {
                let a_value = get_value(&self.structures, &self.values, a_id);

                let Some(a_type) = a_value.kind else { return };

                if let TypeKind::RuntimeGeneric { id, number } = a_type.kind {
                    if id == marker {
                        self.constraints[constraint_id].applied = true;

                        let monomorph = &self.monomorphs[monomorph_id as usize];
                        let new_type = monomorph.arg_types[number as usize];

                        self.set_equal(b_id, new_type, constraint.reason);
                        return;
                    }
                }

                let Some(a_args) = &a_type.args else { return };

                let a_kind = a_type.kind.clone();
                // TODO: Performance!
                let a_args = a_args.to_vec();

                let mut b_args = Vec::with_capacity(a_args.len());
                for &a_arg in a_args.iter() {
                    let b_arg = self.add_unknown_type();
                    b_args.push((b_arg, Reason::temp_zero()));
                    insert_active_constraint(
                        &mut self.constraints,
                        &mut self.available_constraints,
                        &mut self.queued_constraints,
                        Constraint {
                            kind: ConstraintKind::DynMonomorph { values: [a_arg, b_arg], marker, monomorph_id },
                            applied: false,
                            reason: constraint.reason,
                        },
                    );
                }

                let b_reference_id = self.add_type(a_kind, Args(b_args));
                self.set_equal(b_id, b_reference_id, Reason::temp_zero());

                self.constraints[constraint_id].applied = true;
            }
            ConstraintKind::Compare {
                values: [a_id, b_id],
                comparison,
            } => {
                let a_value = get_value(&self.structures, &self.values, a_id);
                let b_value = get_value(&self.structures, &self.values, b_id);

                let (Some(a_type), Some(b_type)) = (a_value.kind, b_value.kind) else { return };

                if let TypeKind::CompareUnspecified = b_type.kind {
                    self.constraints[constraint_id].applied = true;
                    self.resolve_comparison(comparison, true);
                    return;
                }

                if a_type.kind != b_type.kind {
                    self.constraints[constraint_id].applied = true;
                    self.resolve_comparison(comparison, false);
                    return;
                }

                let (Some(a_args), Some(b_args)) = (&a_type.args, &b_type.args) else { return };

                if a_args.len() != b_args.len() {
                    self.constraints[constraint_id].applied = true;
                    self.resolve_comparison(comparison, false);
                    return;
                }

                for (&a_arg, &b_arg) in a_args.iter().zip(b_args.iter()) {
                    self.comparisons[comparison].left_to_do += 1;
                    insert_active_constraint(
                        &mut self.constraints,
                        &mut self.available_constraints,
                        &mut self.queued_constraints,
                        Constraint {
                            kind: ConstraintKind::Compare { values: [a_arg, b_arg], comparison, },
                            applied: false,
                            // We don't need reasoning for comparisons.... At least for now
                            reason: Reason::temp_zero(),
                        },
                    );
                }

                self.constraints[constraint_id].applied = true;
                self.resolve_comparison(comparison, true);
            }
            ConstraintKind::Equal {
                values: [a_id, b_id],
                creator: _,
            } => {
                let a_value = get_value(&self.structures, &self.values, a_id);
                let b_value = get_value(&self.structures, &self.values, b_id);

                // @Slight hack: If they have the same _pointer_ to a kind, they are the same structure, and therefore, we
                // should not apply this constraint.
                if let (Some(a_struct_id), Some(b_struct_id)) = (a_value.structure_id, b_value.structure_id) {
                    if a_struct_id == b_struct_id {
                        return;
                    }
                }

                let a = a_value.kind;
                let b = b_value.kind;
                let (to, from) = match (a, b) {
                    (None, None) => (a_id, b_id),
                    (None, Some(_)) => (b_id, a_id),
                    (Some(_), None) => (a_id, b_id),
                    (Some(a_type), Some(b_type)) => {
                        if a_type.kind != b_type.kind {
                            self.errors.push(Error { a: a_id, b: b_id, kind: ErrorKind::IncompatibleTypes });
                            self.constraints[constraint_id].applied = true;
                            self.make_erroneous(a_id);
                            self.make_erroneous(b_id);
                            return;
                        } else {
                            match (&a_type.args, &b_type.args) {
                                (None, None) => (a_id, b_id),
                                (None, Some(_)) => (b_id, a_id),
                                (Some(_), None) => (a_id, b_id),
                                (Some(a_args), Some(b_args)) => {
                                    if a_args.len() != b_args.len() {
                                        self.errors.push(Error { a: a_id, b: b_id, kind: ErrorKind::IncompatibleTypes });
                                        self.constraints[constraint_id].applied = true;
                                        self.make_erroneous(a_id);
                                        self.make_erroneous(b_id);
                                        return;
                                    } else {
                                        for (a_arg, b_arg) in a_args.iter().zip(b_args.iter()) {
                                            let loc = self.constraints[constraint_id].reason.loc;
                                            insert_active_constraint(
                                                &mut self.constraints,
                                                &mut self.available_constraints,
                                                &mut self.queued_constraints,
                                                Constraint::equal(*a_arg, *b_arg, Some(constraint_id), Reason::new(loc, ReasonKind::Ignore)),
                                            );
                                        }
                                    }

                                    if get_value(&self.structures, &self.values, b_id).layout.map_or(false, |v| v.align > 0) {
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
                for id in iter_values_in_structure(&self.structures, &self.values, from) {
                    self.queued_constraints.extend(
                        self.available_constraints
                            .get(&id)
                            .iter()
                            .flat_map(|v| v.iter())
                            .copied()
                            .filter(|v| v != &constraint_id),
                    );
                }

                structurally_combine(&mut self.structures, &mut self.values, &mut self.computable_value_sizes, to, from);
            }
        }
    }

    pub fn make_erroneous(&mut self, _id: ValueId) {
        /* TODO
        let value = self.values.get(id);
        self.value_sets.make_erroneous(&value.value.value_sets);
        */
    }

    /// Adds a value set to a value. This value has to be an unknown type, otherwise it will panic
    /// in debug mode. It also cannot be an alias. This is solely intended for use by the building
    /// process of the typer.
    pub fn set_value_set(&mut self, value_id: ValueId, value_set_id: ValueSetId) {
        if insert_active_constraint(
            &mut self.constraints,
            &mut self.available_constraints,
            &mut self.queued_constraints,
            Constraint {
                kind: ConstraintKind::RequireSize { value_id, value_set_id },
                applied: false,
                reason: Reason::temp_zero(),
            },
        ) {
            self.value_sets.lock(value_set_id);
        }
    }

    pub fn add_unknown_type_with_set(&mut self, set: ValueSetId) -> ValueId {
        let type_ = self.add_unknown_type();
        self.set_value_set(type_, set);
        type_
    }

    pub fn set_compiler_type(&mut self, program: &Program, id: ValueId, type_: &types::Type) -> ValueId {
        let args: Vec<_> = type_.args().iter().map(|v| (self.add_compiler_type(program, v), Reason::temp_zero())).collect();
        self.set_type(id, type_.kind().clone(), Args(args))
    }

    pub fn add_compiler_type(&mut self, program: &Program, type_: &types::Type) -> ValueId {
        let id = self.add_unknown_type();
        self.set_compiler_type(program, id, type_)
    }

    pub fn set_type(&mut self, value_id: ValueId, kind: TypeKind, args: impl IntoValueArgs) -> ValueId {
        let args = args
            .into_value_args()
            .map(|v|
                v.into_iter().enumerate().map(|(index, (v, reason))| {
                    insert_constraint(
                        &mut self.constraints,
                        &mut self.available_constraints,
                        Constraint {
                            kind: ConstraintKind::EqualsField { values: [value_id, v], index, },
                            reason,
                            // It's not actually applied, but because we already have it as an argument, it never needs to be applied.
                            applied: true,
                        },
                    );
                    v
                })
                .collect()
            );
        set_value(&mut self.structures, &mut self.values, value_id, Type { kind, args });
        *get_value_mut(&mut self.structures, &mut self.values, value_id).is_base_value = true;

        value_id
    }

    pub fn add_int(&mut self, int_kind: IntTypeKind) -> ValueId {
        let id = self.add_unknown_type();
        self.set_int(id, int_kind);
        id
    }

    // @Speed: This creates a temporary, but is also a kind of temporary value itself....
    pub fn set_int(&mut self, value_id: ValueId, int_kind: IntTypeKind) {
        let (signed, size) = match int_kind {
            IntTypeKind::U8    => (false, 1),
            IntTypeKind::U16   => (false, 2),
            IntTypeKind::U32   => (false, 4),
            IntTypeKind::U64   => (false, 8),
            IntTypeKind::Usize => (false, 0),
            IntTypeKind::I8    => (true,  1),
            IntTypeKind::I16   => (true,  2),
            IntTypeKind::I32   => (true,  4),
            IntTypeKind::I64   => (true,  8),
            IntTypeKind::Isize => (true,  0),
        };

        let size = self.add_type(TypeKind::IntSize(size), Args([]));
        let sign = self.add_type(TypeKind::IntSigned(signed), Args([]));

        self.set_type(value_id, TypeKind::Int, Args([(sign, Reason::temp_zero()), (size, Reason::temp_zero())]));
    }

    pub fn add_type(&mut self, kind: TypeKind, args: impl IntoValueArgs) -> ValueId {
        let value_id = self.add_unknown_type();
        self.set_type(value_id, kind, args);
        value_id
    }

    pub fn add_unknown_type(&mut self) -> ValueId {
        add_value(
            &mut self.structures,
            &mut self.values,
            None,
        )
    }

    pub fn set_value(&mut self, value_id: ValueId, type_: ValueId, value: impl IntoConstant) {
        let value = value.into_constant();
        let constant_value_id = add_value(
            &mut self.structures,
            &mut self.values,
            value.map(|v| Type {
                kind: TypeKind::ConstantValue(v),
                args: Some(Box::new([])),
            }),
        );
        *get_value_mut(&mut self.structures, &mut self.values, constant_value_id).is_base_value = true;
        self.set_type(value_id, TypeKind::Constant, Args([(type_, Reason::temp_zero()), (constant_value_id, Reason::temp_zero())]));
    }

    pub fn add_value(&mut self, type_: ValueId, value: impl IntoConstant) -> ValueId {
        let type_id = self.add_unknown_type();
        self.set_value(type_id, type_, value);
        type_id
    }
}

#[derive(Debug, Clone, Copy)]
pub struct MemberInfo {
    pub name: Ustr,
    pub index: usize,
    pub offset: usize,
    pub layout: Layout,
}
