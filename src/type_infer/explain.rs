use super::{TypeSystem, ConstraintId, ValueId, ConstraintKind};
use crate::location::Location;
use std::collections::{hash_map, HashMap};
use crate::errors::ErrorCtx;
use crate::program::PolyMemberId;
use crate::parser::Ast;
use crate::type_infer;
use ustr::Ustr;

pub fn get_reasons(base_value: ValueId, types: &TypeSystem, ast: &crate::parser::Ast) -> Vec<ReasoningChain> {
    get_reasons_with_look_inside(base_value, base_value, types, ast)
}

pub fn get_reasons_with_look_inside(base_value: ValueId, look_inside: ValueId, types: &TypeSystem, ast: &crate::parser::Ast) -> Vec<ReasoningChain> {
    #[derive(Debug, Default)]
    struct Node {
        source: Option<(ValueId, Vec<usize>)>,
        reason: Option<Reason>,
        distance: u32,
    }

    struct Frontier {
        source: (ValueId, Vec<usize>),
        distance: u32,
        constraint_id: ConstraintId,
    }

    fn reason_from_values(system: &TypeSystem, base_value: ValueId, look_inside: ValueId, mut graph: HashMap<(ValueId, Vec<usize>), Node>, mut frontier: Vec<Frontier>) -> ReasoningChain {
        'path_loop: loop {
            let Some((index, _)) = frontier.iter().enumerate().min_by_key(|(_, v)| v.distance) else { panic!("Exited too early I think") };
            let Frontier { source, distance, constraint_id } = frontier.swap_remove(index);

            if source.0.is_static_value() {
                continue;
            }

            let constraint = &system.constraints[constraint_id];
            
            // We only deal with these two kinds of constraints
            let values = match constraint.kind {
                ConstraintKind::EqualsField { values, .. } => { values }
                ConstraintKind::Equal { values, .. } => { values }
                _ => continue,
            };

            for (i, value_id) in values.into_iter().enumerate() {
                if value_id == source.0 { continue; }

                let mut reason = constraint.reason;
                if reason.kind == ReasonKind::Ignore { continue; }
                reason.forward ^= i > 0;

                let new_node = Node {
                    source: Some(source.clone()),
                    distance,
                    reason: Some(reason),
                };

                let mut new_source = (value_id, source.1.clone());
                match constraint.kind {
                    ConstraintKind::EqualsField { index, .. } => if i == 0 {
                        new_source.1.push(index);
                    } else {
                        let Some(old_index) = new_source.1.pop() else { continue };
                        // We can't use this constraint to explain things.
                        if old_index != index { continue; }
                    }
                    _ => {}
                }

                let progress = match graph.entry(new_source.clone()) {
                    hash_map::Entry::Occupied(_) => {
                        false
                    }
                    hash_map::Entry::Vacant(entry) => {
                        entry.insert(new_node);
                        true
                    }
                };

                if value_id == base_value && new_source.1.is_empty() {
                    break 'path_loop;
                }

                if progress {
                    if let Some(constraints) = system.available_constraints.get(&value_id) {
                        frontier.extend(constraints.iter().map(|&constraint_id| Frontier {
                            source: new_source.clone(),
                            distance: distance + system.constraints[constraint_id].reason.kind.weight(),
                            constraint_id,
                        }));
                    }
                }
            }
        }

        debug_assert!(graph.contains_key(&(base_value, Vec::new())));

        let distance = graph[&(base_value, Vec::new())].distance;

        let mut chain = Vec::new();
        let mut next = &Some((base_value, Vec::new()));
        let mut i = 0;
        while let Some(value_id) = next {
            i = i + 1;
            if i > 500 { break; }
            let node = &graph[value_id];
            if let Some(reason) = node.reason {
                if reason.kind != ReasonKind::Passed {
                    chain.push(reason);
                }
            }
            next = &node.source;
        }

        ReasoningChain {
            explaining: look_inside,
            distance,
            chain,
        }
    }

    let mut best_reason: Option<ReasoningChain> = None;

    for value_id in type_infer::iter_values_in_structure(&types.structures, &types.values, look_inside) {
        if *types.get(value_id).is_base_value {
            let mut graph = HashMap::new();
            let mut frontier = Vec::new();
            // It's a base value, which means that we can draw a chain of reasoning from it.
            let node = Node {
                source: None,
                reason: match value_id {
                    ValueId::Node(id) => Some(crate::typer::explain_given_type(ast, id)),
                    _ => None,
                },
                distance: 0,
            };

            graph.insert((value_id, Vec::new()), node);

            if let Some(constraints) = types.available_constraints.get(&value_id) {
                frontier.extend(constraints.iter().map(|&constraint_id| Frontier {
                    source: (value_id, Vec::new()),
                    distance: 1,
                    constraint_id,
                }));

                let new_reason = reason_from_values(types, base_value, look_inside, graph, frontier);
                if let Some(ref best_reason) = best_reason {
                    if best_reason.distance < new_reason.distance { continue; }
                }
                best_reason = Some(new_reason);
            }
        }
    }
    
    best_reason.into_iter().collect()
}

#[derive(Clone, Copy)]
enum ExpressionKind {
    Used,
}

struct Explanation {
    loc: Location,
    message: String,
    kind: ExpressionKind,
    next: Option<Box<Explanation>>,
}

impl Explanation {
    fn new(loc: Location, kind: ExpressionKind, message: impl Into<String>) -> Self {
        Self {
            loc,
            message: message.into(),
            kind,
            next: None,
        }
    }
}

fn get_concise_explanation(errors: &mut ErrorCtx, ast: &Ast, chain: &[Reason]) -> Explanation {
    let mut needs_break = false;

    let (explanation, rest) : (_, &[_]) = match chain {
        //
        // -- Function declaration --
        //
        [Reason { kind: ReasonKind::Declaration, forward: true, .. }, Reason { kind: ReasonKind::FunctionDecl, loc, .. }, rest @ ..] => {
            needs_break = true;
            (
                Explanation::new(*loc, ExpressionKind::Used, "declared to a function"),
                rest,
            )
        }
        [Reason { kind: ReasonKind::FunctionDecl, loc, .. }, rest @ ..] => {
            needs_break = true;
            (
                Explanation::new(*loc, ExpressionKind::Used, "a function"),
                rest,
            )
        }
        [Reason { kind: ReasonKind::FunctionDeclReturnType, .. }, Reason { kind: ReasonKind::FunctionDeclReturned, loc, .. }, rest @ ..] => (
            Explanation::new(*loc, ExpressionKind::Used, "which returns"),
            rest,
        ),
        [Reason { kind: ReasonKind::FunctionDeclReturnType, loc, .. }, rest @ ..] => (
            Explanation::new(*loc, ExpressionKind::Used, "where the return type is"),
            rest,
        ),
        [Reason { kind: ReasonKind::FunctionDeclArgumentDeclaration(_), loc, .. }, rest @ ..] => (
            Explanation::new(*loc, ExpressionKind::Used, ", which is an argument of"),
            rest,
        ),
        [Reason { kind: ReasonKind::FunctionDeclReturned, loc, forward, .. }, rest @ ..] => (
            Explanation::new(*loc, ExpressionKind::Used, if *forward {
                "inferred from what is returned, which is"
            } else {
                "inferred from what is returned, which is"
            }),
            rest,
        ),

        // A declaration should only appear after a usage of a local variable.
        [Reason { kind: ReasonKind::Declaration, loc, forward: true, .. }, Reason { kind: ReasonKind::TypeBound, .. }, rest @ ..] => (
            Explanation::new(*loc, ExpressionKind::Used, "declared as"),
            rest,
        ),
        [Reason { kind: ReasonKind::Declaration, loc, forward: true, .. }, rest @ ..] => (
            Explanation::new(*loc, ExpressionKind::Used, "declared to"),
            rest,
        ),
        [Reason { kind: ReasonKind::Assigned, loc, forward: true, .. }, Reason { kind: ReasonKind::TypeBound, .. }, rest @ ..] => (
            Explanation::new(*loc, ExpressionKind::Used, "assigned as"),
            rest,
        ),
        [Reason { kind: ReasonKind::Assigned, forward: true, loc, .. }, rest @ ..] => (
            Explanation::new(*loc, ExpressionKind::Used, "assigned to"),
            rest,
        ),
        [Reason { kind: ReasonKind::Declaration | ReasonKind::Assigned, loc, forward: false, .. }, Reason { kind: ReasonKind::LocalVariableIs(name), .. }, Reason { kind: ReasonKind::LocalVariableIs(_), .. }, rest @ ..] => (
            Explanation::new(*loc, ExpressionKind::Used, format!(", which we assign to `{}`, which is", name)),
            rest,
        ),
        [Reason { kind: ReasonKind::Declaration | ReasonKind::Assigned, loc, forward: false, .. }, rest @ ..] => (
            Explanation::new(*loc, ExpressionKind::Used, "a value which we put into"),
            rest,
        ),
        [Reason { kind: ReasonKind::LocalVariableIs(name), loc, forward, .. }, Reason { kind: ReasonKind::LocalVariableIs(_), .. }, rest @ ..] => (
            Explanation::new(*loc, ExpressionKind::Used, if *forward { format!("`{}`", name) } else { format!("`{}`, which is", name) }),
            rest,
        ),
        [Reason { kind: ReasonKind::LocalVariableIs(name), loc, forward, .. }, rest @ ..] => (
            Explanation::new(*loc, ExpressionKind::Used, if *forward { format!("`{}`", name) } else { format!("`{}`, which is", name) }),
            rest,
        ),

        [Reason { kind: ReasonKind::TypeOf, loc, forward, .. }, rest @ ..] => (
            Explanation::new(*loc, ExpressionKind::Used, if *forward { "the type of" } else { ", the type of which" }),
            rest,
        ),
        [Reason { kind: ReasonKind::NamedField(name), loc, forward, .. }, rest @ ..] => (
            Explanation::new(*loc, ExpressionKind::Used, if !*forward { format!("the field `{}` of", name) } else { format!("a value, that has a field `{}`, that is", name) }),
            rest,
        ),
        [Reason { kind: ReasonKind::Dereference, loc, .. }, rest @ ..] => (
            Explanation::new(*loc, ExpressionKind::Used, "the value behind"),
            rest,
        ),
        [Reason { kind: ReasonKind::TypeBound, loc, forward, .. }, rest @ ..] => (
            Explanation::new(*loc, ExpressionKind::Used, if *forward { "a value bound as" } else { "use this type to bind" }),
            rest,
        ),
        [Reason { kind: ReasonKind::IntLiteral, loc, .. }] => (
            Explanation::new(*loc, ExpressionKind::Used, "an int literal"),
            &[],
        ),
        [Reason { kind: ReasonKind::LiteralType, loc, .. }] => (
            Explanation::new(*loc, ExpressionKind::Used, "the type"),
            &[],
        ),

        //
        // -- Function call --
        //
        [Reason { kind: ReasonKind::FunctionCallReturn, .. }, Reason { kind: ReasonKind::FunctionCall, loc, .. }, rest @ ..] => {
            (
                Explanation::new(*loc, ExpressionKind::Used, "a call to"),
                rest,
            )
        }
        [Reason { kind: ReasonKind::FunctionCall, .. }, Reason { kind: ReasonKind::FunctionCallArgument, loc, .. }, rest @ ..] => (
            Explanation::new(*loc, ExpressionKind::Used, "called with"),
            rest,
        ),
        [Reason { kind: ReasonKind::FunctionCallArgument, loc, .. }, Reason { kind: ReasonKind::FunctionCall, .. }, rest @ ..] => (
            Explanation::new(*loc, ExpressionKind::Used, ", an argument of a call to"),
            rest,
        ),

        [base, rest @ ..] => (
            Explanation::new(base.loc, ExpressionKind::Used, format!("<{:?}>", base.kind)),
            rest,
        ),
        [] => (
            Explanation::new(Location::unknown(), ExpressionKind::Used, format!("<Invalid end>")),
            &[],
        ),
    };

    if rest.is_empty() {
        explanation
    } else {
        let inner = get_concise_explanation(errors, ast, rest);
        if !needs_break && inner.message.len() < 100 && inner.loc.line == explanation.loc.line {
            Explanation {
                message: explanation.message + " " + &inner.message,
                loc: inner.loc,
                next: inner.next,
                kind: explanation.kind,
            }
        } else  {
            Explanation {
                message: explanation.message + "..",
                loc: explanation.loc,
                next: Some(Box::new(inner)),
                kind: explanation.kind,
            }
        }
    }
} 

#[derive(Debug)]
pub struct ReasoningChain {
    pub explaining: ValueId,
    pub distance: u32,
    pub chain: Vec<Reason>,
}

impl ReasoningChain {
    pub fn output(&self, errors: &mut ErrorCtx, ast: &Ast, types: &TypeSystem) {
        let chain = &self.chain[..];

        let explanation = get_concise_explanation(errors, ast, chain);
        if explanation.next.is_none() {
            errors.info(
                explanation.loc,
                format!(
                    "we {} {}, which is `{}`",
                    match explanation.kind {
                        ExpressionKind::Used => "use",
                    },
                    explanation.message,
                    types.value_to_str(self.explaining, 0),
                )
            );
        } else {
            errors.info(
                explanation.loc,
                format!(
                    "we {} {}",
                    match explanation.kind {
                        ExpressionKind::Used => "use",
                    },
                    explanation.message
                )
            );
        }

        let mut next = &explanation.next;
        while let Some(thing) = next {
            next = &thing.next;
            if next.is_none() {
                errors.info(
                    thing.loc,
                    format!("{}, which is `{}`", (thing.message.strip_prefix(", ").unwrap_or(&thing.message)), types.value_to_str(self.explaining, 0)),
                );
            } else {
                errors.info(
                    thing.loc,
                    (thing.message.strip_prefix(", ").unwrap_or(&thing.message)).to_string(),
                );
            }
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Reason {
    pub loc: Location,
    kind: ReasonKind,
    forward: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReasonKind {
    Passed,

    FunctionCall,
    FunctionCallReturn,
    FunctionCallArgument,

    FunctionDecl,
    FunctionDeclArgumentType(Ustr),
    FunctionDeclArgumentDeclaration(Ustr),
    FunctionDeclReturnType,
    FunctionDeclReturned,

    PolyMember(PolyMemberId),
    InferredPolyParam(usize),
    // @TODO: We want the parameter to be named, but we don't have that information right now...
    PolyParam(usize),
    Dereference,
    LocalVariableIs(Ustr),
    LiteralType,
    TypeOf,
    TypeBound,
    Declaration,
    NamedField(Ustr),
    Assigned,
    IntLiteral,
    // Some thing is literally a type, like the global `Thing` is of some specific type.
    IsOfType,
    // This reason means that we may have skipped a bunch of steps, so we should never add this to the chain unless we have no other choice(which would indicate a compiler bug).
    Ignore,
    Temp(&'static std::panic::Location<'static>),
}

impl ReasonKind {
    fn weight(&self) -> u32 {
        match self {
            Self::IsOfType => 1000,
            _ => 1,
        }
    }
}

impl Reason {
    pub fn new(loc: Location, kind: ReasonKind) -> Self {
        Self { loc, kind, forward: true }
    }

    #[track_caller]
    pub fn temp(loc: Location) -> Self {
        Self {
            loc,
            kind: ReasonKind::Temp(std::panic::Location::caller()),
            forward: true,
        }
    }

    #[track_caller]
    pub fn temp_zero() -> Self {
        Self::temp(Location::unknown())
    }
}
