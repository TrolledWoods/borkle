use super::{TypeSystem, ConstraintId, ValueId, IdMapper, MappedId};
use std::collections::{hash_map, HashMap};
use crate::errors::ErrorCtx;
use crate::parser::Ast;
use ustr::Ustr;

pub fn get_reasons(base_value: ValueId, types: &TypeSystem, mapper: &IdMapper, ast: &crate::parser::Ast) -> Vec<ReasoningChain> {
    #[derive(Default)]
    struct Node {
        source: Option<ValueId>,
        reason: Option<Reason>,
        distance: u32,
    }

    struct Frontier {
        source: ValueId,
        distance: u32,
        constraint_id: ConstraintId,
    }

    fn reason_from_values(system: &TypeSystem, base_value: ValueId, mut graph: HashMap<ValueId, Node>, mut frontier: Vec<Frontier>) -> ReasoningChain {
        while let Some(Frontier { source, distance, constraint_id }) = frontier.pop() {
            let constraint = &system.constraints[constraint_id];
            for &value_id in constraint.values() {
                let new_node = Node {
                    source: Some(source),
                    distance,
                    reason: Some(constraint.reason),
                };

                let progress = match graph.entry(value_id) {
                    hash_map::Entry::Occupied(mut entry) => {
                        let entry = entry.get_mut();
                        if entry.distance > new_node.distance {
                            *entry = new_node;
                            true
                        } else {
                            false
                        }
                    }
                    hash_map::Entry::Vacant(entry) => {
                        entry.insert(new_node);
                        true
                    }
                };

                if progress {
                    if let Some(constraints) = system.available_constraints.get(&value_id) {
                        frontier.extend(constraints.iter().map(|&constraint_id| Frontier {
                            source: value_id,
                            distance: distance + 1,
                            constraint_id,
                        }));
                    }
                }
            }
        }

        let mut chain = Vec::new();
        let mut next = Some(base_value);
        while let Some(value_id) = next {
            let node = &graph[&value_id];
            if let Some(reason) = node.reason {
                chain.push(reason);
            }
            next = node.source;
        }

        ReasoningChain {
            chain,
        }
    }

    let mut reasons = Vec::new();
    for value_id in types.values.iter_values_in_structure(base_value) {
        if *types.values.get(value_id).is_base_value {
            let mut graph = HashMap::new();
            let mut frontier = Vec::new();
            // It's a base value, which means that we can draw a chain of reasoning from it.
            let node = Node {
                source: None,
                reason: match mapper.map(value_id) {
                    MappedId::AstNode(id) => Some(crate::typer::explain_given_type(ast, id)),
                    _ => None,
                },
                distance: 0,
            };
            graph.insert(value_id, node);

            if let Some(constraints) = types.available_constraints.get(&value_id) {
                frontier.extend(constraints.iter().map(|&constraint_id| Frontier {
                    source: value_id,
                    distance: 1,
                    constraint_id,
                }));
                reasons.push(reason_from_values(types, base_value, graph, frontier));
            }
        }
    }
    
    reasons
}

#[derive(Clone, Copy)]
enum ExpressionKind {
    Used,
    Created,
}

struct Explanation {
    node: crate::parser::NodeId,
    message: String,
    kind: ExpressionKind,
    next: Option<Box<Explanation>>,
}

impl Explanation {
    fn new(node: crate::parser::NodeId, kind: ExpressionKind, message: impl Into<String>) -> Self {
        Self {
            node,
            message: message.into(),
            kind,
            next: None,
        }
    }
}

fn get_concise_explanation(errors: &mut ErrorCtx, ast: &Ast, chain: &[Reason]) -> Explanation {
    let (explanation, rest) : (_, &[_]) = match chain {
        [Reason { kind: ReasonKind::Passed, .. }, rest @ ..] => (get_concise_explanation(errors, ast, rest), &[]),

        // A declaration should only appear after a usage of a local variable.
        [Reason { kind: ReasonKind::LocalVariableIs(_), .. }, Reason { kind: ReasonKind::Declaration, node }, Reason { kind: ReasonKind::TypeBound, .. }, rest @ ..] => (
            Explanation::new(*node, ExpressionKind::Used, "declared as"),
            rest,
        ),
        [Reason { kind: ReasonKind::LocalVariableIs(_), .. }, Reason { kind: ReasonKind::Declaration, node }, rest @ ..] => (
            Explanation::new(*node, ExpressionKind::Used, "declared to"),
            rest,
        ),
        [Reason { kind: ReasonKind::LocalVariableIs(_), .. }, Reason { kind: ReasonKind::Assigned, node }, Reason { kind: ReasonKind::TypeBound, .. }, rest @ ..] => (
            Explanation::new(*node, ExpressionKind::Used, "assigned as"),
            rest,
        ),
        [Reason { kind: ReasonKind::LocalVariableIs(_), .. }, Reason { kind: ReasonKind::Assigned, node }, rest @ ..] => (
            Explanation::new(*node, ExpressionKind::Used, "assigned to"),
            rest,
        ),
        [Reason { kind: ReasonKind::LocalVariableIs(name), node }, rest @ ..] => (
            Explanation::new(*node, ExpressionKind::Used, format!("`{}`, which is", name)),
            rest,
        ),

        [Reason { kind: ReasonKind::TypeOf, node }, rest @ ..] => (
            Explanation::new(*node, ExpressionKind::Used, "the type of"),
            rest,
        ),
        [Reason { kind: ReasonKind::NamedField(name), node }, rest @ ..] => (
            Explanation::new(*node, ExpressionKind::Used, format!("the field `{}`, which is", name)),
            rest,
        ),
        [Reason { kind: ReasonKind::ReturnedFromFunction, node }, rest @ ..] => (
            Explanation::new(*node, ExpressionKind::Used, "returned from a function, whose return type is"),
            rest,
        ),
        [Reason { kind: ReasonKind::Assigned, node }, rest @ ..] => (
            Explanation::new(*node, ExpressionKind::Used, "assigned to"),
            rest,
        ),
        [Reason { kind: ReasonKind::TypeBound, node }, rest @ ..] => (
            Explanation::new(*node, ExpressionKind::Used, "a value bound as"),
            rest,
        ),
        [Reason { kind: ReasonKind::IntLiteral, node, .. }] => (
            Explanation::new(*node, ExpressionKind::Used, "an int literal"),
            &[],
        ),
        [Reason { kind: ReasonKind::LiteralType, node, .. }] => (
            Explanation::new(*node, ExpressionKind::Used, "this type"),
            &[],
        ),
        [base, rest @ ..] => (
            Explanation::new(base.node, ExpressionKind::Used, format!("{:?}", base.kind)),
            rest,
        ),
        [] => unreachable!("Invalid explanation!"),
    };

    if rest.is_empty() {
        explanation
    } else {
        let inner = get_concise_explanation(errors, ast, rest);
        if ast.get(inner.node).loc.line == ast.get(explanation.node).loc.line {
            Explanation {
                message: explanation.message + " " + &inner.message,
                node: inner.node,
                next: inner.next,
                kind: explanation.kind,
            }
        } else  {
            Explanation {
                message: explanation.message + "..",
                node: explanation.node,
                next: Some(Box::new(inner)),
                kind: explanation.kind,
            }
        }
    }
} 

#[derive(Debug)]
pub struct ReasoningChain {
    pub chain: Vec<Reason>,
}

impl ReasoningChain {
    pub fn output(&self, errors: &mut ErrorCtx, ast: &Ast) {
        let chain = &self.chain[..];

        let explanation = get_concise_explanation(errors, ast, chain);
        errors.info(
            ast.get(explanation.node).loc,
            format!(
                "we {} {}",
                match explanation.kind {
                    ExpressionKind::Used => "use",
                    ExpressionKind::Created => "create",
                },
                explanation.message
            )
        );

        let mut next = &explanation.next;
        while let Some(thing) = next {
            next = &thing.next;
            errors.info(
                ast.get(thing.node).loc,
                thing.message.clone(),
            );
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Reason {
    node: crate::parser::NodeId,
    kind: ReasonKind,
}

#[derive(Debug, Clone, Copy)]
pub enum ReasonKind {
    Passed,
    LocalVariableIs(Ustr),
    LiteralType,
    TypeOf,
    TypeBound,
    ReturnedFromFunction,
    Declaration,
    NamedField(Ustr),
    Assigned,
    IntLiteral,
    // Some thing is literally a type, like the global `Thing` is of some specific type.
    IsOfType,
    Temp(&'static std::panic::Location<'static>),
}

impl Reason {
    pub fn new(node: crate::parser::NodeId, kind: ReasonKind) -> Self {
        Self { node, kind }
    }

    #[track_caller]
    pub fn temp(node: crate::parser::NodeId) -> Self {
        Self {
            node,
            kind: ReasonKind::Temp(std::panic::Location::caller()),
        }
    }
}
