use super::{static_values, TypeSystem, ConstraintId, ValueId, IdMapper, MappedId, ConstraintKind};
use std::collections::{hash_map, HashMap};
use crate::errors::ErrorCtx;
use crate::parser::Ast;
use ustr::Ustr;

pub fn get_reasons(base_value: ValueId, types: &TypeSystem, mapper: &IdMapper, ast: &crate::parser::Ast) -> Vec<ReasoningChain> {
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

    fn reason_from_values(system: &TypeSystem, base_value: ValueId, mut graph: HashMap<(ValueId, Vec<usize>), Node>, mut frontier: Vec<Frontier>) -> ReasoningChain {
        'path_loop: loop {
            let Some((index, _)) = frontier.iter().enumerate().min_by_key(|(_, v)| v.distance) else { panic!("Exited too early I think") };
            let Frontier { source, distance, constraint_id } = frontier.swap_remove(index);

            if source.0 < static_values::STATIC_VALUES_SIZE {
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
                            distance: distance + 1,
                            constraint_id,
                        }));
                    }
                }
            }
        }

        debug_assert!(graph.contains_key(&(base_value, Vec::new())));

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

            graph.insert((value_id, Vec::new()), node);

            if let Some(constraints) = types.available_constraints.get(&value_id) {
                frontier.extend(constraints.iter().map(|&constraint_id| Frontier {
                    source: (value_id, Vec::new()),
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
    let mut needs_break = false;

    let (explanation, rest) : (_, &[_]) = match chain {
        //
        // -- Function declaration --
        //
        [Reason { kind: ReasonKind::Declaration, forward: true, .. }, Reason { kind: ReasonKind::FunctionDecl, node, .. }, rest @ ..] => {
            needs_break = true;
            (
                Explanation::new(*node, ExpressionKind::Used, "declared to a function"),
                rest,
            )
        }
        [Reason { kind: ReasonKind::FunctionDecl, node, .. }, rest @ ..] => {
            needs_break = true;
            (
                Explanation::new(*node, ExpressionKind::Used, "a function"),
                rest,
            )
        }
        [Reason { kind: ReasonKind::FunctionDeclReturnType, .. }, Reason { kind: ReasonKind::FunctionDeclReturned, node, .. }, rest @ ..] => (
            Explanation::new(*node, ExpressionKind::Used, "which returns"),
            rest,
        ),
        [Reason { kind: ReasonKind::FunctionDeclReturnType, node, .. }, rest @ ..] => (
            Explanation::new(*node, ExpressionKind::Used, "where the return type is"),
            rest,
        ),
        [Reason { kind: ReasonKind::FunctionDeclArgumentDeclaration(_), node, .. }, rest @ ..] => (
            Explanation::new(*node, ExpressionKind::Used, ", which is an argument of"),
            rest,
        ),
        [Reason { kind: ReasonKind::FunctionDeclReturned, node, forward, .. }, rest @ ..] => (
            Explanation::new(*node, ExpressionKind::Used, if *forward {
                "inferred from what is returned, which is"
            } else {
                "inferred from what is returned, which is"
            }),
            rest,
        ),

        // A declaration should only appear after a usage of a local variable.
        [Reason { kind: ReasonKind::Declaration, node, forward: true, .. }, Reason { kind: ReasonKind::TypeBound, .. }, rest @ ..] => (
            Explanation::new(*node, ExpressionKind::Used, "declared as"),
            rest,
        ),
        [Reason { kind: ReasonKind::Declaration, node, forward: true, .. }, rest @ ..] => (
            Explanation::new(*node, ExpressionKind::Used, "declared to"),
            rest,
        ),
        [Reason { kind: ReasonKind::Assigned, node, forward: true, .. }, Reason { kind: ReasonKind::TypeBound, .. }, rest @ ..] => (
            Explanation::new(*node, ExpressionKind::Used, "assigned as"),
            rest,
        ),
        [Reason { kind: ReasonKind::Assigned, forward: true, node, .. }, rest @ ..] => (
            Explanation::new(*node, ExpressionKind::Used, "assigned to"),
            rest,
        ),
        [Reason { kind: ReasonKind::Declaration | ReasonKind::Assigned, node, forward: false, .. }, Reason { kind: ReasonKind::LocalVariableIs(name), .. }, Reason { kind: ReasonKind::LocalVariableIs(_), .. }, rest @ ..] => (
            Explanation::new(*node, ExpressionKind::Used, format!(", which we assign to `{}`, which is", name)),
            rest,
        ),
        [Reason { kind: ReasonKind::Declaration | ReasonKind::Assigned, node, forward: false, .. }, rest @ ..] => (
            Explanation::new(*node, ExpressionKind::Used, "a value which we put into"),
            rest,
        ),
        [Reason { kind: ReasonKind::LocalVariableIs(name), node, forward, .. }, Reason { kind: ReasonKind::LocalVariableIs(_), .. }, rest @ ..] => (
            Explanation::new(*node, ExpressionKind::Used, if *forward { format!("`{}`", name) } else { format!("`{}`, which is", name) }),
            rest,
        ),
        [Reason { kind: ReasonKind::LocalVariableIs(name), node, forward, .. }, rest @ ..] => (
            Explanation::new(*node, ExpressionKind::Used, if *forward { format!("`{}`", name) } else { format!("`{}`, which is", name) }),
            rest,
        ),

        [Reason { kind: ReasonKind::TypeOf, node, forward, .. }, rest @ ..] => (
            Explanation::new(*node, ExpressionKind::Used, if *forward { "the type of" } else { ", the type of which" }),
            rest,
        ),
        [Reason { kind: ReasonKind::NamedField(name), node, forward, .. }, rest @ ..] => (
            Explanation::new(*node, ExpressionKind::Used, if !*forward { format!("the field `{}` of", name) } else { format!("a value, that has a field `{}`, that is", name) }),
            rest,
        ),
        [Reason { kind: ReasonKind::Assigned, node, .. }, rest @ ..] => (
            Explanation::new(*node, ExpressionKind::Used, "assigned to"),
            rest,
        ),
        [Reason { kind: ReasonKind::TypeBound, node, forward, .. }, rest @ ..] => (
            Explanation::new(*node, ExpressionKind::Used, if *forward { "a value bound as" } else { "use this type to bind" }),
            rest,
        ),
        [Reason { kind: ReasonKind::IntLiteral, node, .. }] => (
            Explanation::new(*node, ExpressionKind::Used, "an int literal"),
            &[],
        ),
        [Reason { kind: ReasonKind::LiteralType, node, .. }] => (
            Explanation::new(*node, ExpressionKind::Used, "the type"),
            &[],
        ),

        //
        // -- Function call --
        //
        [Reason { kind: ReasonKind::FunctionCallReturn, .. }, Reason { kind: ReasonKind::FunctionCall, node, .. }, rest @ ..] => {
            (
                Explanation::new(*node, ExpressionKind::Used, "a call to"),
                rest,
            )
        }
        [Reason { kind: ReasonKind::FunctionCall, .. }, Reason { kind: ReasonKind::FunctionCallArgument, node, .. }, rest @ ..] => (
            Explanation::new(*node, ExpressionKind::Used, "called with"),
            rest,
        ),
        [Reason { kind: ReasonKind::FunctionCallArgument, node, .. }, Reason { kind: ReasonKind::FunctionCall, .. }, rest @ ..] => (
            Explanation::new(*node, ExpressionKind::Used, ", an argument of a call to"),
            rest,
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
        if !needs_break && inner.message.len() < 100 && ast.get(inner.node).loc.line == ast.get(explanation.node).loc.line {
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
                (thing.message.strip_prefix(", ").unwrap_or(&thing.message)).to_string(),
            );
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Reason {
    pub node: crate::parser::NodeId,
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

impl Reason {
    pub fn new(node: crate::parser::NodeId, kind: ReasonKind) -> Self {
        Self { node, kind, forward: true }
    }

    #[track_caller]
    pub fn temp(node: crate::parser::NodeId) -> Self {
        Self {
            node,
            kind: ReasonKind::Temp(std::panic::Location::caller()),
            forward: true,
        }
    }

    #[track_caller]
    pub fn temp_zero() -> Self {
        Self::temp(crate::parser::NodeId(0))
    }
}
