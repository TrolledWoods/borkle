use crate::errors::ErrorCtx;
use crate::literal::Literal;
use crate::parser::{self, ast::NodeKind as ParserNodeKind};
use crate::types::{Type, TypeKind};
use ast::{Node, NodeKind};

type ParsedAst = bump_tree::Tree<parser::ast::Node>;
type ParsedNode<'a> = bump_tree::Node<'a, parser::ast::Node>;

type Ast = bump_tree::Tree<Node>;
type NodeBuilder<'a> = bump_tree::NodeBuilder<'a, Node>;

mod ast;

pub fn process_ast(errors: &mut ErrorCtx, ast: &ParsedAst) -> Result<Ast, ()> {
    let root = ast.root().unwrap();
    let mut ast = Ast::new();
    type_ast(errors, None, root, ast.builder())?;
    ast.set_root();
    Ok(ast)
}

// NOTE: ParsedNode is both Copy and 8 bytes. I don't see why the lint is triggered
// in this case.
#[allow(clippy::needless_pass_by_value)]
pub fn type_ast(
    errors: &mut ErrorCtx,
    wanted_type: Option<Type>,
    parsed: ParsedNode<'_>,
    mut node: NodeBuilder<'_>,
) -> Result<(), ()> {
    let parsed_node = &*parsed;
    match parsed_node.kind {
        ParserNodeKind::Literal(Literal::Int(num)) => {
            node.set(Node::new(
                parsed_node.loc,
                NodeKind::Constant(num.to_le_bytes().into()),
                TypeKind::I64,
            ));
        }
        _ => todo!(),
    }

    Ok(())
}
