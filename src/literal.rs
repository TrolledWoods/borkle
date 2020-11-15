#[derive(Debug, Clone, PartialEq)]
pub enum Literal {
    Int(u64),
    String(String),
}
