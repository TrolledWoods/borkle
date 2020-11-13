use ustr::Ustr;

#[derive(Debug, Clone, Copy)]
pub struct Location {
    pub file: Ustr,
    pub line: u32,
    pub character: u32,
}
