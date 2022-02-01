// @Volatile: These have to match the definitions inside of `library\compiler.bo`.
// This is also why they are not an enum, since borkle enums are not guaranteed to only contain
// valid variant values.
pub const CALL_BORKLE: u8 = 0;
pub const CALL_C:      u8 = 1;

