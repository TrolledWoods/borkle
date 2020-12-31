use crate::operators::{BinaryOp, UnaryOp};
use crate::program::constant::ConstantRef;
use crate::program::ffi;
use crate::types::{to_align, Type, TypeKind};
use std::fmt;
use ustr::Ustr;

#[derive(Clone)]
#[allow(non_camel_case_types)]
pub enum Instr {
    // to = pointer(args)
    CallExtern {
        to: Value,
        pointer: Value,
        // FIXME: We don't really want a vector here, we want a more efficient datastructure
        args: Vec<Value>,
        convention: ffi::CallingConvention,
    },
    // to = pointer(args)
    Call {
        to: Value,
        pointer: Value,
        // FIXME: We don't really want a vector here, we want a more efficient datastructure
        args: Vec<Value>,
    },
    // to = from
    Constant {
        to: Value,
        from: ConstantRef,
    },
    // value ++
    Increment {
        value: Value,
    },
    // to = a op b
    Binary {
        op: BinaryOp,
        to: Value,
        a: Value,
        b: Value,
    },
    // to = op from
    Unary {
        op: UnaryOp,
        to: Value,
        from: Value,
    },
    // to = of.member
    Member {
        to: Value,
        of: Value,
        member: Member,
    },
    // to = &(*of).member
    MemberIndirect {
        to: Value,
        of: Value,
        member: Member,
    },
    // to = *from
    Dereference {
        to: Value,
        from: Value,
    },
    // to = &from.offset
    Reference {
        to: Value,
        from: Value,
        offset: Member,
    },
    // to.member = from
    Move {
        to: Value,
        from: Value,
        size: usize,
        member: Member,
    },
    // &(*to).member = from
    MoveIndirect {
        to: Value,
        from: Value,
        size: usize,
        member: Member,
    },
    // jump to 'to' if condition
    JumpIfZero {
        condition: Value,
        to: LabelId,
    },
    // jump to 'to'
    Jump {
        to: LabelId,
    },
    LabelDefinition(LabelId),
    //
    // ##################################
    // ##                              ##
    // ## Intrinsic-esque instructions ##
    // ##                              ##
    // ##################################
    //
    i_stdout_write {
        to: Value,
        buffer: Value,
    },
    i_stdout_flush,
    i_stdin_getline {
        to: Value,
    },
    i_alloc {
        to: Value,
        size: Value,
    },
    i_dealloc {
        buffer: Value,
    },
    i_copy {
        from: Value,
        to: Value,
        size: Value,
    },
    i_copy_nonoverlapping {
        from: Value,
        to: Value,
        size: Value,
    },
}

impl fmt::Debug for Instr {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::CallExtern {
                to,
                pointer,
                args,
                convention: _,
            }
            | Self::Call { to, pointer, args } => {
                write!(fmt, "{} = {}(", to, pointer)?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(fmt, ", ")?;
                    }

                    write!(fmt, "{}", arg)?;
                }
                write!(fmt, ")")?;
                Ok(())
            }
            Self::Constant { to, from: _ } => write!(fmt, "{} = const", to),
            Self::Increment { value } => write!(fmt, "{} += 1", value),
            Self::Binary { op, to, a, b } => write!(fmt, "{} = {} {:?} {}", to, a, op, b),
            Self::Unary { op, to, from } => write!(fmt, "{} = {:?} {}", to, op, from),
            Self::MemberIndirect { to, of, member } => {
                write!(fmt, "{} = &(*{})", to, of)?;
                for name in &member.name_list {
                    write!(fmt, ".{}", name)?;
                }
                Ok(())
            }
            Self::Member { to, of, member } => {
                write!(fmt, "{} = {}", to, of)?;
                for name in &member.name_list {
                    write!(fmt, ".{}", name)?;
                }
                Ok(())
            }
            Self::Dereference { to, from } => write!(fmt, "{} = *{}", to, from),
            Self::Reference { to, from, offset } => {
                write!(fmt, "{}", to)?;
                for name in &offset.name_list {
                    write!(fmt, ".{}", name)?;
                }
                write!(fmt, "= &{}", from)
            }
            Self::Move {
                to,
                from,
                size: _,
                member,
            } => {
                write!(fmt, "{}", to)?;
                for name in &member.name_list {
                    write!(fmt, ".{}", name)?;
                }
                write!(fmt, "= {}", from)
            }
            Self::MoveIndirect {
                to,
                from,
                size: _,
                member,
            } => {
                write!(fmt, "*{}", to)?;
                for name in &member.name_list {
                    write!(fmt, ".{}", name)?;
                }
                write!(fmt, "= {}", from)
            }
            Self::JumpIfZero { condition, to } => {
                write!(fmt, "jump to {} if {} == 0", to.0, condition)
            }
            Self::Jump { to } => write!(fmt, "jump to {}", to.0),
            Self::LabelDefinition(id) => write!(fmt, "-- label {}", id.0),
            Self::i_stdout_write { to, buffer } => {
                write!(fmt, "{} = i_stdout_write({})", to, buffer)
            }
            Self::i_stdout_flush => write!(fmt, "i_stdout_flush()"),
            Self::i_stdin_getline { to } => {
                write!(fmt, "{} = i_stdin_getline()", to)
            }
            Self::i_alloc { to, size } => write!(fmt, "{} = i_alloc({})", to, size),
            Self::i_dealloc { buffer } => write!(fmt, "i_dealloc({})", buffer),
            Self::i_copy { from, to, size } => write!(fmt, "i_copy({}, {}, {})", from, to, size),
            Self::i_copy_nonoverlapping { from, to, size } => {
                write!(fmt, "i_copy_nonoverlapping({}, {}, {})", from, to, size)
            }
        }
    }
}

#[derive(Default, Debug, Clone)]
pub struct Member {
    pub offset: usize,
    // FIXME: This is inefficient af!!!!
    pub name_list: Vec<Ustr>,
}

// Why is this safe? Well, because we do not have interior mutability anywhere, so the raw pointers
// are okay.
unsafe impl Send for Instr {}
unsafe impl Sync for Instr {}

pub struct Routine {
    pub label_locations: Vec<usize>,
    pub instr: Vec<Instr>,
    pub registers: Registers,
    pub result: Value,
}

pub struct Registers {
    pub(crate) locals: Vec<Register>,
    // If you had a buffer with a bunch of locals inside,
    // how big would that buffer have to be to fit all of them?
    max_buffer_size: usize,
    buffer_head: usize,
}

impl Registers {
    pub fn new() -> Self {
        Self {
            locals: Vec::new(),
            max_buffer_size: 0,
            buffer_head: 0,
        }
    }

    pub fn buffer_size(&self) -> usize {
        self.max_buffer_size.max(self.buffer_head)
    }

    pub fn get_head(&self) -> usize {
        self.buffer_head
    }

    pub fn set_head(&mut self, head: usize) {
        assert!(head <= self.buffer_head);

        self.max_buffer_size = self.max_buffer_size.max(self.buffer_head);
        self.buffer_head = head;
    }

    pub fn create(&mut self, type_: impl Into<Type>) -> Value {
        self.create_min_align(type_.into(), 1)
    }

    pub fn zst(&mut self) -> Value {
        self.create(TypeKind::Empty)
    }

    pub fn create_min_align(&mut self, type_: impl Into<Type>, min_align: usize) -> Value {
        let type_ = type_.into();
        let mut align = type_.align();
        if align < min_align {
            align = min_align;
        }
        self.buffer_head = to_align(self.buffer_head, align);
        let value = Value::Register(self.locals.len(), type_);
        self.locals.push(Register {
            offset: self.buffer_head,
            type_,
        });
        self.buffer_head += to_align(type_.size(), align);
        value
    }

    pub(crate) fn get(&self, index: usize) -> &'_ Register {
        &self.locals[index]
    }
}

pub(crate) struct Register {
    offset: usize,
    pub(crate) type_: Type,
}

impl Register {
    pub(crate) fn offset(&self) -> usize {
        self.offset
    }

    pub(crate) fn size(&self) -> usize {
        self.type_.size()
    }
}

#[derive(Debug, Clone, Copy)]
pub enum Value {
    Register(usize, Type),
    Global(ConstantRef, Type),
}

impl fmt::Display for Value {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Register(id, type_) => write!(fmt, "{} {}", type_, id),
            Value::Global(_, type_) => write!(fmt, "const {}", type_),
        }
    }
}

unsafe impl Send for Value {}
unsafe impl Sync for Value {}

impl Value {
    pub fn type_(&self) -> Type {
        match self {
            Self::Register(_, type_) => *type_,
            Self::Global(_, type_) => *type_,
        }
    }

    pub fn size(&self) -> usize {
        self.type_().size()
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct LabelId(pub usize);
