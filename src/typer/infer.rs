use super::ast::Node;
use crate::self_buffer::SelfBuffer;
use crate::types::{Type, TypeKind};
use std::fmt;

#[derive(Clone, Copy)]
pub struct WantedType {
    kind: WantedKind,
}

#[derive(Clone, Copy)]
enum WantedKind {
    Array(Type),
    Specific(Type),
    None,
}

impl WantedType {
    pub fn none() -> Self {
        Self {
            kind: WantedKind::None,
        }
    }

    pub fn specific(type_: Type) -> Self {
        Self {
            kind: WantedKind::Specific(type_),
        }
    }

    pub fn array(type_: Type) -> Self {
        Self {
            kind: WantedKind::Array(type_),
        }
    }

    pub fn get_specific(&self) -> Option<Type> {
        if let WantedKind::Specific(type_) = self.kind {
            Some(type_)
        } else {
            None
        }
    }

    pub fn get_element(&self) -> Option<Self> {
        match self.kind {
            WantedKind::None => Some(Self::none()),
            WantedKind::Specific(type_) => match type_.kind() {
                TypeKind::Array(element, _) | TypeKind::Buffer(element) => {
                    Some(Self::specific(*element))
                }
                _ => None,
            },
            WantedKind::Array(element) => Some(Self::specific(element)),
        }
    }

    pub fn get_pointee(&self) -> Option<Self> {
        match self.kind {
            WantedKind::None => Some(Self::none()),
            WantedKind::Specific(type_) => match type_.kind() {
                TypeKind::Reference(inner) => Some(Self::specific(*inner)),
                TypeKind::Buffer(inner) => Some(Self::array(*inner)),
                _ => None,
            },
            WantedKind::Array(_) => None,
        }
    }

    pub fn cast_node(&self, got: Node, buffer: &mut SelfBuffer) -> Result<Node, ()> {
        match self.kind {
            WantedKind::None => Ok(got),
            WantedKind::Specific(type_) => {
                if got.type_() == type_ {
                    Ok(got)
                } else {
                    Err(())
                }
            }
            WantedKind::Array(inner) => match got.type_().kind() {
                TypeKind::Array(element, _) if *element == inner => Ok(got),
                _ => Err(()),
            },
        }
    }

    pub fn type_fits(&self, got: Type) -> bool {
        match self.kind {
            WantedKind::None => true,
            WantedKind::Specific(wanted) => wanted == got,
            WantedKind::Array(inner) => match *got.kind() {
                TypeKind::Array(got_inner, _) => got_inner == inner,
                _ => false,
            },
        }
    }
}

impl fmt::Display for WantedType {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind {
            WantedKind::None => write!(fmt, "none"),
            WantedKind::Specific(inner) => inner.fmt(fmt),
            WantedKind::Array(inner) => write!(fmt, "[_] {}", inner),
        }
    }
}

impl From<Option<Type>> for WantedType {
    fn from(other: Option<Type>) -> Self {
        match other {
            Some(type_) => Self::specific(type_),
            None => Self::none(),
        }
    }
}

impl From<Type> for WantedType {
    fn from(other: Type) -> Self {
        Self::specific(other)
    }
}
