use crate::location::Location;
use crate::types::{Type, TypeKind};
use std::fmt;

#[derive(Clone, Copy)]
pub struct WantedType {
    pub loc: Option<Location>,
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
            loc: None,
            kind: WantedKind::None,
        }
    }

    pub fn maybe_specific(loc: Option<Location>, type_: Option<Type>) -> Self {
        Self {
            loc,
            kind: match type_ {
                Some(type_) => WantedKind::Specific(type_),
                None => WantedKind::None,
            },
        }
    }

    pub fn specific(loc: Option<Location>, type_: Type) -> Self {
        Self {
            loc,
            kind: WantedKind::Specific(type_),
        }
    }

    pub fn array(loc: Option<Location>, type_: Type) -> Self {
        Self {
            loc,
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
                    Some(Self::specific(self.loc, *element))
                }
                _ => None,
            },
            WantedKind::Array(element) => Some(Self::specific(self.loc, element)),
        }
    }

    pub fn get_pointee(&self) -> Option<Self> {
        match self.kind {
            WantedKind::None => Some(Self::none()),
            WantedKind::Specific(type_) => match type_.kind() {
                TypeKind::Reference(inner) => Some(Self::specific(self.loc, *inner)),
                TypeKind::Buffer(inner) => Some(Self::array(self.loc, *inner)),
                _ => None,
            },
            WantedKind::Array(_) => None,
        }
    }

    pub fn type_fits(&self, got: Type) -> bool {
        if got.is_never_type() {
            return true;
        }

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
            Some(type_) => Self::specific(None, type_),
            None => Self::none(),
        }
    }
}

impl From<Type> for WantedType {
    fn from(other: Type) -> Self {
        Self::specific(None, other)
    }
}
