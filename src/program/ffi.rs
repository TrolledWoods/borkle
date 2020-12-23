#![allow(clippy::map_entry)]

use crate::types::{IntTypeKind, Type, TypeKind};
use bumpalo::Bump;
#[allow(clippy::wildcard_imports)]
use libffi_sys::*;
use std::convert::TryFrom;
use std::fmt;
use std::mem::MaybeUninit;
use std::path::Path;
use ustr::{Ustr, UstrMap};

// FIXME: This type has no multithreading synchronisation jazz whatsoever; this is kindof a
// problem. Thing is I'm not sure if libffi supports multithreading, so putting everything behind a
// lock might be for the best... We'll see in the profiling later if this becomes a problem.
struct Library {
    lib: libloading::Library,
}

pub struct Libraries {
    libs: UstrMap<Library>,
}

impl Libraries {
    pub fn new() -> Self {
        Self {
            libs: UstrMap::default(),
        }
    }

    pub fn load_symbol(
        &mut self,
        lib_name: &Path,
        symbol_name: Ustr,
    ) -> Result<unsafe extern "C" fn(), libloading::Error> {
        let lib_name = lib_name.to_str().expect("Path not utf8? Wut!!!!").into();
        let lib = get_or_insert_lib(&mut self.libs, lib_name)?;

        Ok(unsafe {
            *lib.lib
                .get::<unsafe extern "C" fn()>(symbol_name.as_bytes())?
        })
    }

    pub fn iter(&self) -> impl Iterator<Item = Ustr> + '_ {
        self.libs.keys().copied()
    }
}

fn get_or_insert_lib(
    libs: &mut UstrMap<Library>,
    lib_name: Ustr,
) -> Result<&'_ mut Library, libloading::Error> {
    if !libs.contains_key(&lib_name) {
        libs.insert(
            lib_name,
            Library {
                lib: libloading::Library::new(lib_name.as_str())?,
            },
        );
    }

    Ok(libs.get_mut(&lib_name).unwrap())
}

#[derive(Clone, Copy)]
pub struct CallingConvention(ffi_cif);

impl fmt::Debug for CallingConvention {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(fmt, "FFICallingConvention")
    }
}

unsafe impl Send for CallingConvention {}
unsafe impl Sync for CallingConvention {}

impl CallingConvention {
    /// Creates a new calling convention. This can cause allocations, so it should be done somewhat
    /// sparingly. It will fail the given type is not an extern function.
    pub fn new(alloc: &Bump, type_: Type) -> Self {
        if let TypeKind::Function {
            args,
            returns,
            is_extern: true,
        } = type_.kind()
        {
            let arg_ffi_types = alloc.alloc_slice_copy(
                &args
                    .iter()
                    .filter_map(|&type_| {
                        type_to_ffi_type(type_).map(|ffi_type| alloc.alloc(ffi_type) as *mut _)
                    })
                    .collect::<Vec<_>>(),
            );
            let return_ffi_type = unsafe {
                alloc.alloc(type_to_ffi_type(*returns).unwrap_or(ffi_type_void)) as *mut _
            };

            unsafe {
                let mut cif = MaybeUninit::uninit();
                ffi_prep_cif(
                    cif.as_mut_ptr(),
                    ffi_abi_FFI_DEFAULT_ABI,
                    u32::try_from(arg_ffi_types.len()).unwrap(),
                    return_ffi_type,
                    arg_ffi_types.as_mut_ptr(),
                );
                Self(cif.assume_init())
            }
        } else {
            unreachable!("Give me extern function pointer!? Got {}", type_);
        }
    }

    /// Calls the Function.
    ///
    /// # Safety
    /// The data should contain all of the arguments that you have.
    /// The `ptr` has to be valid
    pub unsafe fn call(&self, ptr: unsafe extern "C" fn(), data: *mut *mut (), returns: *mut ()) {
        ffi_call(
            &self.0 as *const _ as *mut _,
            Some(ptr),
            returns.cast(),
            data.cast(),
        );
    }
}

/// Converts a compiler type into a libffi type. This might fail if the type
/// is zero sized!
fn type_to_ffi_type(type_: Type) -> Option<ffi_type> {
    // Safety: These statics should not be modified ever, I don't know why they are mutable statics.
    unsafe {
        match type_.kind() {
            TypeKind::Range(_) | TypeKind::Never | TypeKind::Empty => None,
            TypeKind::Type | TypeKind::Int(IntTypeKind::U64) => Some(ffi_type_uint64),
            TypeKind::Int(IntTypeKind::I64) => Some(ffi_type_sint64),
            TypeKind::Int(IntTypeKind::U32) => Some(ffi_type_uint32),
            TypeKind::Int(IntTypeKind::I32) => Some(ffi_type_sint32),
            TypeKind::Int(IntTypeKind::U16) => Some(ffi_type_uint16),
            TypeKind::Int(IntTypeKind::I16) => Some(ffi_type_sint16),
            TypeKind::Int(IntTypeKind::U8) => Some(ffi_type_uint8),
            TypeKind::Int(IntTypeKind::I8) => Some(ffi_type_sint8),
            TypeKind::F64 => Some(ffi_type_double),
            TypeKind::F32 => Some(ffi_type_float),
            TypeKind::Bool => Some(ffi_type_uint8),
            TypeKind::Int(IntTypeKind::Usize) => Some(ffi_type_pointer),
            TypeKind::Int(IntTypeKind::Isize) => Some(ffi_type_pointer),
            TypeKind::Reference(_) | TypeKind::Function { .. } => Some(ffi_type_pointer),
            TypeKind::Array(_, _) => {
                todo!("Array ffi is not implemented yet");
            }
            TypeKind::Buffer(_) => {
                todo!("Buffer ffi is not implemented yet");
            }
            TypeKind::Struct(_) => {
                todo!("Struct ffi is not implemented yet");
            }
        }
    }
}
