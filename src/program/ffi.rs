#![allow(clippy::map_entry)]

use crate::types::{Type, TypeKind};
use bumpalo::Bump;
#[allow(clippy::wildcard_imports)]
use libffi_sys::*;
use std::convert::TryFrom;
use std::mem::MaybeUninit;
use ustr::{Ustr, UstrMap};

// FIXME: This type has no multithreading synchronisation jazz whatsoever; this is kindof a
// problem. Thing is I'm not sure if libffi supports multithreading, so putting everything behind a
// lock might be for the best... We'll see in the profiling later if this becomes a problem.
struct Library {
    lib: libloading::Library,
    functions: UstrMap<Function>,
}

pub struct Libraries {
    alloc: Bump,
    libs: UstrMap<Library>,
}

impl Libraries {
    pub fn new() -> Self {
        Self {
            alloc: Bump::new(),
            libs: UstrMap::default(),
        }
    }

    pub fn load_symbol(
        &mut self,
        lib_name: Ustr,
        symbol_name: Ustr,
        arg_types: &[Type],
        return_type: Type,
    ) -> Result<Function, libloading::Error> {
        let lib = get_or_insert_lib(&mut self.libs, lib_name)?;

        if !lib.functions.contains_key(&symbol_name) {
            let ptr = *unsafe { lib.lib.get::<*const ()>(symbol_name.as_bytes())? };

            let alloc = &self.alloc;
            let arg_ffi_types = alloc.alloc_slice_copy(
                &arg_types
                    .iter()
                    .filter_map(|&type_| {
                        type_to_ffi_type(alloc, type_)
                            .map(|ffi_type| alloc.alloc(ffi_type) as *mut _)
                    })
                    .collect::<Vec<_>>(),
            );
            let return_ffi_type = unsafe {
                alloc.alloc(type_to_ffi_type(&self.alloc, return_type).unwrap_or(ffi_type_void))
                    as *mut _
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
                let cif = cif.assume_init();
                lib.functions.insert(
                    symbol_name,
                    Function {
                        calling_convention: cif,
                        ptr,
                    },
                );
            };
        }

        Ok(*lib.functions.get(&symbol_name).unwrap())
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
                functions: UstrMap::default(),
            },
        );
    }

    Ok(libs.get_mut(&lib_name).unwrap())
}

#[derive(Clone, Copy)]
pub struct Function {
    calling_convention: ffi_cif,
    ptr: *const (),
}

unsafe impl Send for Function {}
unsafe impl Sync for Function {}

impl Function {
    /// Calls the Function.
    ///
    /// # Safety
    /// The data should contain all of the arguments that you have.
    pub unsafe fn call(&self, data: *mut *mut (), returns: *mut ()) {
        ffi_call(
            &self.calling_convention as *const _ as *mut _,
            Some(std::mem::transmute(self.ptr)),
            returns.cast(),
            data.cast(),
        );
    }
}

/// Converts a compiler type into a libffi type. This might fail if the type
/// is zero sized!
fn type_to_ffi_type(alloc: &Bump, type_: Type) -> Option<ffi_type> {
    // Safety: These statics should not be modified ever, I don't know why they are mutable statics.
    unsafe {
        match type_.kind() {
            TypeKind::Empty => None,
            TypeKind::U8 => Some(ffi_type_uint8),
            TypeKind::I64 => Some(ffi_type_sint64),
            TypeKind::F64 => Some(ffi_type_double),
            TypeKind::Reference(_) => Some(ffi_type_pointer),
            TypeKind::Function { .. } => todo!("Function pointers are not supported in FFI yet, because function pointers in the compile time execution part of things are not represented like they would be in other languages; this is a problem, and it means I'll have to change the way that functions are represented. The solution I'll come up with is probably to split functions into 'extern fn' and 'fn'. 'extern' fns will always just be a function poitner that can be called directly with libffi, while 'fn' will be a different kind of thing that is called by just running it with the interpreter."),
            TypeKind::Struct(members) => {
                todo!("Struct ffi is not implemented yet");
            }
        }
    }
}
