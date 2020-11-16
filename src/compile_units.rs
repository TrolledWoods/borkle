use crate::errors::ErrorCtx;
use crate::location::Location;
use parking_lot::RwLock;
use std::collections::HashMap;
use std::path::PathBuf;

pub struct CompileUnitId(u32);

#[derive(Default)]
pub struct CompileUnits {
    files: RwLock<Vec<PathBuf>>,
    units: RwLock<HashMap<u32, RwLock<Unit>>>,
}

impl CompileUnits {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn add_file(&self, path: PathBuf) {
        let mut files = self.files.write();
        files.push(path);
    }

    /// Runs a single unit of work.
    ///
    /// Returns Ok(true) if there is more work, returns
    /// Ok(false) if there is no more work
    pub fn bump(&self, errors: &mut ErrorCtx) -> Result<bool, ()> {
        if let Some(path) = self.files.write().pop() {
            let file_name = path.to_str().unwrap().into();
            let file_contents = match std::fs::read_to_string(path) {
                Ok(contents) => contents,
                Err(err) => {
                    errors.global_error(format!("{:?}", err));
                    return Err(());
                }
            };
            let output = crate::parser::process_string(errors, file_name, &file_contents)?;
            println!("{:#?}", output);
            Ok(true)
        } else {
            // In this case we are done
            Ok(false)
        }
    }
}

pub struct File {
    pub path: PathBuf,
    // pub scope: ScopeId,
}

pub struct Unit {
    loc: Location,
    kind: UnitKind,
}

/// Contains temporary data associated with stages
/// of compilation. Permanent data that can be depended upon
/// should be stored in the [`Unit`]]]]]]]]] struct.
pub enum UnitKind {
    Parsed(crate::parser::Ast),
    Done,
}
