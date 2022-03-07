use std::path::{Path, PathBuf};
use std::io::{self, Write};

const SETTINGS_HEADER: &str = 
r#"# Settings file for the borkle compiler
# Starting a line with `#` makes a comment.
"#;

#[derive(Debug, Clone)]
pub struct Arguments {
    pub file: PathBuf,
    pub lib_path: PathBuf,
    pub threads: usize,
    pub debug: bool,
    pub debug_asm_output: bool,
    pub builtins: bool,
}

#[derive(Default)]
struct ArgumentsBuilder {
    file: Option<PathBuf>,
    lib_path: Option<PathBuf>,
    threads: Option<usize>,
    debug: Option<bool>,
    debug_asm_output: Option<bool>,
    builtins: Option<bool>,
}

fn read_argument(arguments: &mut ArgumentsBuilder, strings: &mut dyn Iterator<Item = &str>) -> Result<(), String> {
    let arg_name = strings.next().ok_or("Expected argument name")?;

    match arg_name {
        "file" => {
            let file = strings.next().ok_or_else(|| "Argument `file` expects a filename")?;
            arguments.file.get_or_insert_with(|| file.to_string().into());
        }
        "lib_path" => {
            let file = strings.next().ok_or_else(|| "Argument `lib_path` expects a filename")?;
            arguments.lib_path.get_or_insert_with(|| file.to_string().into());
        }
        "threads" => {
            let number = strings
                .next()
                .ok_or_else(|| "Argument `threads` expects a number")?
                .parse()
                .map_err(|_| "Argument given to `threads` isn't a number")?;

            arguments.threads.get_or_insert(number);
        }
        "debug" => { arguments.debug.get_or_insert(true); },
        "!debug" => { arguments.debug.get_or_insert(false); },
        "debug_asm_output" => { arguments.debug_asm_output.get_or_insert(true); },
        "!debug_asm_output" => { arguments.debug_asm_output.get_or_insert(false); },
        "builtins" => { arguments.builtins.get_or_insert(true); },
        "!builtins" => { arguments.builtins.get_or_insert(false); },
        _ => {
            return Err(format!("Unknown argument `{}`", arg_name));
        }
    }

    Ok(())
}

fn save_arguments(path: &Path, builder: &ArgumentsBuilder) -> io::Result<()> {
    let mut out = std::fs::File::create(path)?;

    writeln!(&mut out, "# Default compiler settings")?;

    if let Some(ref file) = builder.file {
        writeln!(&mut out, "file {}", file.display())?;
    }
    if let Some(ref lib_path) = builder.lib_path {
        writeln!(&mut out, "lib_path {}", lib_path.display())?;
    }
    if let Some(threads) = builder.threads {
        writeln!(&mut out, "threads {}", threads)?;
    }
    if let Some(debug) = builder.debug {
        if debug {
            writeln!(&mut out, "debug")?;
        } else {
            writeln!(&mut out, "!debug")?;
        }
    }
    if let Some(debug) = builder.debug_asm_output {
        if debug {
            writeln!(&mut out, "debug_asm_output")?;
        } else {
            writeln!(&mut out, "!debug_asm_output")?;
        }
    }
    if let Some(debug) = builder.builtins {
        if debug {
            writeln!(&mut out, "builtins")?;
        } else {
            writeln!(&mut out, "!builtins")?;
        }
    }

    drop(out);

    Ok(())
}

fn read_arguments_from_global_file(arguments: &mut ArgumentsBuilder) -> Option<()> {
    let mut path = std::env::current_exe().ok()?;
    path.pop();
    path.push("settings.txt");

    let file_contents = match std::fs::read_to_string(&path) {
        Ok(v) => v,
        Err(_) => {
            eprintln!("No settings file found, so creating it");
            // Create default file, so that it's easy to know where it should be for the compiler to find it.
            let mut file = std::fs::File::create(path).ok()?;
            writeln!(&mut file, "{}", SETTINGS_HEADER).ok()?;
            
            return None;
        }
    };

    for (line_number, line) in file_contents
        .lines()
        .enumerate()
        .map(|(i, v)| (i + 1, v.trim()))
        .filter(|(_, v)| !v.is_empty())
    {
        if line.starts_with("#") {
            continue;
        }

        let result = read_argument(arguments, &mut line.split_whitespace());

        if let Err(msg) = result {
            eprintln!("`{}:{}`: {}", path.display(), line_number, msg);
        }
    }

    Some(())
}

fn read_remaining_as_defaults(arguments: ArgumentsBuilder) -> Arguments {
    Arguments {
        file: arguments.file.unwrap_or_else(|| PathBuf::from("src.bo".to_string())),
        lib_path:  arguments.lib_path.unwrap_or_else(|| {
            let mut path = std::env::current_exe().expect("We have to be able to locate the executable");
            path.pop(); // Pop the executable
            path.push("library");
            path
        }),
        debug_asm_output: arguments.debug_asm_output.unwrap_or(false),
        debug: arguments.debug.unwrap_or(false),
        builtins: arguments.builtins.unwrap_or(true),
        threads: arguments.threads.unwrap_or(4),
    }
}

pub fn read_arguments() -> Option<Arguments> {
    let mut builder = ArgumentsBuilder::default();

    read_arguments_from_global_file(&mut builder)?;

    Some(read_remaining_as_defaults(builder))
}
