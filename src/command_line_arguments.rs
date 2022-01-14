use std::path::PathBuf;
use std::str::FromStr;

#[derive(Debug)]
pub enum Error {
    InvalidArgNumber {
        expected_number: Option<usize>,
        recieved_number: usize,
    },
    UnknownArgument,
    InvalidData(String),
}

trait Argument: Sized {
    fn parse(input: &[&str]) -> Result<Self, Error>;
}

fn parse_from_str<T>(input: &[&str]) -> Result<T, Error>
where
    T: FromStr,
{
    if let [string] = *input {
        string
            .parse()
            .map_err(|_| Error::InvalidData(string.to_string()))
    } else {
        Err(Error::InvalidArgNumber {
            expected_number: Some(1),
            recieved_number: input.len(),
        })
    }
}

macro_rules! impl_argument_with_from_str {
    ($type_:ty) => {
        impl Argument for $type_ {
            fn parse(input: &[&str]) -> Result<Self, Error> {
                parse_from_str(input)
            }
        }
    };
}

impl_argument_with_from_str!(u8);
impl_argument_with_from_str!(u16);
impl_argument_with_from_str!(u32);
impl_argument_with_from_str!(u64);
impl_argument_with_from_str!(i8);
impl_argument_with_from_str!(i16);
impl_argument_with_from_str!(i32);
impl_argument_with_from_str!(i64);
impl_argument_with_from_str!(usize);
impl_argument_with_from_str!(isize);
impl_argument_with_from_str!(f32);
impl_argument_with_from_str!(f64);
impl_argument_with_from_str!(String);
impl_argument_with_from_str!(PathBuf);

impl Argument for bool {
    fn parse(input: &[&str]) -> Result<Self, Error> {
        if input.is_empty() {
            Ok(true)
        } else {
            Err(Error::InvalidArgNumber {
                expected_number: Some(0),
                recieved_number: input.len(),
            })
        }
    }
}

macro_rules! create_arguments {
    ($(#[$meta_data:meta])* struct $name:ident { $($field_name:ident: $field_type:ty = $field_value:expr; $field_description:tt),*, }) => {
        $(#[$meta_data])*
        pub struct $name {
            $(
                pub $field_name: $field_type,
            )*
        }

        impl $name {
            pub fn set_argument(&mut self, name: &str, data: &[&str]) -> Result<(), Error> {
                match name {
                    $(
                        stringify!($field_name) =>
                            self.$field_name = <$field_type as Argument>::parse(data)?,
                    )*
                    _ => return Err(Error::UnknownArgument),
                }

                Ok(())
            }

            pub fn from_args(args: &[&str]) -> Option<Self> {
                let mut creating = Self {
                    $(
                        $field_name: $field_value.into(),
                    )*
                };

                let mut argument = None;
                let mut success = true;
                for (i, arg) in args.iter().enumerate() {
                    // A start of a new set of things
                    if let Some(name) = arg.strip_prefix("--") {
                        if name == "help" {
                            success = false;

                            println!("# Help information:");
                            $(
                                println!("'{}': {}", stringify!($field_name), $field_description);
                                println!("   (default: {:?})", $field_value);
                            )*
                        } else {
                            if let Some((name, start)) = argument.take() {
                                if let Err(err) = creating.set_argument(name, &args[start..i]) {
                                    println!("['{}']: {:?}", name, err);
                                    success = false;
                                }
                            }

                            argument = Some((name, i + 1));
                        }
                    } else if argument.is_none() {
                        println!("'{}' is not an argument, arguments have to be prefixed by '--'", arg);
                        success = false;
                    }
                }

                if let Some((name, start)) = argument.take() {
                    if let Err(err) = creating.set_argument(name, &args[start..]) {
                        println!("['{}']: {:?}", name, err);
                        success = false;
                    }
                }

                if success {
                    Some(creating)
                } else {
                    None
                }
            }
        }
    }
}

create_arguments!(
    #[derive(Debug, Clone)]
    struct Arguments {
        file: PathBuf = "src.bo";
            "The file to compile",

        run: bool = false;
            "If this is set, the compiler will run the entry point using the interpreter.",

        output: PathBuf = "target/";
            "The folder to put output files into",

        lib_path: PathBuf = {
            let mut path = std::env::current_exe().expect("We have to be able to locate the executable");
            path.pop(); // Pop the executable
            path.pop(); // Pop the debug/release folder
            path.pop(); // Pop the target folder
            path.push("library");
            path
        };
            "The folder where global libraries are stored",

        c_compiler: String = "clang";
            "The c compiler to use",
        output_c: bool = false;
            "If set to true, c code will be emitted",
        compile_c: bool = true;
            "If set to true, the emitted c code will be compiled using the given c compiler",

        c_path: PathBuf = "target/output.c";
            "If set to true, c code will be emitted",
        exe_path: PathBuf = "target/output.exe";
            "The path of the executable",

        x64_path: PathBuf = "target/output.asm";
            "The path where the x64 file should be created",
        output_x64: bool = true;
            "If set to true, a file containing x64 will be emitted",
        debug_asm_output: bool = false;
            "Internal compiler debugging option, debug symbols will be generated for the assembly itself to debug it",

        ir_path: PathBuf = "target/output.bir";
            "The path where the ir file should be created",
        output_ir: bool = false;
            "If set to true, a file containing ir will be emitted",

        debug: bool = true;
            "Whether or not debug information will be emitted(very basic, just prints the locations of the nodes that are run for now)",

        num_threads: usize = 1_usize;
            "The number of threads to use for compilation",
    }
);
