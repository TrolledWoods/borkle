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
    #[derive(Debug)]
    struct Arguments {
        file: String = "testing.bo";
            "The file to compile",

        output: String = "target/borkle";
            "The folder to put output files into",

        release: bool = false;
            "If set to true, c code will be emitted",

        c_compiler: String = "gcc";
            "The name of the command to invoke a c compiler",

        num_threads: usize = 3_usize;
            "The number of threads to use for compilation",
    }
);
