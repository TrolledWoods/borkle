# borkle
A compiler/interpreter for a homemade programming language.
It can compile to x86 assembly, or run the program in an interpreted mode.

This is not stable software, and it might have very bad bugs or change at any time.

## Building
Just build with cargo, like any other rust program.

## Command line arguments
Run with the ``--help`` command to see the information. To do this with cargo, type `cargo run -- --help`.

## Examples
There are are a number of test programs in the `tests` directory that should be up to date.

You can also look in the `library` directory to look at how the standard library is implemented.

## Hello World
Because every language needs a hello world program, here is the one for borkle:
```rust
print("Hello, world!\n");
```
However, this is cheating, because code written in global scope like this ends up being interpreted.

To get a compiled hello world, you have to do this:
```rust
create_exe("some_file_name.exe", fn() print("Hello, world!\n"));
```
