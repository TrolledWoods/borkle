# borkle
A compiler/interpreter for a homemade programming language.
It can compile to c code, or run the program in an interpreted mode.

This is not stable software, and it might have very bad bugs and change at any time.

## Building
There are two things you need to build. First, you have to build the compiler, which you can just do with cargo. Then, you have to also build the standard library for borkle, if you want to use it that is. The ``library/build.bat`` file invokes rustc to build it for you, so if you just run that it should work out.

## Command line arguments
* ``--file <path>`` (default value "src.bo") The path to the file to compile.
* ``--output <path>`` (default value "target/") The directory where generated c code will be put.
* ``--release`` If this is set c code will be generated, otherwise the code will be interpreted.
* ``--num_threads <number>`` (default value 3) The number of threads the compiler will use.
* There are more, run ``borkle --help`` to get information about them

When compiling in release, all the dll:s from libraries used will be copied into the output directory,
an ``output.c`` file will be generated there, and the specified c compiler will be run to commpile the c code.

## Examples
Look in the ``examples`` directory for example programs. As long as you have compiled the dynamic library the standard
library depends on, you should be able to run these by just running borkle inside of their respective folders.

## Programming language
The language is still heavily work in progress, but some features are fairly complete;

The language is strongly typed, which means that all values have to know their types at compile time
and can't change their types randomly; even when not outputting c code.

The type of an expression can be specified with a type bound, ``<expression> : <type>``.

Example:
```rust
42 : i64
```
This expression creates a signed 64 bit integer with the value ``42``.

Common operators like addition and multiplication are also implemented for integers.
```rust
42 + 30 : i64 // A signed 64 bit integer with value 72
```

If you want to make more complex expressions with operators that have different priority, like mixing addition and multiplication, you have to wrap one of the operators in parenthesees.
```rust
42 + (15 * 2) : i64 // Same as previous example
```

Blocks are also expressions. A block returns the last expression inside of it if that expression does not have a trailing semicolon. If it does have a trailing semicolon, the block returns the empty type, ``()``.
```rust
{
    42 + (15 * 2) : i64 // This is returned from the block
}
```

In blocks you can declare variables with ``let``. You specify the type of a variable with a type bound on the expression you initialize it to.
```rust
{
    let thirty = 15 * 2 : i64;
    42 + thirty : i64
}
```

Now, just expressions are not valid programs by themselves. Programs in borkle are based around constants. Constants are values that are computed at compile time, and the order of them does not matter. The entire language is supported at compile time.
```rust
const seventy_two = {
    let thirty = 15 * 2 : i64;
    42 + thirty : i64
};
```

Functions are also just constants, but you assign a function to them.
```rust
const add_two_numbers = fn(a: i64, b: i64) -> i64  a + b;
```

The syntax of a function declaration is ``fn(arg_0: type, arg_1: type, arg_3: type,) -> return_type  function_body_expression``.
If you don't want to return anything, you can simply omit the ``-> return_type`` part of the declaration.
Of course, since code blocks are also expressions, it's fine to use a code block as the function body as well.

However, even with constants we don't have a valid program yet. No, for a program to be valid there has to exist a specific
constant, ``main``, which has to be of the type ``fn() -> u64``. That is the entry point of our program, and it is the equivalent of ``int main()`` in c.

```rust
const main = fn() -> u64 {
    answer
};

const answer = 42 : u64;
```
This is a valid borkle program; we have a constant ``main`` which is the correct type. Here it's also demonstrated how constants can be in any order; we can use ``answer`` in ``main`` even though it's declared later on.

Now you say, quit it with the boring stuff, give me a hello world program!

## Hello world
```rust
library "io.bo";

const main = fn() -> u64 {
    put_string("Hello, world!\n");
};
```
Here, we import the "put\_string" function by importing the "io.bo" file. ``library`` just imports a file relative to the ``lib_path``. This also means that you can look at the definition of "put\_string":

```rust
const put_string = fn (buffer: [] u8) -> u64 {
    (extern "target/library" "put_string" : extern fn(&u8, usize) -> u64)
        (buffer.ptr, buffer.len)
};
```
Wow that's ugly. Anyway, put\_string calls an FFI function to do its magic.

Now you're wondering, why aren't you using ``printf`` or something!? ``print`` does indeed exist, but it does formatting,
so calling it is a bit more complicated than ``put_string``.

There is more documentation to come later, but take a look at the examples if you want to see more of how the language works.
The examples may not be up to date, because keeping them all up to date constantly as I work on the language would be a huge pain.
