# borkle
A compiler/interpreter for a homemade programming language.
It can compile to c code, or run the program in an interpreted mode.

This is not stable software, and it might have very bad bugs and change at any time.

## Command line arguments
* ``--file <path>`` (default value "src.bo") The path to the file to compile.
* ``--output <path>`` (default value "target/") The directory where generated c code will be put.
* ``--release`` If this is set c code will be generated, otherwise the code will be interpreted.
* ``--num_threads <number>`` (default value 3) The number of threads the compiler will use.

When compiling in release an ``output.c`` file will be generated in the output directory.

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

Now you say; I want a "Hello world" program! Unfortunately, there is not yet a built in way to print things. So let me show you how you could make a hello world.

## FFI
This language has ffi, both a compile time and at run time. To load an ffi value, you can use the ``extern`` keyword;

```rust
const print = extern "some_random_ffi_library" "print" : extern fn (string: [] u8);
```
There is a lot of stuff here, so let's break it down; ``some_random_ffi_library`` is the path to a dynamic library(the file extension is inserted automatically based on your operating system), ``print`` is the symbol in that library you want to load.

Since you can't know what type something is just from the information in the dynamic library, you have to type bound the extern to tell it what type ``print`` is. ``extern fn`` specifies that the function is an external ffi function. ``[] u8`` is a buffer of bytes(u8), which is what strings are.

So, if you have a library that provides a print function, this is what hello world might look like;
```rust
const main = fn() -> u64 {
    print("Hello, world!\n");
    0
};

const print = extern "some_random_ffi_library" "print" : extern fn (string: [] u8);
```
Of course, when you compile the generated c code you have to link the library with the c compiler as well.

This is all I'll write for now, later there might be more documentation on how the language works, and also examples of programs in it.
