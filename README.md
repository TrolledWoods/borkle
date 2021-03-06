# borkle
A compiler/interpreter for a homemade programming language.
It can compile to c code, or run the program in an interpreted mode.

This is not stable software, and it might have very bad bugs and change at any time.

## Building
Just build with cargo, like any other rust program.
** DISCLAIMER ** There is no support for 32-bit systems right now.

## Command line arguments
Run with the ``--help`` flag to print up-to-date information. To do this with cargo, type ``cargo run -- --help``.

## Examples
Look in the ``examples`` directory for example programs. A lot of these are not up-to-date with the latest version, but concepts should cary across at least.

In the ``library`` directory there are more up-to-date examples, these are also the library files you can import with the ``library`` command. However, since these are library files and not full programs their utility as examples is questionable I think.

There is also a ``src.bo`` file, this is mostly for just quickly checking that the compiler somewhat works while developing it, but it's a good up to date small example file as well.

## Hello World
Because every language needs a hello world program, here is the one for borkle:
```rust
library "fmt.bo";

#entry fn() -> u64 {
    print("Hello, world!\n");
    0
};
```
Of course, this may change heavily in the future! For example, the entry point will probably not have to return a ``u64`` number in the future, but for now it has to.

## Syntax
Borkle has an odd syntax, the philosophy behind it is nothing more than "I kinda like this, let's steal it". To start, let's do some sample expressions and what they evaluate to.

``42`` This evaluates to the number "42", and the type ``i32``, which is a signed 32 bit integer. That is the default type for integer literals at the moment, though it might be changed to 64 bit signed integer in the future, not sure.

``42 + 10`` This evaluates to "52", and again the type ``i32``.

``42 + 10 * 5`` This evaluates to... no... this doesn't compile. Why? Because of a syntax decision I made! I decided that in order to avoid ambiguity about order of operations you have to wrap operators in parenthesees, like this; ``42 + (10 * 5)``. However, it's not as bad as it seems, if the operators have the same priority you can still just do ``42 + 10 - 2`` for example.

What if we want something other than an ``i32``? Well, we can add a type bound to our expression, like this; ``42 + (10 * 5) : u64``. This will create a ``u64``, an unsigned 64 bit integer. Type bounds are a very fundamental feature of borkle, so you'll see it a lot!

``"Hello, world!\n"`` Your standard issue string literal, nothing too special about it. It is of type ``[] u8``, what I call a "buffer type". A buffer is just a pointer and a length. This also means strings in borkle are not null terminated.

``"a" : u8`` This is a character literal. It's also just a string literal, but it is specified to be of the type ``u8``, i.e. a byte.

Okay, now we have a small feel for how expressions look in borkle. One more thing before I go on to bigger examples; ``//`` is a comment, just like in every c style language.

Now the tutorial continues in comment form.

```rust
library "fmt.bo";
library "mem.bo";

#entry fn() -> u64 {
    // This is our hello world example again, so I can show you around a bit.
    print("Hello, world!\n");

    // You can declare variables in a block with the ``let`` keyword, like this:
    // All declarations require an expression to the right, and the type of the
    // expression is the type of the variable.
    let x = 5;

    // What if you want to only declare a variable? You use the ``#uninit`` 
    // initializer
    let uninitialized = #uninit : i32;

    // Like in C, we can take pointers to variables on the stack.
    // (the type bound here is unnecessary, it's just to show how the type looks)
    let pointer_to_x = &x : &i32;

    // You can offset pointers. The type of integer you offset with is called
    // ``usize``, it's an integer the size of a pointer.
    // The offset not in bytes, but in elements of the thing behind the pointer,
    // in this case we offset it by 4 bytes.
    let added_pointer = pointer_to_x + 1;

    // If you want a null pointer, you can use the ``#0`` initializer. This just
    // sets all the bytes in the type to zero. You can use it for any type.
    let null_pointer = #0 : &i16;

    // Let's allocate 512 bytes of memory. The ``alloc`` function is defined in the
    // ``mem.bo`` library. The type ``alloc`` returns is a buffer of any, similar
    // to a ``void *`` in c, but it knows the length of allocation. The power
    // of this type is that you can cast it to any other buffer type, and it will
    // calculate the correct length.
    let memory_block = alloc(512) : [] any;

    // We can also deallocate the block here, with a defer. The defer will run the code
    // inside of it right before the current scope is exited.
    defer dealloc(memory_block);

    // ``<<`` is how you cast, and here we cast the ``memory_block`` to a
    // buffer of u8.
    let u8_block = << memory_block : [] u8;

    // Here we instead cast the ``memory_block`` to a buffer of ``u64``.
    let u64_block = << memory_block : [] u64;

    // We can get the lengths of our blocks by accessing the ``len`` fields
    // on them.
    let u8_block_len = u8_block.len;
    let u64_block_len = u64_block.len;
    // Here, ``u8_block_len`` will be 512, while the ``u64_block_len`` will be 64.

    // Let's say we now want to initialize our memory block to zero. We can do this
    // with a for loop!
    for u8_block { // NOTE: The block here isn't meant to be necessary, but because of a parser limitation it is for now.
        *_it = 0;
    };
    // This is a very strange for loop probably coming from other languages.
    // What's happening is we are iterating over the ``u8_block``. By default, for loops
    // use ``_it`` as the iteration variable, and sets this to pointers to the values
    // in the buffer you're iterating over.

    // What if we want do something more interesting, like setting the first element to
    // 0, the second element to 1, e.t.c.
    // We can do this with a for loop also, but with the u8 buffer we will run out of
    // space in the u8, since u8 only stores up to 255, while the length of our buffer
    // is 512 bytes! So let's use the u64_block instead(it's still the same memory, just
    // a different 'interpretation' of that memory).
    let num = 0 : u64;
    for u64_block {
        *_it = num;
        num = num + 1; // This is temporary, += is not implemented yet
    };

    // One thing to note is that ``for`` loops also require a semicolon after them.
    // The reason is simple; for loops are also expressions, they just return the ``()``
    // type(a.k.a the empty type).

    // Anyway, that's all well and good, but there is a built in feature that can help
    // us make this even more concise. I mentioned that for loops implicitly define the
    // ``_it`` variable, but it also defined a variable called ``_iters``, which just
    // starts at 0 at the first iteration, becomes 1 at the second iteration e.t.c,
    // exactly like the ``num`` variable in our prevoius for loop!

    // One minor hickup though is that this variable is of type ``usize``, so we're going
    // to have to cast them.
    for u64_block {
        *_it = bit_cast _iters;
    };
    // bit_cast is a cast that just reinterprets the bits. It requires the types it's casting
    // between to be the same size, but other than that there is no restriction.

    // Also, just in case you're worried, the ``_iters`` variable is only created if you use it.

    // If you want, you can also name the ``_it`` variable to something different, like this;
    for number in u64_block {
        *number = bit_cast _iters;
    };

    // Time to go on a bit of a different journey; blocks!
    {
        // This is a block.
        // Blocks are essentially just lists of expressions that run one after another,
        // separated by semicolons, ``;``.

        // Blocks are also scopes. Remember ``defer`` earlier? If I create a defer
        // in this block, it will run right before we exit this block.

        // Blocks are also expressions, they return the last expression in them, as long as
        // that expression does not have an ending semicolon. If it does, the block instead
        // returns the empty type, ``()``.

        let variable = {
            59
        };
    };

    // I can name a block
    { 'name_of_my_block
        // If I have named a block, I can break out of it.
        break 'name_of_my_block; // This break jumps to the end of the block
        // Note: ``defer`` code also runs before breaks out of the block.
    };

    // If my block returns a value, breaks can also pass values.
    let value = { 'the_block
        break 'the_block 4;

        2
    };

    // You can also break out of loops.
    // This for loop is a for loop over a range, it will iterate from 0 up to 10, but not
    // including 10.
    for 'my_for_loop 0 .. 10 {
        break 'my_for_loop;
    };

    // If you do not pass a name to ``break`` it will break the closest loop.
    // This is equivalent to the for loop above.
    for 0 .. 10 {
        break;
    };

    // You may have noticed everything is an expressions, well, loops are too. However,
    // usually they only return the ``()`` type. However, if you give them an
    // ``else`` block, they can return values.
    //
    // How this works is this; if the loop exits normally, i.e. by its condition becoming
    // false or by it having iterated over all the values in a range or buffer, it will
    // run the else block and return the value from that. However, if you break out of the
    // for loop, the break will provide the value and the else block will be skipped.
    let from_for_loop = for 0 .. 10 {
    } else {
        5
    };

    // Of course, if there are for loops, there are while loops.
    // while loops also have else blocks, the implicit ``_iters`` variable, you can break
    // out of them, you can name them, e.t.c.
    // This while loop will iterate 10 times. while loops do not have an
    // ``_it`` variable though, because it doesn't iterate over anything.
    while _iters < 10 {};

    // Now, just to be different, we will enter constant land, and look at ways
    // to create a function.

    0 // (and don't forget to return the ``u64`` from the entry point)
};

// A constant is just defined with the ``const`` keyword, and they are unordered, meaning
// you can access a constant defined below another constant.
const SOME_CONSTANT = 5;

// Constants are evaluated at compile time, but the full language is supported in them.
// Anyway, let's make some functions! Function declarations are just expressions like
// everything else, so to make a function you declare a constant to a function declaration.
const print_hello = fn()  print("Hello\n");

// This is a very simple function just to get started; it has no arguments and no return
// values. As you can see, you do not need a block around the function body, as it is
// just an expression(like everything else).

// This is a bit more of a complex function, that adds two numbers.
const add_numbers = fn(a: i32, b: i32) -> i32  a + b;

// We can call functions like in most languages. There is no function overloading, so
// the argument types can easily be inferred, so you do not have to specify the types
// of the integers here for example.
const THE_ANSWER = add_numbers(10, 32);

// However, you can also specify the names of the arguments. When you do this the order
// no longer matters, you can pass arguments in any order you want.
const THE_ANSWER_AGAIN = add_numbers(b = 10, a = 32);

// We can declare a function with default arguments too.
const add_more_numbers = fn(a: i32, b = 0 : i32, c = 0 : i32, d = 0 : i32) -> i32
    a + b + c + d;

// So now all of these are valid
const TWO_ADDED = add_more_numbers(1, 2);
const THREE_ADDED = add_more_numbers(1, 2, 3);
const FOUR_ADDED = add_more_numbers(1, 2, 3, 4);

// You can mix named arguments and default arguments to only override a specific default
// argument, and leave the rest untouched.
const ADDED_STRANGE = add_more_numbers(1, c = 9);
```

That's it for now! There may be more documentation later. Some things that weren't covered; if, types as values, structs, &any type.

You can look in the ``library/`` directory for somewhat up-to-date files that you can import into your borkle program with ``library "library_file.bo";``
