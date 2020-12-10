# Version 0.0.2
* [X] Struct types
* [X] Type definitions
* [X] References of temporary values
* [X] Improved naming in Program.
* [X] Defer
* [X] Optimize stack size for interpreter
* [X] Break out of blocks/loops

* [ ] In emit.rs, don't pass nodes by reference but by value instead
* [ ] Never type
* [ ] Make locals/labels use pure register ids instead of values, since they are never going to be global anyway
* [ ] Polymorphism
* [ ] Anonymous constants
* [ ] Figure out if there is a way to have fewer keywords.
* [ ] BUG! There is a bug with variable shadowing
* [ ] If the dynamic library in the target directory is already defined, and has the same "last edited" date as the source file, don't copy the file from the source.
* [ ] Allow running the examples folder as tests
* [ ] Make a global setup file for the compiler!
* [ ] Struct literals
* [ ] Structs in ffi
* [ ] Indexing operations
* [ ] Implement the proper separation between 'thread pool' and 'program'
* [ ] Redo ast nodes to be more readable, like right now what the heck is it even!? 
        Maybe it's fine to use unsafe, because if we do we can also include other data types in the ast buffer.
* [ ] Allow array literals to also become buffers if the wanted type needs it.
* [ ] For loops
* [ ] Function arguments are implicitly dereferenced/referenced(maybe we want this?)
* [ ] 'Any' type, the same as C void\*
    (do we want it to behave this way or do we want 'Any' to use a type id, and have some other type that works like c void)
* [ ] Change the type inference system to allow for more nuanced things, since right now it's cracking at the seems.

# Version 0.0.3
* [ ] Compile time functions
* [ ] Functions for constructing types programmatically at compile time
