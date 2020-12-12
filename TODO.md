# Version 0.0.2
* [X] Struct types
* [X] Type definitions
* [X] References of temporary values
* [X] Improved naming in Program.
* [X] Defer
* [X] Optimize stack size for interpreter
* [X] Break out of blocks/loops
* [X] Redo ast nodes to be more readable
* [ ] Constant folding of operations

* [ ] Allow array types to contain arbitrary length expressions
* [ ] BUG! Seems like empty array literals can be of any type, even though they should only be arrays.
* [ ] Make a separate ast node kind for type expressions?
* [ ] Figure out why ifs with loose expressions after them never seem to work.
* [ ] If break \<label\> is followed by a ';', then just break with the Empty type.
* [ ] In emit.rs, don't pass nodes by reference but by value instead
* [ ] Never type
* [ ] Make locals/labels use pure register ids instead of values, since they are never going to be global anyway
* [ ] Polymorphism
* [ ] Anonymous constants. Should these use 'const' keyword or something else, like jai's #run directive for example.
* [ ] Figure out if there is a way to have fewer keywords.
* [ ] BUG! There is a bug with variable shadowing
* [ ] If the dynamic library in the target directory is already defined, and has the same "last edited" date as the source file, don't copy the file from the source.
* [ ] Allow running the examples folder as tests
* [ ] Make a global setup file for the compiler!
* [ ] Struct literals
* [ ] Structs in ffi
* [ ] Indexing operations
* [ ] Implement the proper separation between 'thread pool' and 'program'
* [ ] Allow array literals to also become buffers if the wanted type needs it.
* [ ] For loops
* [ ] Function arguments are implicitly dereferenced/referenced(maybe we want this?)
* [ ] 'Any' type, the same as C void\*
    (do we want it to behave this way or do we want 'Any' to use a type id, and have some other type that works like c void)
* [ ] Change the type inference system to allow for more nuanced things, since right now it's cracking at the seems.

# Version 0.0.3
* [ ] Compile time functions
* [ ] Functions for constructing types programmatically at compile time
