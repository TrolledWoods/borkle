# Version 0.0.2
* [X] Struct types
* [X] Type definitions
* [X] References of temporary values
* [X] Improved naming in Program.
* [X] Defer
* [X] Optimize stack size for interpreter
* [X] Break out of blocks/loops
* [X] Redo ast nodes to be more readable
* [X] Constant folding of operations
* [X] Anonymous constants. Should these use 'const' keyword or something else, like jai's #run directive for example.
* [X] Allow constants to "extract" extra metadata from typer nodes, such as default parameters to functions for example.
        To test this, default value function parameters are also added.
* [X] Name arguments when calling a function, and default arguments.
* [X] Taking a reference does an autocast as well
* [X] Change the type inference system to allow for more nuanced things, since right now it's cracking at the seems.
* [X] Put the emitter context in a different function and make zst type checks for all of them.
* [X] BUG! Seems like empty array literals can be of any type, even though they should only be arrays.
* [X] BUG! There is a bug with variable shadowing
* [X] If break \<label\> is followed by a ';', then just break with the Empty type.
* [X] Figure out why ifs with loose expressions after them never seem to work.
* [X] Allow array types to contain arbitrary length expressions
* [X] Allow array literals to also become buffers if the wanted type needs it.
* [X] Ranges
* [X] For loops
* [X] Make sure certain types of values are "alone" in an expression.
* [X] Meta data is kept when aliasing
* [X] Nice error message formatting
* [X] 'Any' type, the same as C void\*
    (do we want it to behave this way or do we want 'Any' to use a type id, and have some other type that works like c void)
* [X] 'Any' buffer type.
* [X] for/while loops have else clauses
* [X] for/while loops have labels
* [X] breaks that don't jump to a named labels
* [X] \_iteration variable in loops that shows how many times the loop has iterated

* [ ] Make assignment an expression.
* [ ] Make a global setup file for the compiler!
* [ ] Add a flag to types that are not storable in constants.
* [ ] BUG! Parsing ambiguity error is not resolved even after adding parenthesees
* [ ] When a file cannot be loaded, show where the task was queued.

# Version 0.0.3
* [ ] Compile time functions
* [ ] Functions for constructing types programmatically at compile time
* [ ] Polymorphism
* [ ] Implement the proper separation between 'thread pool' and 'program'
* [ ] If the dynamic library in the target directory is already defined, and has the same "last edited" date as the source file, don't copy the file from the source.
* [ ] Struct literals
* [ ] Structs in ffi
* [ ] Figure out if there is a way to have fewer keywords.
* [ ] Make locals/labels use pure register ids instead of values, since they are never going to be global anyway
* [ ] Add overflow checks to type size calculations, and add a user level error for trying to create too large types.
* [ ] Use the never type to find dead code, and allow casting from it to anything.
* [ ] Indexing operations
