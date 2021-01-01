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
* [X] Variables know how many times they have been used
* [X] Code for the \_iters variable is only generated if it is used.
* [X] Custom printing for intermediate representation
* [X] BUG! Parsing ambiguity error is not resolved even after adding parenthesees
* [X] Zeroed values
* [X] Auto dereference things when taking a member.
* [X] BUG! Problem when doing something like &(\*value).member\_name
* [X] Hexadecimal integers
* [X] Make 'namespaces', i.e. only imported files are in scope, they do not indirectly pollute scopes like they do right now
* [X] Error for having two #entry points
* [X] Add a flag to types that are not storable in constants.
* [X] Make put\_string, read\_line, read\_file e.t.c. built into the compiler(though lower level equivalents)
* [X] When a file cannot be loaded, show where the task was queued.
* [X] BUG! extern still uses relative paths I think, that's a bug.
* [X] BUG! Some files are still imported twice! Fix this by converting all paths to absolute paths first, so that there is no ambiguity as to which file something is
* [X] BUG! Indirect members do not handle ZST:s yet.
* [X] Cleaned up some stuff in the Program
* [X] Look into reducing the amount of recursion, the stack can overflow quite easily at the moment!

# Version 0.0.1
* [X] Simple control flow, if, while.
* [X] Buffer pointer type
* [X] Pointers in globals
* [X] Fix bug where things try to be computed without dependencies
* [X] Deduplicated constants can have the wrong alignment
        (do we want something more 'proper' than just forcing alignment to be 8?)
* [X] Array types
* [X] String literals
* [X] Generalise operators
* [X] Make if use booleans
* [X] Add error for unresolved dependencies
* [X] Check for duplicate constants
* [X] Command line arguments
* [X] Optional logging
* [X] C backend
* [X] Bug! Extern functions break when stored in constants
* [X] Reimplement deduplication for constants
* [X] Implement lvalue members in c backend
* [X] Auto casts
* [X] Pointer offset operators
* [X] Array literals
* [X] Make comparison operators care about sign bits
* [X] File imports
* [X] Make a readme file
* [X] BUG! Pointer to zst doesn't work
* [X] Add floating point literals and types
* [X] BUG! Pointer to members do not seem to work properly
* [X] Make paths(for both import and extern) relative
* [X] Global libraries
* [X] Call c compiler automatically when running release
* [X] Add compiler flag to only check the code, not run it.
* [X] Stress test the language!
