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

* [ ] Stress test the language!

# Version 0.0.2
* [ ] Make a setup file for projects!
* [ ] Type definitions
* [ ] Struct types
* [ ] Struct literals
* [ ] Structs in c
* [ ] Indexing operations
* [ ] Use hashes for deduplication like before
* [ ] Implement the proper separation between 'thread pool' and 'program'
* [ ] Redo ast nodes to be more readable, like right now what the heck is it even!? 
        Maybe it's fine to use unsafe, because if we do we can also include other data types in the ast buffer.
* [ ] Variable arguments for functions
* [ ] Defer
* [ ] Function arguments are implicitly dereferenced/referenced(maybe we want this?)
* [ ] 'Any' type, the same as C void\*
    (do we want it to behave this way or do we want 'Any' to use a type id, and have some other type that works like c void)
* [ ] Change the type inference system to allow for more nuanced things, since right now it's cracking at the seems.
