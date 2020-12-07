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

* [ ] Make comparison operators care about sign bits
* [ ] More comparison operators
* [ ] Indexing operations
* [ ] Stress test the language!
* [ ] Implement lvalue members in c backend

# Version 0.0.2
* [ ] Implement the proper separation between 'thread pool' and 'program'
* [ ] Redo ast nodes to be more readable, like right now what the heck is it even!? 
        Maybe it's fine to use unsafe, because if we do we can also include other data types in the ast buffer.
* [ ] Variable arguments for functions
* [ ] Defer
* [ ] Function arguments are implicitly dereferenced/referenced(maybe we want this?)
* [ ] 'Any' type, the same as C void\*
    (do we want it to behave this way or do we want 'Any' to use a type id, and have some other type that works like c void)
