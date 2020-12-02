# Version 0.0.1 features
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

* [ ] Make comparison operators care about sign bits
* [ ] More comparison operators
* [ ] C backend
* [ ] Add error for unresolved dependencies
* [ ] Check for duplicate constants

# Version 0.0.2 features
* [ ] Redo ast nodes to be more readable, like right now what the heck is it even!? 
        Maybe it's fine to use unsafe, because if we do we can also include other data types in the ast buffer.
* [ ] Variable arguments for functions
* [ ] Defer
* [ ] Function arguments are implicitly dereferenced/referenced(maybe we want this?)
* [ ] 'Any' type, the same as C void\*
