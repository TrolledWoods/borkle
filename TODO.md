# Version 0.0.1 features
* [X] Simple control flow, if, while.
* [X] Buffer pointer type

* [.] Pointers in globals
* [ ] Generalise operators
* [ ] C backend
* [ ] Fix bug where things try to be computed without dependencies
* [ ] Add error for unresolved dependencies
* [ ] Deduplicated constants can have the wrong alignment

# Version 0.0.2 features
* [ ] Redo ast nodes to be more readable, like right now what the heck is it even!? 
        Maybe it's fine to use unsafe, because if we do we can also include other data types in the ast buffer.
* [ ] Variable arguments for functions
* [ ] Defer
* [ ] Function arguments are implicitly dereferenced/referenced(maybe we want this?)
* [ ] 'Any' type, the same as C void\*
