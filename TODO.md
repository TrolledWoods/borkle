# Version 0.0.3
* [X] Made all the locks in Program private, and manage them by documenting what locks a function takes, and never take two non recursive locks at the same time. Might not be completely robust, but it is certainly a lot better than it was before!

* [ ] Make a global setup file for the compiler!
* [ ] Add a way to run all the borkle sub-programs in a markdown file
* [ ] Have a way for named function parameter meta data to be created for extern functions.
* [ ] IDEA: &out pointer, write only pointer, if a function takes a pointer like this you can also declare a variable like this; initialize(let variable), where initialize is a fn(&out Something)
* [ ] BUG! The compiler locks up sometimes.
* [ ] Make intrinsics use stubs instead of the #intrinsic stuff that's there right now
* [ ] When the type of a function is known, allow for omitting the parameter and return types.
* [ ] Make functions have their own scope.
* [ ] Ambiguous rules about what expression a type bound applies to.
* [ ] Make assignment an expression.
* [ ] Compile time functions
* [ ] Functions for constructing types programmatically at compile time
* [ ] Polymorphism
* [ ] Implement the proper separation between 'thread pool' and 'program'
* [ ] If the dynamic library in the target directory is already defined, and has the same "last edited" date as the source file, don't copy the file from the source.
* [ ] Struct literals
* [ ] Figure out if there is a way to have fewer keywords.
* [ ] Make locals/labels use pure register ids instead of values, since they are never going to be global anyway
* [ ] Add overflow checks to type size calculations, and add a user level error for trying to create too large types.
* [ ] Use the never type to find dead code, and allow casting from it to anything.
* [ ] Indexing operations
* [ ] In the Instr it's unclear what thing members are for. Make this more general. Also, probably remove some members as there are a lot of instructions that have them and it's probably unnecessary, or make that information part of Values?
