# Version 0.0.3
* [X] Made all the locks in Program private, and manage them by documenting what locks a function takes, and never take two non recursive locks at the same time. Might not be completely robust, but it is certainly a lot better than it was before!
* [X] BUG! The compiler locks up sometimes.
* [X] IDEA: Make aliases in structs, so you can alias a name as a more complex path
* [X] Redid built in functions/intrinsics
* [X] Inconsistancy; Named type uses ';' while unnamed struct uses ',', this is inconsistant!
* [X] Dependency system now doesn't associate tasks with members, but rather tasks are their own standalone thing
* [X] Feature; Allow for recursive functions.
* [X] "Polymorphism"

* [ ] Make a generic way to construct an Id that just wraps a usize.
* [ ] Cached polymorphic variants
* [ ] Cache callable functions, so that when a function is callable it doesn't have to be recalculated whether it is callable or not.
* [ ] Right now functions in type expressions are not properly handled in the dependency system, and might crash the compiler!
* [ ] Show where bad loops of recursion happen(can they even happen?)
* [ ] BUG! Collision checks on field names and aliases, and collisions between aliases.
* [ ] Add an instruction for calling a built in function, so built in function calls are cheaper?
* [ ] BUG! Status access violation when the compiler crashes(probably a thread trying to still do things)
* [ ] BUG! Doesn't exit "gracefully" when a thread panics.
* [ ] BUG! Sometimes we try to modify a dependency when it's not supposed to be modified? Very elusive bug it looks like :(
* [ ] Make a global setup file for the compiler!
* [ ] Add a way to run all the borkle sub-programs in a markdown file
* [ ] Have a way for named function parameter meta data to be created for extern functions.
* [ ] IDEA: &out pointer, write only pointer, if a function takes a pointer like this you can also declare a variable like this; initialize(let variable), where initialize is a fn(&out Something)
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
* [ ] Task scheduler
* [ ] A zero sized type that doesn't fit into constants as a way to mark your own type as not being able to fit into a constant.
