# TODO
* Constraints should have value sets, not values! (Note!!) Once this is done, `set_int` should emit a constraint that uses the value set.
* Check that array members are within the bounds of the array, before it panics in the emitter.
* Figure out what to do with cycles....
* Change the parser to use the ExecutionTime enum instead of whatever it's doing right now.
* Nice presentation of printing inside of constants?
* Fix arrays in `c_output`
* Investigate why i_stdout_write turns out to be a fn([]!! u8) -> usize, when this can cause incorrect behaviour. The r here should be covariant with the return type, so it shouldn't be able to cast down to !!....
* Custom pointer thing for the interpreter; could also use this for constants, and to statically pre-build some pointer values that let you reference known values and so on.
* POSSIBLE BUG!!! Make sure that constants that contain pointers don't compile time merge with ones that don't.
