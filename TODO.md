# TODO
* Check that integers are actually integers.
* Check that array members are within the bounds of the array, before it panics in the emitter.
* Figure out what to do with cycles....
* Dependencies for constants aren't correct right now!!!
* Change the parser to use the ExecutionTime enum instead of whatever it's doing right now.
* Nice presentation of printing inside of constants?
* Fix arrays in `c_output`
* Investigate why i_stdout_write turns out to be a fn([]!! u8) -> usize, when this can cause incorrect behaviour. The r here should be covariant with the return type, so it shouldn't be able to cast down to !!....
