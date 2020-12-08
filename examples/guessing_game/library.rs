use std::time::Instant;

#[no_mangle]
extern "C" fn start_timer() -> Box<Instant> {
    Box::new(Instant::now())
}

#[no_mangle]
extern "C" fn end_timer(time: Box<Instant>) -> u64 {
    println!("Elapsed: {}ms", time.elapsed().as_millis());
    time.elapsed().as_millis() as u64
}

#[no_mangle]
pub extern "C" fn read_input(buffer: &mut *mut u8) -> usize {
    use std::io::BufRead;
    let mut string = String::new();
    std::io::stdin().lock().read_line(&mut string).unwrap();
    let mut s = string.trim().to_string().into_boxed_str();

    println!("Got {}", s);
    *buffer = s.as_mut_ptr();
    let len = s.len();
    std::mem::forget(s);
    len
}

#[no_mangle]
pub extern "C" fn print_u64(num: u64) {
    print!("{}", num);
}

#[no_mangle]
pub extern "C" fn print_i64(num: i64) {
    print!("{}", num);
}

#[no_mangle]
pub extern "C" fn put_string(pointer: *const u8, length: usize) {
    let buffer = unsafe { std::slice::from_raw_parts(pointer, length) };
    print!("{}", std::str::from_utf8(buffer).unwrap());
}

#[no_mangle]
pub extern "C" fn alloc(size: usize) -> *mut u8 {
    unsafe { std::alloc::alloc(std::alloc::Layout::from_size_align(size, 16).unwrap()) }
}

#[no_mangle]
pub extern "C" fn dealloc(ptr: *mut u8, size: usize) {
    unsafe { std::alloc::dealloc(ptr, std::alloc::Layout::from_size_align(size, 16).unwrap()) }
}
