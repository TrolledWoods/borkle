#[no_mangle]
pub extern "C" fn alloc(size: usize) -> *mut u8 {
    println!("Allocating {} bytes of memory", size);
    unsafe { std::alloc::alloc(std::alloc::Layout::from_size_align(size, 16).unwrap()) }
}

#[no_mangle]
pub extern "C" fn dealloc(ptr: *mut u8, size: usize) {
    println!("Deallocating {} bytes of memory", size);
    unsafe { std::alloc::dealloc(ptr, std::alloc::Layout::from_size_align(size, 16).unwrap()) }
}

#[no_mangle]
pub extern "C" fn put_string(pointer: *const u8, length: usize) {
    let buffer = unsafe { std::slice::from_raw_parts(pointer, length) };
    print!("{}", std::str::from_utf8(buffer).unwrap());
}

#[no_mangle]
pub extern "C" fn flush_stdout() {
    use std::io::Write;
    std::io::stdout().flush().expect("Flushing stdout failed");
}

#[no_mangle]
pub extern "C" fn print_i64(num: i64) -> i64 {
    println!("{}", num);
    num
}

#[no_mangle]
pub extern "C" fn print_u8(num: u8) -> u8 {
    println!("{}", num);
    num
}

#[no_mangle]
pub extern "C" fn callback() -> extern "C" fn(i64) -> i64 {
    print_i64
}
