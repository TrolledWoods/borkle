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
pub extern "C" fn print_i64(num: i64) -> i64 {
    println!("{}", num);
    num
}

#[no_mangle]
pub extern "C" fn print_u8(num: u8) -> u8 {
    println!("{}", num);
    num
}
