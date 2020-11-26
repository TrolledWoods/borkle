#[no_mangle]
pub extern "C" fn alloc(size: usize) -> *mut u8 {
    unsafe { std::alloc::alloc(std::alloc::Layout::from_size_align(size, 16).unwrap()) }
}

#[no_mangle]
pub extern "C" fn dealloc(ptr: *mut u8, size: usize) {
    unsafe { std::alloc::dealloc(ptr, std::alloc::Layout::from_size_align(size, 16).unwrap()) }
}
