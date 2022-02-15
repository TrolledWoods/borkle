use std::sync::atomic::{AtomicPtr, AtomicUsize, AtomicBool, Ordering};
use std::mem::MaybeUninit;
use std::ptr;
use std::marker::PhantomData;

const DEFAULT_SIZE: usize = 64;

pub struct SyncVec<T, const N: usize = DEFAULT_SIZE> {
    first: AtomicPtr<Buffer<T, N>>,
    // TODO: There could be a `current` variable here that says
    // which index we're currently at.
    len: AtomicUsize,
}

impl<T> SyncVec<T> {
    pub fn new() -> Self {
        Self::new_with_size()
    }
}

impl<T, const N: usize> SyncVec<T, N> {
    pub fn new_with_size() -> Self {
        Self {
            first: AtomicPtr::new(ptr::null_mut()),
            len: AtomicUsize::new(0),
        }
    }

    pub fn iter(&self) -> Iter<'_, T, N> {
        Iter {
            next: &self.first,
            // an index of `N` means that we need to reload the values.
            local_index: N,
            occupied: ptr::null(),
            element: ptr::null(),
            _phantom: PhantomData,
        }
    }

    pub fn reserve(&self) -> Reserved<'_, T> {
        // Get the index
        let index = self.len.fetch_add(1, Ordering::SeqCst);
        let block = index / N;
        let inner_index = index % N;

        let mut current = &self.first;
        for block_i in 0..=block {
            let current_val = current.load(Ordering::SeqCst);
            let real_val = if current_val.is_null() {
                // We need to allocate a new buffer!
                // TODO: This could probably be done faster in-place by using `alloc` directly and then just setting the exact fields we want.
                let the_box = Box::new(Buffer {
                    index: block_i,
                    // Safety: An uninitialized [MaybeUninit<T>; _] is valid.
                    // TODO: This could be uninit_array once that is stabilized.
                    elements: unsafe { MaybeUninit::uninit().assume_init() },
                    occupied: [(); N].map(|()| AtomicBool::new(false)),
                    next: AtomicPtr::new(ptr::null_mut()),
                });

                let raw_ptr = Box::into_raw(the_box);

                let result = current.compare_exchange(ptr::null_mut(), raw_ptr, Ordering::SeqCst, Ordering::SeqCst);

                match result {
                    Ok(_) => raw_ptr,
                    // Someone else inserted it while we were allocating, but that's fine
                    // since we didn't do anything during that time.
                    Err(old_value) => {
                        unsafe {
                            drop(Box::from_raw(raw_ptr));
                        }
                        old_value
                    }
                }
            } else {
                current_val
            };

            if unsafe { (*real_val).index } < block {
                current = unsafe { &(*real_val).next };
            }
        }

        unsafe {
            // TODO: We load this before in the loop, can we dedupliate these loads?
            let current = current.load(Ordering::SeqCst);

            // TODO: This cast feels hairy, but it's because a raw pointer to an uninit value
            // should be fine, right?
            let element = ptr::addr_of_mut!((*current).elements).cast::<T>().add(inner_index);
            let occupied = &(*current).occupied[inner_index];

            Reserved {
                element,
                occupied,
                _phantom: PhantomData,
            }
        }
    }

    pub fn push(&self, item: T) -> &T {
        self.reserve().insert(item)
    }
}

impl<T, const N: usize> Drop for SyncVec<T, N> {
    fn drop(&mut self) {
        let mut current = *self.first.get_mut();
        while !current.is_null() {
            unsafe {
                let ptr_to_dealloc = current;
                current = *(*current).next.get_mut();

                // Drop it!
                drop(Box::from_raw(ptr_to_dealloc));
            }
        }
    }
}

struct Buffer<T, const N: usize> {
    index: usize,
    next: AtomicPtr<Buffer<T, N>>,
    elements: [MaybeUninit<T>; N],
    // TODO: This could be a bitfield.
    // Used to synchronize `elements`
    occupied: [AtomicBool; N],
}

pub struct Reserved<'a, T> {
    element: *mut T,
    occupied: *const AtomicBool,
    _phantom: PhantomData<&'a mut T>,
}

impl<'a, T> Reserved<'a, T> {
    pub fn insert(self, value: T) -> &'a T {
        unsafe {
            self.element.write(value);
            (*self.occupied).store(true, Ordering::SeqCst);

            &*self.element
        }
    }
}

pub struct Iter<'a, T, const N: usize = DEFAULT_SIZE> {
    next: &'a AtomicPtr<Buffer<T, N>>,
    local_index: usize,
    occupied: *const AtomicBool,
    element: *const T,
    _phantom: PhantomData<&'a [T]>,
}

impl<'a, T, const N: usize> Iterator for Iter<'a, T, N> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if self.local_index == N {
                let pointer = self.next.load(Ordering::SeqCst);
                if pointer.is_null() {
                    return None;
                }

                unsafe {
                    self.next = &(*pointer).next;
                    self.element = ptr::addr_of_mut!((*pointer).elements).cast::<T>();
                    self.occupied = (*pointer).occupied.as_ptr();
                }

                self.local_index = 0;
            }

            let occupied = self.occupied;
            let element = self.element;
            unsafe {
                self.occupied = self.occupied.add(1);
                self.element = self.element.add(1);
                self.local_index += 1;
            }

            unsafe {
                let is_occupied = (*occupied).load(Ordering::SeqCst);
                if is_occupied {
                    return Some(&*element);
                }
            }
        }
    }
}

#[test]
fn basic() {
    use std::sync::Arc;
    use std::thread;

    let sync_vec = Arc::new(SyncVec::<u64>::new());

    let mut handles = Vec::new();
    let total = (1+2+3+4+5+6) * 50;
    for _ in 0..50 {
        let sync_vec = sync_vec.clone();
        handles.push(thread::spawn(move || {
            sync_vec.push(1);
            sync_vec.push(2);
            sync_vec.push(3);
            sync_vec.push(4);
            sync_vec.push(5);
            sync_vec.push(6);
        }));
    }

    for handle in handles {
        handle.join().unwrap();
    }

    let summed = sync_vec.iter().copied().sum::<u64>();
    assert_eq!(summed, total);
}
