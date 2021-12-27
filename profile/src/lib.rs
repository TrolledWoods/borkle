#![feature(once_cell)]
#![feature(thread_id_value)]
#![allow(warnings)]

//! A simple profiling backend for the "chrome://tracing" profiler built into google chrome.
//! Output format is described here in detail:
//! `https://docs.google.com/document/d/1CvAClvFfyA5R-PhYUmn5OOQtYMH4h6I0nSsKchNAySU`
//!
//! By default the profiling is turned off, because profiling has a performance penalty.
//! "Turned off" mode still has some overhead, it still creates a profiling output file, but the
//! reason for that is so you won't accidentally use an old profile
//! because you forgot to build with profiling and just built a normal release build instead.

use std::lazy::SyncOnceCell;
use std::sync::Mutex;
use std::time::Instant;
use std::path::Path;
use std::thread;
use std::io::Write;

static GLOBAL_DATA: SyncOnceCell<GlobalData> = SyncOnceCell::new();

struct GlobalData {
    time: Instant,
    frames: Mutex<Vec<Frame>>,
}

/// Sets up global data required by other profiling functions.
pub fn begin() {
    {
        let result = GLOBAL_DATA.set(GlobalData {
            time: Instant::now(),
            frames: Mutex::new(Vec::new()),
        });

        if result.is_err() {
            panic!("Cannot create more than one `Profile` struct");
        }
    }
}

/// Finishes the profile, and dumps the data to a json file at the specified path.
///
/// # Panics
/// * If `begin` hasn't been called.
pub fn finish(filename: impl AsRef<Path>) {
    #[cfg(feature = "profiling")]
    {
        // Write the profile to disk(this will happen even if the program crashes right now, but we could check is_panicking later)
        let global_data = GLOBAL_DATA
            .get()
            .expect("Before beginning to profile(i.e. in the beginning of main), you should always do ``begin()`");

        let frames = global_data.frames.lock().expect("Lock is poisoned");

        let mut file_handle = std::fs::File::create(filename).expect("Couldn't open profile output file");
        writeln!(file_handle, "[").unwrap();
        for (i, frame) in frames.iter().enumerate() {
            write!(file_handle, "{{\"name\": {:?}, \"cat\": \"PERF\", \"ph\": \"X\", \"ts\": {}, \"dur\": {}, \"pid\": {}, \"tid\": {} }}", frame.name, frame.time_stamp, frame.duration, frame.thread_id, frame.thread_id).unwrap();

            if i + 1 != frames.len() {
                writeln!(file_handle, ",").unwrap();
            }
        }
        writeln!(file_handle, "]").unwrap();
        drop(file_handle);
    }
}

// Implementation detail! Users of the crate should not depend on this! The only reason it's public is because macros require that for now.
#[doc(hidden)]
pub struct FrameTimer {
    name: &'static str,
    time_stamp: u128,
}

impl FrameTimer {
    pub fn new(name: &'static str) -> Self {
        Self {
            name,
            time_stamp: GLOBAL_DATA
                .get()
                .expect("Before beginning to profile(i.e. in the beginning of main), you should always do ``begin()`")
                .time
                .elapsed()
                .as_micros(),
        }
    }
}

impl Drop for FrameTimer {
    fn drop(&mut self) {
        let global_data = GLOBAL_DATA
            .get()
            .expect("Before beginning to profile(i.e. in the beginning of main), you should always do ``begin()`");
        let duration = global_data.time.elapsed().as_micros() - self.time_stamp;
        let thread_id = thread::current().id().as_u64().get();

        global_data.frames.lock().unwrap().push(Frame {
            name: self.name,
            time_stamp: self.time_stamp,
            duration,
            thread_id,
        });
    }
}

/// Profiles the code until the end of the scope.
#[cfg(feature = "profiling")]
#[macro_export]
macro_rules! profile {
    ($name:tt) => {
        let _deferred = $crate::FrameTimer::new(concat!($name, " ", file!(), ":", line!(), ",", column!()));
    };
}

#[cfg(not(feature = "profiling"))]
#[macro_export]
macro_rules! profile {
    ($name:tt) => {};
}

// Implementation detail! Users of the crate should not depend on this! The only reason it's public is because macros require that for now.
#[doc(hidden)]
pub struct Frame {
    name: &'static str,
    // All times are in microseconds
    time_stamp: u128,
    duration: u128,
    thread_id: u64,
}
