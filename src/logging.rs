#[cfg(feature = "log")]
use parking_lot::Mutex;
#[cfg(feature = "log")]
use std::fs::File;
#[cfg(feature = "log")]
use std::sync::Arc;

#[derive(Clone)]
pub struct Logger {
    #[cfg(feature = "log")]
    file: Arc<Mutex<File>>,
}

#[cfg(not(feature = "log"))]
impl Logger {
    pub fn new() -> Self {
        Self {}
    }

    #[allow(clippy::unused_self)]
    pub fn log(&self, _args: std::fmt::Arguments<'_>) {}
}

#[cfg(feature = "log")]
impl Logger {
    pub fn new() -> Self {
        Self {
            file: Arc::new(Mutex::new(File::create("target/log.txt").expect("When logging is enabled, 'target/log.txt' has to be creatable, since that's where logging output happens"))),
        }
    }

    pub fn log(&self, args: std::fmt::Arguments<'_>) {
        use std::io::Write;

        let mut logs = self.file.lock();
        writeln!(logs, "{}", args).unwrap();
    }
}
