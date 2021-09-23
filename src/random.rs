#[derive(Clone, Copy)]
pub struct Random(u32);

impl Default for Random {
    fn default() -> Self {
        Self::new()
    }
}

impl Random {
    pub fn new() -> Self {
        use std::time::{SystemTime, UNIX_EPOCH};
        Self::with_seed(
            (SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap_or_else(|_| std::time::Duration::from_millis(0))
                .as_nanos()
                % 0xffff_ffff) as u32,
        )
    }

    pub fn with_seed(seed: u32) -> Self {
        Random(seed)
    }

    /// Generates a random 32 bit number
    pub fn gen_u32(&mut self) -> u32 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 17;
        self.0 ^= self.0 << 5;
        self.0
    }

    /// Generates a random floating point number between 0.0(inclusive) and 1.0(exclusive)
    pub fn gen_f32(&mut self) -> f32 {
        (self.gen_u32() & 0xffff) as f32 / 0x10000 as f32
    }

    pub fn range(&mut self, min: f32, max: f32) -> f32 {
        (self.gen_f32() * (max - min)) + min
    }
}
