#[derive(Debug, Clone, Copy)]
pub enum ExecutionTime {
    Never,
    RuntimeFunc,
    Emission,
    Typing,
}

impl ExecutionTime {
    pub fn combine(self, new: ExecutionTime) -> Self {
        match (self, new) {
            (_, ExecutionTime::Typing) |
            (ExecutionTime::Typing, ExecutionTime::RuntimeFunc | ExecutionTime::Emission) => ExecutionTime::Typing,
            (_, ExecutionTime::Never) |
            (ExecutionTime::Never, ExecutionTime::RuntimeFunc | ExecutionTime::Emission) => ExecutionTime::Never,
            (ExecutionTime::Emission, ExecutionTime::RuntimeFunc | ExecutionTime::Emission) |
            (ExecutionTime::RuntimeFunc, ExecutionTime::Emission | ExecutionTime::RuntimeFunc) => ExecutionTime::Emission,
        }
    }
}

