pub(super) struct VarAllocator {
    index: u64,
}

impl VarAllocator {
    pub(super) fn new() -> Self {
        Self { index: 0 }
    }

    pub(super) fn alloc(&mut self) -> u64 {
        let r = self.index;
        self.index += 1;
        r
    }
}
