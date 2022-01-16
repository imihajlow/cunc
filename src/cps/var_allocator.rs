pub(super) struct VarAllocator {
    index: usize,
}

impl VarAllocator {
    pub(super) fn new() -> Self {
        Self { index: 0 }
    }

    pub(super) fn alloc(&mut self) -> usize {
        let r = self.index;
        self.index += 1;
        r
    }
}
