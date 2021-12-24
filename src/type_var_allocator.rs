
/// Allocates new type variables when assigning them to AST before type deduction.
pub struct TypeVarAllocator {
    cur_index: usize,
    offsets: Vec<usize>,
}

impl TypeVarAllocator {
    pub fn new() -> Self {
        Self {
            cur_index: 0,
            offsets: vec![0],
        }
    }

    /// Allocate a new var index.
    pub fn allocate(&mut self) -> usize {
        let r = self.cur_index;
        self.cur_index += 1;
        r
    }

    /// Get a var index for an existing generic variable.
    pub fn map_existing(&self, n: usize) -> usize {
        self.offsets.last().unwrap() + n
    }

    /// Enter a function having n generic vars
    pub fn enter_function(&mut self, n: usize) {
        self.offsets.push(self.cur_index);
        self.cur_index += n;
    }

    pub fn leave_function(&mut self) {
        self.offsets.pop();
    }
}
