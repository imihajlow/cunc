use std::collections::HashMap;
use crate::position::Position;

/// Allocates new type variables when assigning them to AST before type deduction.
pub struct TypeVarAllocator {
    cur_index: usize,
    offsets: Vec<usize>,
    position_by_index: HashMap<usize, Position>
}

impl TypeVarAllocator {
    pub fn new() -> Self {
        Self {
            cur_index: 0,
            offsets: vec![0],
            position_by_index: HashMap::new()
        }
    }

    /// Allocate a new var index.
    pub fn allocate(&mut self, pos: &Position) -> usize {
        let r = self.cur_index;
        self.cur_index += 1;
        self.position_by_index.insert(r, Position::clone(pos));
        r
    }

    /// Get a var index for an existing generic variable.
    pub fn map_existing(&self, n: usize) -> usize {
        self.offsets.last().unwrap() + n
    }

    /// Enter a function having n generic vars
    pub fn enter_function(&mut self, n: usize, pos: &Position) {
        self.offsets.push(self.cur_index);
        for i in self.cur_index..(self.cur_index + n) {
            self.position_by_index.insert(i, Position::clone(pos));
        }
        self.cur_index += n;
    }

    pub fn leave_function(&mut self) {
        self.offsets.pop();
    }

    pub fn get_position<'a>(&'a self, index: usize) -> &'a Position {
        self.position_by_index.get(&index).unwrap()
    }
}
