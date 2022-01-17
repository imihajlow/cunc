use std::fmt;

use super::{type_solver::Solution, type_info::{AtomicType, TypeExpression}};
use super::concrete_type::ConcreteType;

#[derive(Debug, Clone, PartialEq)]
pub struct TypeVars {
    range: usize,
}

pub struct TypeVarsMapping(Vec<ConcreteType>);

impl TypeVars {
    pub(super) fn new(range: usize) -> Self {
        Self { range }
    }
    pub(super) fn is_empty(&self) -> bool {
        self.range == 0
    }

    pub(super) fn get_vars_count(&self) -> usize {
        self.range
    }
}

impl TypeVarsMapping {
    pub(super) fn new(range: usize, solution: Solution<AtomicType>) -> Self {
        // Self(0..range
            // .map(|i| solution.translate_var_index(i)));
        todo!()
    }
}

impl fmt::Display for TypeVars {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Ok(())
    }
}
