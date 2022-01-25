use std::fmt;

use crate::error::ErrorCause;

use super::ast::Module;
use super::concrete_type::ConcreteType;
use super::{
    type_info::{AtomicType, TypeExpression},
    type_solver::Solution,
};

#[derive(Debug, Clone, PartialEq)]
pub struct TypeVars {
    range: usize,
}

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

    pub(super) fn instantiate(
        &self,
        m: &Module<TypeExpression, String>,
        solution: &Solution<AtomicType>,
    ) -> Result<Vec<ConcreteType>, ErrorCause> {
        (0..self.range)
            .map(|i| {
                let te = solution.translate_var_index(i);
                ConcreteType::new(&te, m)
            })
            .collect()
    }
}

impl fmt::Display for TypeVars {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Ok(())
    }
}
