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
    pub(super) fn new(
        range: usize,
        solution: Solution<AtomicType>,
        m: &Module<TypeExpression, String>,
    ) -> Result<Self, ErrorCause> {
        let rv: Result<Vec<_>, _> = (0..range)
            .map(|i| ConcreteType::new(&solution.translate_var_index(i), m))
            .collect();
        Ok(Self(rv?))
    }
}

impl fmt::Display for TypeVars {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Ok(())
    }
}
