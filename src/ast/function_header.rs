use super::ast::ConstraintContext;
use super::ast::PrefixFormatter;
use super::type_vars::TypeVars;
use std::fmt;

#[derive(Debug, PartialEq, Clone)]
pub(super) struct FunctionHeader<Type, Id> {
    pub name: Id,
    pub t: Type,
    pub constraints: ConstraintContext<Type>,
    pub type_vars: TypeVars,
}

impl<Type, Id> FunctionHeader<Type, Id> {
    pub(super) fn new(
        name: Id,
        t: Type,
        constraints: ConstraintContext<Type>,
        type_vars: TypeVars,
    ) -> Self {
        Self {
            name,
            t,
            constraints,
            type_vars,
        }
    }
}

impl<Type: PrefixFormatter, Id: fmt::Display> fmt::Display for FunctionHeader<Type, Id> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[")?;
        write!(f, "{}", self.constraints)?;
        write!(f, "{}", self.type_vars)?;
        self.t.write_with_prefix(f, "")?;
        write!(f, "]\n{}", self.name)
    }
}
