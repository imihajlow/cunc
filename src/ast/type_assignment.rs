use super::TypeExpression;
use super::type_vars::TypeVars;
use super::ast::ConstraintContext;

/// Enum used in scopes.
#[derive(Debug, Clone)]
pub(super) enum TypeAssignment {
    ToplevelFunction(TypeVars, TypeExpression, ConstraintContext<TypeExpression>),
    LocalName(usize),
}

impl TypeAssignment {
    pub(super) fn unwrap_local_name(&self) -> usize {
        match self {
            TypeAssignment::LocalName(x) => *x,
            _ => panic!("Not a local name: {:?}", self),
        }
    }
}
