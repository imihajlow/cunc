use crate::type_constraint::TypeConstraint;
use crate::type_info::AtomicTypeParseError;
use crate::type_info::TypeExpression;
use crate::position::Position;
use std::fmt;

#[derive(Debug)]
pub struct Error {
    cause: ErrorCause,
    p: Position,
}

#[derive(Debug)]
pub enum ErrorCause {
    SyntaxError(String),
    UnknownIdentifier(String),
    Redefinition(String),
    IsAFunction,
    TooManyArguments,
    TypesMismatch(TypeExpression, TypeExpression),
    AtomicTypeParseError(AtomicTypeParseError),
    TypeConstraintMismatch(TypeConstraint),
    TypeConstraintsIncompatible(TypeConstraint, TypeConstraint),
}

impl Error {
    pub fn new(cause: ErrorCause, position: Position) -> Self {
        Self {
            cause,
            p: position
        }
    }
}

impl fmt::Display for ErrorCause {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use ErrorCause::*;
        match self {
            SyntaxError(s) => write!(f, "syntax error: {}", s),
            UnknownIdentifier(s) => write!(f, "unknown identifier `{}'", s),
            Redefinition(s) => write!(f, "`{}' is redefined", s),
            IsAFunction => f.write_str("a non-functional type declaration for a function"),
            TooManyArguments => f.write_str("too many arguments"),
            TypesMismatch(t1, t2) => write!(f, "cannot match `{}' against `{}'", t1, t2),
            AtomicTypeParseError(e) => write!(f, "{}", e),
            TypeConstraintMismatch(c) => write!(f, "Cannot match type constraint: {}", c),
            TypeConstraintsIncompatible(c1, c2) => write!(f, "Incompatible type constraints: `{}' and `{}'", c1, c2),
        }
    }
}


impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Error at {}: {}", self.p, self.cause)
    }
}
