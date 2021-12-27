use crate::type_info::AtomicType;
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
    UnknownConstraint(String),
    Redefinition(String),
    IsAFunction,
    TooManyArguments,
    TypesMismatch(TypeExpression, TypeExpression),
    AtomicTypeParseError(AtomicTypeParseError),
    TypeConstraintMismatch,
    // TypeConstraintsIncompatible(TypeConstraint, TypeConstraint),
    MultipleTypeSpecification,
    NotAConstraint(TypeExpression),
}

impl Error {
    pub fn new(cause: ErrorCause, position: Position) -> Self {
        Self {
            cause,
            p: position
        }
    }
}

pub trait Mismatchable {
    fn new_types_mismatch_error(&self, other: &Self) -> ErrorCause;
}

impl Mismatchable for TypeExpression {
    fn new_types_mismatch_error(&self, other: &Self) -> ErrorCause {
        ErrorCause::TypesMismatch(TypeExpression::clone(self), TypeExpression::clone(other))
    }
}

impl fmt::Display for ErrorCause {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use ErrorCause::*;
        match self {
            SyntaxError(s) => write!(f, "syntax error: {}", s),
            UnknownIdentifier(s) => write!(f, "unknown identifier `{}'", s),
            UnknownConstraint(s) => write!(f, "unknown constraint `{}'", s),
            Redefinition(s) => write!(f, "`{}' is redefined", s),
            IsAFunction => f.write_str("a non-functional type declaration for a function"),
            TooManyArguments => f.write_str("too many arguments"),
            TypesMismatch(t1, t2) => write!(f, "cannot match `{}' against `{}'", t1, t2),
            AtomicTypeParseError(e) => write!(f, "{}", e),
            TypeConstraintMismatch => write!(f, "cannot match type constraint"),
            // TypeConstraintsIncompatible(c1, c2) => write!(f, "incompatible type constraints: `{}' and `{}'", c1, c2),
            MultipleTypeSpecification => write!(f, "type is specified multiple times"),
            NotAConstraint(t) => write!(f, "`{}' is not a constraint", t),
        }
    }
}


impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Error at {}: {}", self.p, self.cause)
    }
}
