use crate::position::Position;
use crate::ast::type_info::AtomicTypeParseError;
use crate::ast::type_info::KindExpression;
use crate::ast::type_info::TypeExpression;
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
    TooManyArguments,
    TypesMismatch(TypeExpression, TypeExpression),
    KindsMismatch(KindExpression, KindExpression),
    KindApplicationError(KindExpression, KindExpression),
    AtomicTypeParseError(AtomicTypeParseError),
    TypeConstraintMismatch,
    MultipleTypeSpecification,
    NotAConstraint(TypeExpression),
    RecursiveType(String),
    TypeConstructorNotFound(String),
}

impl Error {
    pub fn new(cause: ErrorCause, position: Position) -> Self {
        Self { cause, p: position }
    }

    pub fn with_position(self, position: Position) -> Self {
        Self {
            cause: self.cause,
            p: position,
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

impl Mismatchable for KindExpression {
    fn new_types_mismatch_error(&self, other: &Self) -> ErrorCause {
        ErrorCause::KindsMismatch(KindExpression::clone(self), KindExpression::clone(other))
    }
}

impl fmt::Display for ErrorCause {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use ErrorCause::*;
        match self {
            SyntaxError(s) => write!(f, "syntax error: {}", s),
            UnknownIdentifier(s) => write!(f, "unknown identifier `{}'", s),
            Redefinition(s) => write!(f, "`{}' is redefined", s),
            TooManyArguments => f.write_str("too many arguments"),
            TypesMismatch(t1, t2) => write!(f, "cannot match `{}' against `{}'", t1, t2),
            KindsMismatch(t1, t2) => write!(f, "cannot match `{}' against `{}'", t1, t2),
            KindApplicationError(k1, k2) => write!(f, "cannot apply kinds ({}) ({})", k1, k2),
            AtomicTypeParseError(e) => write!(f, "{}", e),
            TypeConstraintMismatch => write!(f, "cannot match type constraint"),
            MultipleTypeSpecification => write!(f, "type is specified multiple times"),
            NotAConstraint(t) => write!(f, "`{}' is not a constraint", t),
            RecursiveType(s) => write!(f, "recursive types are not allowed, `{}' is recursive", s),
            TypeConstructorNotFound(s) => write!(f, "type constructor `{}' not found", s),
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Error at {}: {}", self.p, self.cause)
    }
}
