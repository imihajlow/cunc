use crate::type_info::AtomicTypeParseError;
use crate::type_info::CuncType;
use crate::position::Position;

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
    NotAFunction,
    TooManyArguments,
    TypesMismatch(CuncType, CuncType),
    AtomicTypeParseError(AtomicTypeParseError),
}

impl Error {
    pub fn new(cause: ErrorCause, position: Position) -> Self {
        Self {
            cause,
            p: position
        }
    }
}
