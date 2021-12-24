use crate::type_var_allocator::TypeVarAllocator;
use crate::util::var_from_number;
use std::{str::FromStr};

use std::fmt;
use itertools::Itertools;
use crate::{error::{ErrorCause}};

#[derive(Debug, Clone)]
pub struct TypeInfo {
    expr: TypeExpression,
    vars: TypeVars
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypeExpression {
    AtomicType(AtomicType),
    Var(usize),
    Function(Vec<TypeExpression>),
}

#[derive(Debug, Clone)]
pub struct TypeVars {
    range: usize,
    constraints: Vec<TypeConstraint>
}

#[derive(Debug, Clone)]
pub struct TypeConstraint {
    // TODO
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum IntBits {
    B8 = 1,
    B16 = 2,
    B32 = 4,
}

#[derive(Clone, Debug, PartialEq)]
pub struct IntType {
    signed: bool,
    bits: IntBits,
}

#[derive(Clone, Debug, PartialEq)]
pub enum AtomicType {
    Void,
    Int(IntType),
}

#[derive(Debug)]
pub enum AtomicTypeParseError {
    Empty,
    WrongIntSize,
    Unknown,
}

impl TypeVars {
    pub fn new(range: usize) -> Self {
        Self {
            range,
            constraints: Vec::new(),
        }
    }
    pub fn is_empty(&self) -> bool {
        self.range == 0
    }

    pub fn get_vars_count(&self) -> usize {
        self.range
    }
}

impl TypeExpression {
    pub fn split_param_type(self) -> Result<(Self, Self), ErrorCause> {
        match self {
            Self::Function(parts) => {
                let count = parts.len();
                if count == 0 {
                    return Err(ErrorCause::TooManyArguments);
                }
                let mut parts_iter = parts.into_iter();
                let first = parts_iter.next().unwrap();
                let rest = match count - 1 {
                    0 => return Err(ErrorCause::TooManyArguments),
                    1 => parts_iter.next().unwrap(),
                    _ => Self::Function(parts_iter.collect())
                };
                Ok((first, rest))
            }
            _ => {
                Err(ErrorCause::TooManyArguments)
            }
        }
    }

    pub fn remap_vars(&self, allocator: &TypeVarAllocator) -> TypeExpression {
        use TypeExpression::*;
        match self {
            AtomicType(_) => TypeExpression::clone(self),
            Var(n) => Var(allocator.map_existing(*n)),
            Function(v) => Function(v.iter().map(|t| t.remap_vars(allocator)).collect())
        }
    }
}

impl IntType {
    pub fn new(signed: bool, bits: IntBits) -> Self {
        Self {
            signed,
            bits
        }
    }
}

impl FromStr for AtomicType {
    type Err = AtomicTypeParseError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s.len() == 0 {
            Err(AtomicTypeParseError::Empty)
        } else if s == "()" {
            Ok(AtomicType::Void)
        } else {
            let (first, last) = s.split_at(1);
            if first == "S" || first == "U" {
                let signed = first == "S";
                let bits = match last.parse::<usize>() {
                    Ok(8) => IntBits::B8,
                    Ok(16) => IntBits::B16,
                    Ok(32) => IntBits::B32,
                    Ok(_) => return Err(AtomicTypeParseError::WrongIntSize),
                    _ => return Err(AtomicTypeParseError::Unknown)
                };
                Ok(AtomicType::Int(IntType { signed, bits }))
            } else {
                Err(AtomicTypeParseError::Unknown)
            }
        }
    }
}

impl fmt::Display for TypeInfo {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if !self.vars.is_empty() {
            write!(f, "{} => ", self.vars)?;
        }
        write!(f, "{}", self.expr)
    }
}

impl fmt::Display for TypeVars {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for s in (0..self.range)
            .map(var_from_number)
            .intersperse(", ".to_string()) {
            f.write_str(&s)?;       
        }
        Ok(())
    }
}

impl fmt::Display for TypeExpression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use TypeExpression::*;
        match self {
            AtomicType(t) => write!(f, "{}", t),
            Var(n) => f.write_str(&var_from_number(*n)),
            Function(ts) => {
                f.write_str("(")?;
                for s in ts.iter().map(|t| format!("{}", t)).intersperse(" -> ".to_string()) {
                    f.write_str(&s)?;
                }
                f.write_str(")")
            }
        }
    }
}

impl fmt::Display for AtomicType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use AtomicType::*;
        match self {
            Void => f.write_str("()"),
            Int(t) => write!(f, "{}", t)
        }
    }
}

impl fmt::Display for IntType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", if self.signed { "s" } else { "u" }, self.bits)
    }
}

impl fmt::Display for IntBits {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", (*self as u32) * 8)
    }
}
