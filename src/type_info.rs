use std::collections::HashMap;
use crate::type_var_allocator::TypeVarAllocator;
use crate::util::var_from_number;
use crate::type_constraint::TypeConstraint;
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
    Atomic(AtomicType),
    Var(usize),
    Function(Vec<TypeExpression>),
}

#[derive(Debug, Clone)]
pub struct TypeVars {
    range: usize,
    constraints: Vec<TypeConstraint>
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
    pub fn new(range: usize, constraints: Vec<TypeConstraint>) -> Self {
        Self {
            range,
            constraints: constraints,
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

    /// Remap existing generic variables into local type variables.
    pub fn remap_vars(&self, allocator: &TypeVarAllocator) -> TypeExpression {
        use TypeExpression::*;
        match self {
            Atomic(_) => TypeExpression::clone(self),
            Var(n) => Var(allocator.map_existing(*n)),
            Function(v) => Function(v.iter().map(|t| t.remap_vars(allocator)).collect())
        }
    }

    /// Rename free variables in a type expression using a mapping (old number -> new number).
    pub fn rename_vars(self, mapping: &HashMap<usize, usize>) -> Self {
        use TypeExpression::*;
        match self {
            Atomic(_) => self,
            Var(n) => Var(mapping[&n]),
            Function(v) => 
                Function(v.into_iter().map(|p| p.rename_vars(mapping)).collect())
        }
    }

    /// Substitute variable with its value in a type expression.
    pub fn substitute(&mut self, var_index: usize, value: &TypeExpression) {
        use TypeExpression::*;
        match self {
            Atomic(_) => (),
            Var(n) if *n == var_index => *self = TypeExpression::clone(value),
            Var(_) => (),
            Function(v) => 
                v.iter_mut().for_each(|t| t.substitute(var_index, value))
        }
    }

    /// Returns true if type expression does not contain any variables.
    pub fn is_fixed(&self) -> bool {
        use TypeExpression::*;
        match self {
            Atomic(_) => true,
            Var(_) => false,
            Function(v) => v.iter().all(|e| e.is_fixed())
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
        if !self.constraints.is_empty() {
            for s in self.constraints.iter().map(|c| format!("{}", c)).intersperse(", ".to_string()) {
                f.write_str(&s)?;
            }
            f.write_str(" => ")?;
        }
        // for s in (0..self.range)
        //     .map(var_from_number)
        //     .intersperse(", ".to_string()) {
        //     f.write_str(&s)?;       
        // }
        Ok(())
    }
}

impl fmt::Display for TypeExpression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use TypeExpression::*;
        match self {
            Atomic(t) => write!(f, "{}", t),
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
        write!(f, "{}{}", if self.signed { "S" } else { "U" }, self.bits)
    }
}

impl fmt::Display for IntBits {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", (*self as u32) * 8)
    }
}

impl fmt::Display for AtomicTypeParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use AtomicTypeParseError::*;
        match self {
            Empty => f.write_str("empty type"),
            WrongIntSize => f.write_str("wrong integer width"),
            Unknown => f.write_str("unknown type"),
        }
    }
}
