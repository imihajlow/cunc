use std::{str::FromStr, io::BufRead};
use std::collections::btree_set::Union;
use std::fmt;
use itertools::Itertools;
use crate::{error::{Error, ErrorCause}, ast::Function};

#[derive(Clone, Debug, PartialEq)]
pub enum CuncType {
    Unknown,
    Atomic(AtomicType),
    Function(Vec<CuncType>)
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
    AnyNumber,
    Int(IntType),
}

#[derive(Debug)]
pub enum AtomicTypeParseError {
    Empty,
    WrongIntSize,
    Unknown,
}

impl CuncType {
    pub fn split_param_type(self) -> Result<(CuncType, CuncType), ErrorCause> {
        match self {
            CuncType::Function(parts) => {
                let count = parts.len();
                if count == 0 {
                    return Err(ErrorCause::TooManyArguments);
                }
                let mut parts_iter = parts.into_iter();
                let first = parts_iter.next().unwrap();
                let rest = match count - 1 {
                    0 => return Err(ErrorCause::TooManyArguments),
                    1 => parts_iter.next().unwrap(),
                    _ => CuncType::Function(parts_iter.collect())
                };
                Ok((first, rest))
            }
            _ => {
                Err(ErrorCause::TooManyArguments)
            }
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

pub fn collect_type<'a, I>(iter: &'a mut I) -> Option<CuncType>
where I: Iterator<Item = &'a CuncType> {
    let types: Vec<_> = iter.collect();
    if types.len() == 0 {
        None
    } else if types.len() == 1 {
        Some(CuncType::clone(types[0]))
    } else {
        Some(CuncType::Function(types.into_iter().map(CuncType::clone).collect()))
    }
}

impl fmt::Display for CuncType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use CuncType::*;
        match self {
            Unknown => write!(f, "?"),
            Atomic(t) => write!(f, "{}", t),
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
            AnyNumber => f.write_str("Num"),
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
