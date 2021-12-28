use crate::error::ErrorCause;
use crate::util::max_options;
use std::collections::HashMap;
use crate::type_var_allocator::TypeVarAllocator;
use crate::util::var_from_number;
use std::{str::FromStr};
use std::fmt;

pub type TypeExpression = CompositeExpression<AtomicType, ()>;

#[derive(Debug, Clone, PartialEq)]
pub enum CompositeExpression<AT, Kind> {
    Atomic(AT),
    Var(usize, Kind),
    Composite(Box<Self>, Box<Self>),
}

#[derive(Debug, Clone)]
pub struct TypeVars {
    range: usize,
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
    Int(IntType),
    Function,
    Num,
    User(String)
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
    pub fn new_function(a: Self, b: Self) -> Self {
        TypeExpression::Composite(
            Box::new(TypeExpression::Composite(
                Box::new(TypeExpression::Atomic(AtomicType::Function)),
                Box::new(a))),
            Box::new(b))
    }

    pub fn new_function_from_vec(v: Vec<Self>) -> Self {
        assert!(!v.is_empty());
        let mut it = v.into_iter().rev();
        let last = it.next().unwrap();
        it.fold(last, |tail, cur| Self::new_function(cur, tail))
    }

    pub fn match_function<'a>(&'a self) -> Option<(&'a Self, &'a Self)> {
        use CompositeExpression::*;
        if let Composite(a, b) = self {
            if let Composite(c, d) = &**a {
                if let Atomic(AtomicType::Function) = **c {
                    Some((&d, b))
                } else {
                    None
                }
            } else {
                None
            }
        } else {
            None
        }
    }
}

impl<AT: Clone, Kind: Clone> CompositeExpression<AT, Kind> {
    /// Remap existing generic variables into local type variables.
    pub fn remap_vars(&self, allocator: &TypeVarAllocator) -> Self {
        use CompositeExpression::*;
        match self {
            Atomic(_) => CompositeExpression::clone(&self),
            Var(n, k) => Var(allocator.map_existing(*n), Kind::clone(k)),
            Composite(a, b) => Composite(
                Box::new(a.remap_vars(allocator)),
                Box::new(b.remap_vars(allocator)))
        }
    }

    /// Rename free variables in a type expression using a mapping (old number -> new number).
    pub fn rename_vars(self, mapping: &HashMap<usize, usize>) -> Self {
        use CompositeExpression::*;
        match self {
            Atomic(_) => self,
            Var(n, k) => Var(mapping[&n], k),
            Composite(a, b) => Composite(
                Box::new(a.rename_vars(mapping)),
                Box::new(b.rename_vars(mapping)))
        }
    }

    /// Substitute variable with its value in a type expression.
    pub fn substitute(&mut self, var_index: usize, value: &CompositeExpression<AT, Kind>) {
        use CompositeExpression::*;
        match self {
            Atomic(_) => (),
            Var(n, k) if *n == var_index => *self = CompositeExpression::clone(value),
            Var(_, _) => (),
            Composite(ref mut a, ref mut b) => {
                a.substitute(var_index, value);
                b.substitute(var_index, value);
            }
        }
    }

    /// Returns true if type expression does not contain any variables.
    pub fn is_fixed(&self) -> bool {
        use CompositeExpression::*;
        match self {
            Atomic(_) => true,
            Var(_, _) => false,
            Composite(a, b) => a.is_fixed() && b.is_fixed()
        }
    }

    /// Find maximum variable index in a type expression. Returns None if expression contains no variables.
    pub fn get_max_var_index(&self) -> Option<usize> {
        use CompositeExpression::*;
        match self {
            Var(n, _) => Some(*n),
            Atomic(_) => None,
            Composite(a, b) =>
                max_options(a.get_max_var_index(), b.get_max_var_index())
        }
    }
}

impl<> CompositeExpression<AtomicType, ()> {
    pub fn check_constraint(&self) -> Result<(), ErrorCause> {
        use CompositeExpression::*;
        // TODO kinds
        match self {
            Var(_, _) |
            Atomic(_) => Err(ErrorCause::NotAConstraint(TypeExpression::clone(self))),
            Composite(a, b) => match &**a {
                Atomic(t) if *t == AtomicType::Num => match &**b {
                    Var(_, _) => Ok(()),
                    Atomic(t) if matches!(t, AtomicType::Int(_)) => Ok(()),
                    _ => Err(ErrorCause::TypeConstraintMismatch),
                }
                _ => Err(ErrorCause::NotAConstraint(TypeExpression::clone(self))),
            }
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
        } else {
            if s == "Num" {
                Ok(AtomicType::Num)
            } else {
                let (first, last) = s.split_at(1);
                if first == "S" || first == "U" {
                    let signed = first == "S";
                    let bits = match last.parse::<usize>() {
                        Ok(8) => IntBits::B8,
                        Ok(16) => IntBits::B16,
                        Ok(32) => IntBits::B32,
                        Ok(_) => return Ok(AtomicType::User(s.to_string())),
                        _ => return Ok(AtomicType::User(s.to_string()))
                    };
                    Ok(AtomicType::Int(IntType { signed, bits }))
                } else {
                    Ok(AtomicType::User(s.to_string()))
                }
            }
        }
    }
}

impl fmt::Display for TypeVars {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Ok(())
    }
}

impl fmt::Display for TypeExpression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use CompositeExpression::*;
        match self {
            Atomic(t) => write!(f, "{}", t),
            Var(n, _) => f.write_str(&var_from_number(*n)),
            Composite(a, b) => {
                match **a {
                    Atomic(AtomicType::Function) => match **b {
                        Atomic(_) | Var(_, _) => write!(f, "{} ->", b),
                        Composite(_, _) => write!(f, "({}) ->", b),
                    }
                    _ => write!(f, "{} {}", a, b)
                }
            }
        }
    }
}

impl fmt::Display for AtomicType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use AtomicType::*;
        match self {
            Int(t) => write!(f, "{}", t),
            Function => write!(f, "(->)"),
            User(s) => f.write_str(s),
            Num => f.write_str("Num"),
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
