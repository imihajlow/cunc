use crate::util::max_options;
use std::collections::HashMap;
use crate::type_var_allocator::TypeVarAllocator;
use crate::util::var_from_number;
use crate::type_constraint::TypeConstraint;
use std::{str::FromStr};

use std::fmt;
use itertools::Itertools;


#[derive(Debug, Clone)]
pub struct TypeInfo {
    expr: TypeExpression,
    vars: TypeVars
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypeExpression {
    Atomic(AtomicType),
    Var(usize),
    Composite(Box<Self>, Box<Self>),
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
    Int(IntType),
    Function,
    User(String)
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

    pub fn constraints_iter(&self) -> core::slice::Iter<TypeConstraint> {
        self.constraints.iter()
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
        use TypeExpression::*;
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

    /// Remap existing generic variables into local type variables.
    pub fn remap_vars(&self, allocator: &TypeVarAllocator) -> TypeExpression {
        use TypeExpression::*;
        match self {
            Atomic(_) => TypeExpression::clone(self),
            Var(n) => Var(allocator.map_existing(*n)),
            Composite(a, b) => Composite(
                Box::new(a.remap_vars(allocator)),
                Box::new(b.remap_vars(allocator)))
        }
    }

    /// Rename free variables in a type expression using a mapping (old number -> new number).
    pub fn rename_vars(self, mapping: &HashMap<usize, usize>) -> Self {
        use TypeExpression::*;
        match self {
            Atomic(_) => self,
            Var(n) => Var(mapping[&n]),
            Composite(a, b) => Composite(
                Box::new(a.rename_vars(mapping)),
                Box::new(b.rename_vars(mapping)))
        }
    }

    /// Substitute variable with its value in a type expression.
    pub fn substitute(&mut self, var_index: usize, value: &TypeExpression) {
        use TypeExpression::*;
        match self {
            Atomic(_) => (),
            Var(n) if *n == var_index => *self = TypeExpression::clone(value),
            Var(_) => (),
            Composite(ref mut a, ref mut b) => {
                a.substitute(var_index, value);
                b.substitute(var_index, value);
            }
        }
    }

    /// Returns true if type expression does not contain any variables.
    pub fn is_fixed(&self) -> bool {
        use TypeExpression::*;
        match self {
            Atomic(_) => true,
            Var(_) => false,
            Composite(a, b) => a.is_fixed() && b.is_fixed()
        }
    }

    /// Find maximum variable index in a type expression. Returns None if expression contains no variables.
    pub fn get_max_var_index(&self) -> Option<usize> {
        use TypeExpression::*;
        match self {
            Var(n) => Some(*n),
            Atomic(_) => None,
            Composite(a, b) =>
                max_options(a.get_max_var_index(), b.get_max_var_index())
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
            Composite(a, b) => {
                match **a {
                    Atomic(AtomicType::Function) => match **b {
                        Atomic(_) | Var(_) => write!(f, "{} ->", b),
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
