use std::collections::HashMap;
use std::fmt;

use crate::type_var_allocator::TypeVarAllocator;
use crate::type_info::{TypeExpression, AtomicType};
use crate::position::Position;
use crate::error::{Error, ErrorCause};

#[derive(Debug, Clone)]
pub struct TypeConstraint {
    t: TypeExpression,
    v: TypeConstraintVariant,
    p: Position,
}

#[derive(Debug, Clone, PartialEq)]
enum TypeConstraintVariant {
    Builtin(BuiltinTypeConstraint)
}

#[derive(Debug, Clone, PartialEq)]
enum BuiltinTypeConstraint {
    Num,
}

impl TypeConstraint {
    pub fn new_num(t: &TypeExpression, p: &Position) -> Self {
        Self {
            t: TypeExpression::clone(t),
            v: TypeConstraintVariant::Builtin(BuiltinTypeConstraint::Num),
            p: Position::clone(p)
        }
    }

    pub fn check(&self) -> Result<(), Error> {
        if self.v.check(&self.t) {
            Ok(())
        } else {
            Err(Error::new(ErrorCause::TypeConstraintMismatch(TypeConstraint::clone(self)),
                Position::clone(&self.p)))
        }
    }

    /// Remap existing generic variables into local type variables.
    pub fn remap_vars(&self, allocator: &TypeVarAllocator) -> TypeConstraint {
        Self {
            t: self.t.remap_vars(allocator),
            v: TypeConstraintVariant::clone(&self.v),
            p: Position::clone(&self.p),
        }
    }

    /// Rename free variables using a mapping (old number -> new number).
    pub fn rename_vars(self, mapping: &HashMap<usize, usize>) -> Self {
        Self {
            t: self.t.rename_vars(mapping),
            v: self.v,
            p: self.p
        }
    }

    /// Substitute variable with its value in a type constraint.
    pub fn substitute(&mut self, var_index: usize, value: &TypeExpression) {
        self.t.substitute(var_index, value);
    }

    pub fn merge(mut constraints: Vec<Self>) -> Result<Vec<Self>, Error> {
        let mut result: Vec<Self> = Vec::new();
        while let Some(top) = constraints.pop() {
            for c in constraints.iter() {
                if !top.is_compatible_with(c) {
                    let pos = Position::clone(&top.p);
                    return Err(Error::new(
                        ErrorCause::TypeConstraintsIncompatible(top, TypeConstraint::clone(c)), pos));
                }
            }
            if !result.iter().any(|c| &top == c) {
                result.push(top);
            }
        }
        Ok(result)
    }

    fn is_compatible_with(&self, other: &Self) -> bool {
        if self.t == other.t {
            self.v.is_compatible_with(&other.v)
        } else {
            true
        }
    }
}

impl PartialEq for TypeConstraint {
    fn eq(&self, other: &Self) -> bool {
        self.t == other.t && self.v == other.v
    }
}

impl TypeConstraintVariant {
    fn check(&self, t: &TypeExpression) -> bool {
        match self {
            Self::Builtin(bi) => bi.check(t)
        }
    }

    fn is_compatible_with(&self, other: &Self) -> bool {
        use TypeConstraintVariant::*;
        match (self, other) {
            (Builtin(a), Builtin(b)) => a.is_compatible_with(b),
        }
    }
}

impl BuiltinTypeConstraint {
    fn check(&self, t: &TypeExpression) -> bool {
        match self {
            Self::Num => {
                use TypeExpression::*;
                match t {
                    Function(v) if v.len() == 1 => self.check(v.first().unwrap()),
                    Function(_) => false,
                    Var(_) => true,
                    Atomic(t) => {
                        match t {
                            AtomicType::Int(_) => true,
                            &AtomicType::Void => false,
                        }
                    }
                }
            }
        }
    }

    fn is_compatible_with(&self, other: &Self) -> bool {
        use BuiltinTypeConstraint::*;
        match (self, other) {
            (Num, Num) => true,
        }
    }
}

impl fmt::Display for TypeConstraint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}({})", self.v, self.t)
    }
}

impl fmt::Display for TypeConstraintVariant {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Builtin(bi) => write!(f, "{}", bi)
        }
    }
}

impl fmt::Display for BuiltinTypeConstraint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Num => f.write_str("Num")
        }
    }
}
