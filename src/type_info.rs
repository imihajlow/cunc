use crate::error::ErrorCause;
use crate::name_context::TypeContext;
use crate::position::Position;
use crate::type_solver::Solver;
use crate::type_var_allocator::TypeVarAllocator;
use crate::util::max_options;
use crate::util::var_from_number;
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::str::FromStr;

pub type TypeExpression = CompositeExpression<AtomicType>;

pub type KindExpression = CompositeExpression<AtomicKind>;

#[derive(Debug, Clone, PartialEq)]
pub enum CompositeExpression<AT> {
    Atomic(AT),
    Var(usize),
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
    User(String),
}

#[derive(Debug)]
pub enum AtomicTypeParseError {
    Empty,
    WrongIntSize,
    Unknown,
}

#[derive(Debug, Clone, PartialEq)]
pub enum AtomicKind {
    Type,
    Constraint,
}

impl TypeVars {
    pub fn new(range: usize) -> Self {
        Self { range }
    }
    pub fn is_empty(&self) -> bool {
        self.range == 0
    }

    pub fn get_vars_count(&self) -> usize {
        self.range
    }
}

impl<AT> CompositeExpression<AT> {
    /// Create an expression which is a transformation from `a` to `b`.
    /// `op` is a `AT`-specific transformation operator,
    /// e.g. `AtomicType::Function` or `AtomicKind::Arrow`.
    pub fn new_transformation(a: Self, b: Self, op: AT) -> Self {
        CompositeExpression::Composite(
            Box::new(CompositeExpression::Composite(
                Box::new(CompositeExpression::Atomic(op)),
                Box::new(a),
            )),
            Box::new(b),
        )
    }
}

impl<AT: Clone> CompositeExpression<AT> {
    /// Create something like `a -> b -> c`.
    pub fn new_transformation_chain(v: Vec<Self>, op: AT) -> Self {
        assert!(!v.is_empty());
        let mut it = v.into_iter().rev();
        let last = it.next().unwrap();
        it.fold(last, |tail, cur| {
            Self::new_transformation(cur, tail, AT::clone(&op))
        })
    }
}

impl TypeExpression {
    pub fn new_function(a: Self, b: Self) -> Self {
        Self::new_transformation(a, b, AtomicType::Function)
    }

    pub fn new_function_from_vec(v: Vec<Self>) -> Self {
        Self::new_transformation_chain(v, AtomicType::Function)
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

    /// Collect references of custom types.
    pub fn collect_refs(&self, set: &mut HashSet<String>) {
        use CompositeExpression::*;
        match self {
            Atomic(a) => {
                if let AtomicType::User(s) = a {
                    set.insert(s.to_string());
                }
            }
            Var(_) => (),
            Composite(a, b) => {
                a.collect_refs(set);
                b.collect_refs(set);
            }
        }
    }

    pub fn get_kind(
        &self,
        context: &TypeContext<KindExpression>,
    ) -> Result<KindExpression, ErrorCause> {
        use CompositeExpression::*;
        match self {
            Atomic(a) => a.get_kind(context),
            Var(_) => Ok(KindExpression::Atomic(AtomicKind::Type)),
            Composite(a, b) => {
                let a_kind = a.get_kind(context)?;
                let b_kind = b.get_kind(context)?;
                a_kind.apply(&b_kind)
            }
        }
    }
}

impl KindExpression {
    pub const TYPE: KindExpression = KindExpression::Atomic(AtomicKind::Type);
    pub const CONSTRAINT: KindExpression = KindExpression::Atomic(AtomicKind::Constraint);

    pub fn mapping(from: KindExpression, to: KindExpression) -> Self {
        KindExpression::Composite(Box::new(from), Box::new(to))
    }

    pub fn substitute_free_vars(&mut self, with: &KindExpression) {
        use CompositeExpression::*;
        match self {
            Var(_) => *self = KindExpression::clone(with),
            Atomic(_) => (),
            Composite(ref mut a, ref mut b) => {
                a.substitute_free_vars(with);
                b.substitute_free_vars(with);
            }
        }
    }

    pub fn apply(&self, applicant: &Self) -> Result<Self, ErrorCause> {
        use CompositeExpression::*;
        match self {
            Var(_) => unreachable!("kind variables should be resolved"),
            Atomic(_) => Err(ErrorCause::KindApplicationError(
                Self::clone(self),
                Self::clone(applicant),
            )),
            Composite(a, b) => {
                if &**a == applicant {
                    Ok(Self::clone(b))
                } else {
                    Err(ErrorCause::KindsMismatch(
                        Self::clone(a),
                        Self::clone(applicant),
                    ))
                }
            }
        }
    }
}

impl<AT: Clone> CompositeExpression<AT> {
    /// Remap existing generic variables into local type variables.
    pub fn remap_vars(&self, allocator: &TypeVarAllocator) -> Self {
        use CompositeExpression::*;
        match self {
            Atomic(_) => CompositeExpression::clone(&self),
            Var(n) => Var(allocator.map_existing(*n)),
            Composite(a, b) => Composite(
                Box::new(a.remap_vars(allocator)),
                Box::new(b.remap_vars(allocator)),
            ),
        }
    }

    /// Rename free variables in a type expression using a mapping (old number -> new number).
    pub fn rename_vars(self, mapping: &HashMap<usize, usize>) -> Self {
        use CompositeExpression::*;
        match self {
            Atomic(_) => self,
            Var(n) => Var(mapping[&n]),
            Composite(a, b) => Composite(
                Box::new(a.rename_vars(mapping)),
                Box::new(b.rename_vars(mapping)),
            ),
        }
    }

    /// Substitute variable with its value in a type expression.
    pub fn substitute(&mut self, var_index: usize, value: &CompositeExpression<AT>) {
        use CompositeExpression::*;
        match self {
            Atomic(_) => (),
            Var(n) if *n == var_index => *self = CompositeExpression::clone(value),
            Var(_) => (),
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
            Var(_) => false,
            Composite(a, b) => a.is_fixed() && b.is_fixed(),
        }
    }

    /// Find maximum variable index in a type expression. Returns None if expression contains no variables.
    pub fn get_max_var_index(&self) -> Option<usize> {
        use CompositeExpression::*;
        match self {
            Var(n) => Some(*n),
            Atomic(_) => None,
            Composite(a, b) => max_options(a.get_max_var_index(), b.get_max_var_index()),
        }
    }
}

impl CompositeExpression<AtomicType> {
    pub fn create_kind_rules(
        &self,
        tva: &mut TypeVarAllocator,
        context: &TypeContext<KindExpression>,
        solver: &mut Solver<AtomicKind>,
    ) -> Result<usize, ErrorCause> {
        use CompositeExpression::*;
        let my_index = tva.allocate(&Position::Unknown);
        match self {
            Atomic(a) => {
                solver.add_rule(my_index, a.get_kind(context)?);
            }
            Var(n) => {
                solver.add_rule(my_index, KindExpression::Var(tva.map_existing(*n)));
            }
            Composite(a, b) => {
                let a_index = a.create_kind_rules(tva, context, solver)?;
                let b_index = b.create_kind_rules(tva, context, solver)?;
                solver.add_rule(
                    a_index,
                    KindExpression::Composite(
                        Box::new(KindExpression::Var(b_index)),
                        Box::new(KindExpression::Var(my_index)),
                    ),
                );
            }
        };
        Ok(my_index)
    }

    pub fn check_constraint(&self) -> Result<(), ErrorCause> {
        use CompositeExpression::*;
        // TODO kinds
        match self {
            Var(_) | Atomic(_) => Err(ErrorCause::NotAConstraint(TypeExpression::clone(self))),
            Composite(a, b) => match &**a {
                Atomic(t) if *t == AtomicType::Num => match &**b {
                    Var(_) => Ok(()),
                    Atomic(t) if matches!(t, AtomicType::Int(_)) => Ok(()),
                    _ => Err(ErrorCause::TypeConstraintMismatch),
                },
                _ => Err(ErrorCause::NotAConstraint(TypeExpression::clone(self))),
            },
        }
    }
}

impl IntType {
    pub fn new(signed: bool, bits: IntBits) -> Self {
        Self { signed, bits }
    }
}

impl AtomicType {
    fn get_kind(
        &self,
        context: &TypeContext<KindExpression>,
    ) -> Result<KindExpression, ErrorCause> {
        use AtomicType::*;
        match self {
            Int(_) => Ok(KindExpression::Atomic(AtomicKind::Type)),
            // * -> * -> *
            // (*, (*, *))
            Function => Ok(KindExpression::mapping(
                KindExpression::Atomic(AtomicKind::Type),
                KindExpression::mapping(
                    KindExpression::Atomic(AtomicKind::Type),
                    KindExpression::Atomic(AtomicKind::Type),
                ),
            )),
            // * -> Constraint
            // (*, Constraint)
            Num => Ok(KindExpression::mapping(
                KindExpression::Atomic(AtomicKind::Type),
                KindExpression::Atomic(AtomicKind::Constraint),
            )),
            User(s) => context
                .get(s)
                .map(|e| KindExpression::clone(e))
                .ok_or(ErrorCause::UnknownIdentifier(s.to_string())),
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
                        _ => return Ok(AtomicType::User(s.to_string())),
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
            Var(n) => f.write_str(&var_from_number(*n)),
            Composite(a, b) => match **a {
                Atomic(AtomicType::Function) => match **b {
                    Atomic(_) | Var(_) => write!(f, "{} ->", b),
                    Composite(_, _) => write!(f, "({}) ->", b),
                },
                _ => write!(f, "{} {}", a, b),
            },
        }
    }
}

impl fmt::Display for KindExpression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use CompositeExpression::*;
        match self {
            Atomic(t) => write!(f, "{}", t),
            Var(n) => f.write_str(&var_from_number(*n)),
            Composite(a, b) => match **b {
                Var(_) | Atomic(_) => write!(f, "{} -> {}", a, b),
                _ => write!(f, "{} -> ({})", a, b),
            },
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

impl fmt::Display for AtomicKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use AtomicKind::*;
        match self {
            Type => f.write_str("*"),
            Constraint => f.write_str("Constraint"),
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
