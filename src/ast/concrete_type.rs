use std::os::unix::prelude::CommandExt;

use crate::ast::ast::Function;
use crate::error::ErrorCause;

use super::ast::Module;
use super::type_info::{AtomicType, CompositeExpression, IntType, TypeExpression};
use super::type_solver::Solution;

#[derive(Debug, Clone, PartialEq)]
pub enum ConcreteType {
    Int(IntType),
    Tuple(Vec<ConcreteType>),
    Enum(Vec<(u8, ConcreteType)>),
    Function(Box<ConcreteType>, Box<ConcreteType>),
}

impl ConcreteType {
    pub(super) fn new(t: &TypeExpression, m: &Module<TypeExpression>) -> Result<Self, ErrorCause> {
        use CompositeExpression::*;
        match t {
            Atomic(a) => {
                use AtomicType::*;
                match a {
                    Int(i) => Ok(ConcreteType::Int(i.to_owned())),
                    _ => unreachable!("{a}"),
                }
            }
            Var(_) => Err(ErrorCause::UnresolvedGenericVars),
            Composite(_, _) => {
                let mut vhead = t.uncurry();
                let tail = vhead.split_off(1);
                // let rtail: Result<Vec<_>, _> = vhead
                //     .split_off(1)
                //     .into_iter()
                //     .map(|t| Self::new(&t, m))
                //     .collect();
                // let tail = rtail?;
                let head = *vhead.first().unwrap();
                match head {
                    Atomic(AtomicType::Function) => {
                        assert!(tail.len() == 2);
                        let a = ConcreteType::new(&tail[0], m)?;
                        let b = ConcreteType::new(&tail[1], m)?;
                        Ok(ConcreteType::Function(Box::new(a), Box::new(b)))
                    }
                    Atomic(AtomicType::User(user_type_name)) => {
                        let user_type = m.get_type(&user_type_name).unwrap();
                        user_type.as_concrete_type(
                            tail.iter().map(|t| CompositeExpression::clone(t)).collect(),
                            m,
                        )
                    }
                    Atomic(_) => unreachable!("{head}"),
                    Var(_) => Err(ErrorCause::UnresolvedGenericVars),
                    _ => unreachable!("{head}"),
                }
            }
        }
    }

    pub fn get_size(&self) -> usize {
        use ConcreteType::*;
        match self {
            Int(t) => t.get_size(),
            Tuple(v) => v.iter().map(|t| t.get_size()).sum(),
            Enum(v) => match v.len() {
                0 => 0,
                1 => v[0].1.get_size(), // enum with one variant, flag is omitted
                2..=255 => v.iter().map(|(_, t)| 1 + t.get_size()).max().unwrap(),
                _ => unreachable!(),
            },
            Function(_, _) => 4, // TODO
        }
    }
}

#[cfg(test)]
mod tests {
    use super::super::parse::parse_str;
    use super::super::scope::TypeScope;
    use super::super::type_info::{IntBits, IntType};
    use super::*;

    #[test]
    fn test_concrete_type_enum() {
        let code = "
        data Foo a b c = Bar a b c | Baz b | Bag a b.

        [U8]
        x = 2.

        y = Bar x x x.
        ";
        let mut module = parse_str(code).unwrap();
        module.generate_type_constructors();
        let typed = module.deduce_types(&TypeScope::new()).unwrap();
        let y = typed.get_function("y").unwrap();
        let yt = &y.body.t;
        let concrete_yt = ConcreteType::new(&yt, &typed).unwrap();

        use ConcreteType::*;
        assert_eq!(
            concrete_yt,
            Enum(vec![
                (
                    0,
                    Tuple(vec![
                        Int(IntType::new(false, IntBits::B8)),
                        Int(IntType::new(false, IntBits::B8)),
                        Int(IntType::new(false, IntBits::B8)),
                    ])
                ),
                (
                    1,
                    Int(IntType::new(false, IntBits::B8))
                ),
                (
                    2,
                    Tuple(vec![
                        Int(IntType::new(false, IntBits::B8)),
                        Int(IntType::new(false, IntBits::B8)),
                    ])
                ),
            ])
        );
    }
}
