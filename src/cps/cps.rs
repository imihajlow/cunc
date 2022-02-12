use crate::ast::type_info::IntType;
use crate::ast::ConcreteType;
use crate::ast::Expression;
use crate::ast::ExpressionVariant;
use crate::ast::MangledId;
use std::fmt;

#[derive(Debug, PartialEq)]
pub enum Value {
    Var(MangledId),
    IntConstant(u64, IntType),
}

#[derive(Debug, PartialEq)]
pub enum Cexp {
    App3 {
        f: MangledId,
        x: Value,
        k: MangledId,
    }, // f x k
    App2 {
        k: MangledId,
        x: Value,
    }, // k x
    Let {
        x: MangledId,
        e1: Box<Aexp>,
        e2: Box<Cexp>,
    }, // let x = e1 in e2
    Extract(MangledId, usize, usize, Box<Cexp>),
}

#[derive(Debug, PartialEq)]
pub enum Aexp {
    Val(Value),
    Abs2(MangledId, MangledId, Box<Cexp>), // \x k -> e
    Abs1(MangledId, Box<Cexp>),            // \x -> e
    Tuple(Vec<(Value, usize)>),            // (e1, e2, ...)
}

impl Cexp {
    fn from_expression(e: Expression<ConcreteType, MangledId>, c: MangledId) -> Self {
        use ExpressionVariant::*;
        match e.e {
            Variable(_) | IntConstant(_) => {
                let v = Value::from_expression(e).unwrap();
                Cexp::App2 { k: c, x: v }
            }
            Abstraction(l) => {
                // [[\x -> e | c]] = c (\x k -> [[e | k]])
                let k = MangledId::new_auto();
                let (x, body) = l.explode();
                let cbody = Cexp::from_expression(body, k.to_owned());
                let new_lambda = Aexp::Abs2(x, k, Box::new(cbody));
                let tmp = MangledId::new_auto();
                Cexp::Let {
                    x: tmp.to_owned(),
                    e1: Box::new(new_lambda),
                    e2: Box::new(Cexp::App2 {
                        k: c,
                        x: Value::Var(tmp),
                    }),
                }
            }
            Application(f, e) => {
                /*
                [[f e|c]] =
                    f atomic, e atomic => f' e c
                    f atomic, e complex =>
                        let k' = \v -> f' v c
                        in [[e|k']]
                    f complex, e atomic =>
                        let k' = \v -> v e c
                        in [[f|k']]
                    f complex, e complex =>
                        let k' = \v ->
                          let k'' = \w -> w v c
                          in [[f|k'']]
                        in [[e|k']]
                */
                let either_f = into_cexp_if_needed(*f);
                let either_e = into_cexp_if_needed(*e);
                use EitherExpr::*;
                match (either_f, either_e) {
                    (Val(f), Val(e)) => {
                        // f atomic, e atomic => f' e c
                        let fvar = f.try_into_id().unwrap(); // function must be a var here, can't be an int
                        Cexp::App3 {
                            f: fvar,
                            x: e,
                            k: c,
                        }
                    }
                    (Val(f), Complex(k, e)) => {
                        // f atomic, e complex =>
                        //     let k' = \v -> f' v c
                        //     in [[e|k']]
                        let fvar = f.try_into_id().unwrap(); // function must be a var here, can't be an int
                        let v = MangledId::new_auto();
                        let lambda = Aexp::Abs1(
                            v.to_owned(),
                            Box::new(Cexp::App3 {
                                f: fvar,
                                x: Value::Var(v),
                                k: c,
                            }),
                        );
                        Cexp::Let {
                            x: k,
                            e1: Box::new(lambda),
                            e2: Box::new(e),
                        }
                    }
                    (Complex(k, f), Val(e)) => {
                        // f complex, e atomic =>
                        //     let k' = \v -> v e c
                        //     in [[f|k']]
                        let v = MangledId::new_auto();
                        let lambda =
                            Aexp::Abs1(v.to_owned(), Box::new(Cexp::App3 { f: v, x: e, k: c }));
                        Cexp::Let {
                            x: k,
                            e1: Box::new(lambda),
                            e2: Box::new(f),
                        }
                    }
                    (Complex(kf, f), Complex(ke, e)) => {
                        // f complex, e complex =>
                        // let ke = \v ->
                        //   let kf = \w -> w v c
                        //   in [[f|kf]]
                        // in [[e|ke]]

                        let v = MangledId::new_auto();
                        let w = MangledId::new_auto();
                        let lambda_kf = Aexp::Abs1(
                            w.to_owned(),
                            Box::new(Cexp::App3 {
                                f: w,
                                x: Value::Var(v.to_owned()),
                                k: c,
                            }),
                        );
                        let lambda_ke = Aexp::Abs1(
                            v.to_owned(),
                            Box::new(Cexp::Let {
                                x: kf,
                                e1: Box::new(lambda_kf),
                                e2: Box::new(f),
                            }),
                        );
                        Cexp::Let {
                            x: ke,
                            e1: Box::new(lambda_ke),
                            e2: Box::new(e),
                        }
                    }
                }
            }
            Let(x, v, e) => {
                // [[let x = v in e|c]] =
                //     v atomic  => let x = v in [[e|c]]
                //     v complex =>
                //         let k = \x -> [[e|c]]
                //         in [[v|k]]
                let x = x.name;
                match into_cexp_if_needed(*v) {
                    EitherExpr::Val(v) => Cexp::Let {
                        x,
                        e1: Box::new(Aexp::Val(v)),
                        e2: Box::new(Cexp::from_expression(*e, c)),
                    },
                    EitherExpr::Complex(k, v) => {
                        let lambda = Aexp::Abs1(x, Box::new(Cexp::from_expression(*e, c)));
                        Cexp::Let {
                            x: k,
                            e1: Box::new(lambda),
                            e2: Box::new(v),
                        }
                    }
                }
            }
            Record(v) => {
                // [[(e1,e2,...) | c]]

                // Tuple is constructed from this.
                let mut result: Vec<(Value, usize)> = Vec::new();

                // Closures needed to compute non-trivial tuple entries.
                // Pairs are (continuation_var, tuple_var, cexp)
                let mut closures: Vec<(MangledId, MangledId, Cexp)> = Vec::new(); // Closures need
                for e in v.into_iter() {
                    let size = e.t.get_size();
                    match into_cexp_if_needed(e) {
                        EitherExpr::Val(v) => {
                            result.push((v, size));
                        }
                        EitherExpr::Complex(k, e) => {
                            // let k = \e_var -> c (.., e_var, ..) in [[e|k]]
                            let e_var = MangledId::new_auto();
                            result.push((Value::Var(e_var.to_owned()), size));
                            closures.push((k, e_var, e));
                        }
                    }
                }
                let tuple_var = MangledId::new_auto();
                // "let tuple_var = Tuple(result) in k tuple_var"
                let core = Cexp::Let {
                    x: tuple_var.to_owned(),
                    e1: Box::new(Aexp::Tuple(result)),
                    e2: Box::new(Cexp::App2 {
                        k: c,
                        x: Value::Var(tuple_var),
                    }),
                };

                /*
                    let continuation_var = \tuple_var -> core in cexp
                */

                closures
                    .into_iter()
                    .fold(core, |core, (continuation, tuple_var, cexp)| Cexp::Let {
                        x: continuation,
                        e1: Box::new(Aexp::Abs1(tuple_var, Box::new(core))),
                        e2: Box::new(cexp),
                    })
            }
            Offset(..) => todo!(),
            Switch(..) => todo!(),
            Pmatch(..) => unreachable!(),
        }
    }
}

enum EitherExpr {
    Val(Value),
    Complex(MangledId, Cexp),
}

fn into_cexp_if_needed(e: Expression<ConcreteType, MangledId>) -> EitherExpr {
    use ExpressionVariant::*;
    match e.e {
        Variable(_) | IntConstant(_) => {
            let v = Value::from_expression(e).unwrap();
            EitherExpr::Val(v)
        }
        _ => {
            let k = MangledId::new_auto();
            let e = Cexp::from_expression(e, k.to_owned());
            EitherExpr::Complex(k, e)
        }
    }
}

impl Value {
    fn from_expression(e: Expression<ConcreteType, MangledId>) -> Option<Self> {
        use ExpressionVariant::*;
        match e.e {
            Variable(s) => Some(Value::Var(s)),
            IntConstant(val) => {
                let t = e.t.try_into_int_type().unwrap();
                Some(Value::IntConstant(val, t))
            }
            _ => None,
        }
    }

    fn try_into_id(self) -> Result<MangledId, Self> {
        use Value::*;
        match self {
            Var(v) => Ok(v),
            _ => Err(self),
        }
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Var(v) => write!(f, "{v}"),
            Value::IntConstant(n, _) => write!(f, "{n}"),
        }
    }
}

impl fmt::Display for Aexp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Aexp::Val(v) => write!(f, "{v}"),
            Aexp::Abs1(v, e) => write!(f, "\\{v} -> {e}"),
            Aexp::Abs2(v, k, e) => write!(f, "\\{v} {k} -> {e}"),
            Aexp::Tuple(e) => {
                f.write_str("(")?;
                for (var, _size) in e.iter() {
                    write!(f, "{var},")?;
                }
                f.write_str(")")
            }
        }
    }
}

impl fmt::Display for Cexp {
    fn fmt(&self, fm: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Cexp::App2 { k, x } => write!(fm, "{k} {x}"),
            Cexp::App3 { f, x, k } => write!(fm, "{f} {x} {k}"),
            Cexp::Let { x, e1, e2 } => write!(fm, "let {x} = {e1} in {e2}"),
            Cexp::Extract(var, offset, _size, k) => write!(fm, "{k} {var}[{offset}]"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::type_info::IntBits;
    use crate::position::Position;

    #[test]
    fn test_app2() {
        let u8_type = ConcreteType::Int(IntType::new(false, IntBits::B8));
        let fn_type =
            ConcreteType::Function(Box::new(u8_type.to_owned()), Box::new(u8_type.to_owned()));
        let expr = Expression::<ConcreteType, MangledId> {
            t: u8_type.to_owned(),
            p: Position::Unknown,
            e: ExpressionVariant::Application(
                Box::new(Expression {
                    t: fn_type.to_owned(),
                    p: Position::Unknown,
                    e: ExpressionVariant::Variable(MangledId::Local("f".to_string())),
                }),
                Box::new(Expression {
                    t: u8_type.to_owned(),
                    p: Position::Unknown,
                    e: ExpressionVariant::Variable(MangledId::Local("x".to_string())),
                }),
            ),
        };
        let cexp = Cexp::from_expression(expr, MangledId::Local("k".to_string()));
        assert_eq!(
            cexp,
            Cexp::App3 {
                f: MangledId::Local("f".to_string()),
                x: Value::Var(MangledId::Local("x".to_string())),
                k: MangledId::Local("k".to_string())
            }
        );
    }

    #[test]
    fn test_app3() {
        let u8_type = ConcreteType::Int(IntType::new(false, IntBits::B8));
        let fn_inner_type =
            ConcreteType::Function(Box::new(u8_type.to_owned()), Box::new(u8_type.to_owned()));
        let fn_type = ConcreteType::Function(
            Box::new(u8_type.to_owned()),
            Box::new(fn_inner_type.to_owned()),
        );
        let inner_app = Expression::<ConcreteType, MangledId> {
            t: fn_inner_type.to_owned(),
            p: Position::Unknown,
            e: ExpressionVariant::Application(
                Box::new(Expression {
                    t: fn_type.to_owned(),
                    p: Position::Unknown,
                    e: ExpressionVariant::Variable(MangledId::Local("f".to_string())),
                }),
                Box::new(Expression {
                    t: u8_type.to_owned(),
                    p: Position::Unknown,
                    e: ExpressionVariant::Variable(MangledId::Local("x".to_string())),
                }),
            ),
        };
        let expr = Expression::<ConcreteType, MangledId> {
            t: u8_type.to_owned(),
            p: Position::Unknown,
            e: ExpressionVariant::Application(
                Box::new(inner_app),
                Box::new(Expression {
                    t: u8_type.to_owned(),
                    p: Position::Unknown,
                    e: ExpressionVariant::Variable(MangledId::Local("y".to_string())),
                }),
            ),
        };
        let cexp = Cexp::from_expression(expr, MangledId::Local("k".to_string()));
        /* 
            let auto_k = \auto_f -> auto_f y k in f x auto_k
        */
        println!("{}", cexp);
        if let Cexp::Let { x: k, e1, e2 } = cexp {
            assert_eq!(
                *e2,
                Cexp::App3 {
                    f: MangledId::Local("f".to_string()),
                    x: Value::Var(MangledId::Local("x".to_string())),
                    k
                }
            );
            if let Aexp::Abs1(inner_k, body) = *e1 {
                assert_eq!(
                    *body,
                    Cexp::App3 {
                        f: inner_k,
                        x: Value::Var(MangledId::Local("y".to_string())),
                        k: MangledId::Local("k".to_string())
                    }
                );
            } else {
                panic!();
            }
        } else {
            panic!();
        }
    }
}
