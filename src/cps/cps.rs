use crate::ast::type_info::IntType;
use crate::ast::ConcreteType;
use crate::ast::Expression;
use crate::ast::ExpressionVariant;
use crate::ast::MangledId;
use std::fmt;

#[derive(Debug)]
pub enum Value {
    Var(MangledId),
    IntConstant(u64, IntType),
}

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
                let mut result: Vec<(Value, usize)> = Vec::new();
                let mut closures: Vec<(MangledId, MangledId, Cexp)> = Vec::new();
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
                let core = Cexp::Let {
                    x: tuple_var.to_owned(),
                    e1: Box::new(Aexp::Tuple(result)),
                    e2: Box::new(Cexp::App2 {
                        k: c,
                        x: Value::Var(tuple_var),
                    }),
                };
                // let tuple = closures
                //     .into_iter()
                //     .fold(core, |acc, (k, e_var, e)| {
                //         Cexp::Let { x: k,
                //             e1: Aexp::Abs1(e_var, Box::new(acc)), e2: e }
                //         todo!()
                //     });
                todo!()
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
                f.write_str("(");
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

    #[test]
    fn test_cps() {
        panic!();
    }
}
