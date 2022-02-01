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
    App3(MangledId, Value, Value),        // f x k
    App2(MangledId, Value),               // k x
    Let(MangledId, Box<Aexp>, Box<Cexp>), // let x = e1 in e2
    Tuple(Vec<(MangledId, usize)>, Box<Cexp>),
    Extract(MangledId, usize, usize, Box<Cexp>),
}

pub enum Aexp {
    Val(Value),
    Abs2(MangledId, MangledId, Box<Cexp>), // \x k -> e
    Abs1(MangledId, Box<Cexp>),            // \x -> e
}

impl Cexp {
    fn from_expression(e: Expression<ConcreteType, MangledId>, c: MangledId) -> Self {
        use ExpressionVariant::*;
        match e.e {
            Variable(_) | IntConstant(_) => {
                let v = Value::from_expression(e).unwrap();
                Cexp::App2(c, v)
            }
            Abstraction(l) => {
                // [[\x -> e | c]] = c (\x k -> [[e | k]])
                let k = MangledId::new_auto();
                let (x, body) = l.explode();
                let cbody = Cexp::from_expression(body, k.to_owned());
                let new_lambda = Aexp::Abs2(x, k, Box::new(cbody));
                let tmp = MangledId::new_auto();
                Cexp::Let(
                    tmp.to_owned(),
                    Box::new(new_lambda),
                    Box::new(Cexp::App2(c, Value::Var(tmp))),
                )
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
                        Cexp::App3(fvar, e, Value::Var(c))
                    }
                    (Val(f), Complex(k, e)) => {
                        // f atomic, e complex =>
                        //     let k' = \v -> f' v c
                        //     in [[e|k']]
                        let fvar = f.try_into_id().unwrap(); // function must be a var here, can't be an int
                        let v = MangledId::new_auto();
                        let lambda = Aexp::Abs1(
                            v.to_owned(),
                            Box::new(Cexp::App3(fvar, Value::Var(v), Value::Var(c))),
                        );
                        Cexp::Let(k, Box::new(lambda), Box::new(e))
                    }
                    (Complex(k, f), Val(e)) => {
                        // f complex, e atomic =>
                        //     let k' = \v -> v e c
                        //     in [[f|k']]
                        let v = MangledId::new_auto();
                        let lambda =
                            Aexp::Abs1(v.to_owned(), Box::new(Cexp::App3(v, e, Value::Var(c))));
                        Cexp::Let(k, Box::new(lambda), Box::new(f))
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
                            Box::new(Cexp::App3(w, Value::Var(v.to_owned()), Value::Var(c))),
                        );
                        let lambda_ke = Aexp::Abs1(
                            v.to_owned(),
                            Box::new(Cexp::Let(kf, Box::new(lambda_kf), Box::new(f))),
                        );
                        Cexp::Let(ke, Box::new(lambda_ke), Box::new(e))
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
                    EitherExpr::Val(v) => Cexp::Let(
                        x,
                        Box::new(Aexp::Val(v)),
                        Box::new(Cexp::from_expression(*e, c)),
                    ),
                    EitherExpr::Complex(k, v) => {
                        let lambda = Aexp::Abs1(x, Box::new(Cexp::from_expression(*e, c)));
                        Cexp::Let(k, Box::new(lambda), Box::new(v))
                    }
                }
            }
            Record(..) => todo!(),
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
        }
    }
}

impl fmt::Display for Cexp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Cexp::App2(g, e) => write!(f, "{g} {e}"),
            Cexp::App3(g, e, k) => write!(f, "{g} {e} {k}"),
            Cexp::Let(x, b, e) => write!(f, "let {x} = {b} in {e}"),
            Cexp::Tuple(v, k) => {
                write!(f, "{k} (")?;
                for (var, _size) in v.iter() {
                    write!(f, "{var},")?;
                }
                f.write_str(")")
            }
            Cexp::Extract(var, offset, _size, k) => write!(f, "{k} {var}[{offset}]")
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
