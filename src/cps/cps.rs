use std::fmt;
use crate::ast::ExpressionVariant;
use crate::ast::type_info::TypeExpression;
use crate::ast::Expression;
use crate::ast::Binding;
use crate::ast::type_info::IntType;
use super::var_allocator::VarAllocator;

#[derive(Debug)]
pub enum Value {
    Var(Var),
    IntConstant(u64, IntType),
}

#[derive(Debug, Clone)]
pub enum Var {
    User(String),
    Auto(usize),
}

pub enum Cexp {
    App3(Var, Value, Value), // f x k
    App2(Var, Value), // k x
    Let(Var, Box<Aexp>, Box<Cexp>), // let x = e1 in e2
}

pub enum Aexp {
    Val(Value),
    Abs2(Var, Var, Box<Cexp>), // \x k -> e
    Abs1(Var, Box<Cexp>), // \x -> e
}

impl Cexp {
    fn from_expression(e: Expression<TypeExpression, String>, c: Var, allocator: &mut VarAllocator) -> Self {
        use ExpressionVariant::*;
        match e.e {
            Variable(_) | IntConstant(_) => {
                let v = Value::from_expression(e).unwrap();
                Cexp::App2(c, v)
            }
            Abstraction(l) => {
                // [[\x -> e | c]] = c (\x k -> [[e | k]])
                let k = Var::alloc(allocator);
                let (var_name, body) = l.explode();
                let cbody = Cexp::from_expression(body, Var::clone(&k), allocator);
                let x = Var::User(var_name);
                let new_lambda = Aexp::Abs2(x, k, Box::new(cbody));
                let tmp = Var::alloc(allocator);
                Cexp::Let(Var::clone(&tmp),
                    Box::new(new_lambda),
                    Box::new(Cexp::App2(c, Value::Var(tmp))))
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
                let either_f = into_cexp_if_needed(*f, allocator);
                let either_e = into_cexp_if_needed(*e, allocator);
                use EitherExpr::*;
                match (either_f, either_e) {
                    (Val(f), Val(e)) => {
                        // f atomic, e atomic => f' e c
                        let fvar = f.try_into_var().unwrap(); // function must be a var here, can't be an int
                        Cexp::App3(fvar, e, Value::Var(c))
                    }
                    (Val(f), Complex(k, e)) => {
                        // f atomic, e complex =>
                        //     let k' = \v -> f' v c
                        //     in [[e|k']]
                        let fvar = f.try_into_var().unwrap(); // function must be a var here, can't be an int
                        let v = Var::alloc(allocator);
                        let lambda = Aexp::Abs1(Var::clone(&v), Box::new(Cexp::App3(fvar, Value::Var(v), Value::Var(c))));
                        Cexp::Let(k, Box::new(lambda), Box::new(e))
                    }
                    (Complex(k, f), Val(e)) => {
                        // f complex, e atomic =>
                        //     let k' = \v -> v e c
                        //     in [[f|k']]    
                        let v = Var::alloc(allocator);
                        let lambda = Aexp::Abs1(Var::clone(&v),
                            Box::new(Cexp::App3(v, e, Value::Var(c))));
                        Cexp::Let(k, Box::new(lambda), Box::new(f))
                    }
                    (Complex(kf, f), Complex(ke, e)) => {
                        // f complex, e complex =>
                        // let ke = \v ->
                        //   let kf = \w -> w v c
                        //   in [[f|kf]]
                        // in [[e|ke]]

                        let v = Var::alloc(allocator);
                        let w = Var::alloc(allocator);
                        let lambda_kf = Aexp::Abs1(Var::clone(&w),
                            Box::new(Cexp::App3(w, Value::Var(Var::clone(&v)), Value::Var(c))));
                        let lambda_ke = Aexp::Abs1(Var::clone(&v),
                            Box::new(Cexp::Let(kf, Box::new(lambda_kf), Box::new(f))));
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
                let x = Var::from_binding(x);
                match into_cexp_if_needed(*v, allocator) {
                    EitherExpr::Val(v) => {
                        Cexp::Let(x, Box::new(Aexp::Val(v)), Box::new(Cexp::from_expression(*e, c, allocator)))
                    }
                    EitherExpr::Complex(k, v) => {
                        let lambda = Aexp::Abs1(x, Box::new(Cexp::from_expression(*e, c, allocator)));
                        Cexp::Let(k, Box::new(lambda), Box::new(v))
                    }
                }
            }
            _ => todo!(),
        }
    }
}

enum EitherExpr {
    Val(Value),
    Complex(Var, Cexp)
}

fn into_cexp_if_needed(e: Expression<TypeExpression, String>, allocator: &mut VarAllocator) -> EitherExpr {
    use ExpressionVariant::*;
    match e.e {
        Variable(_) | IntConstant(_) => {
            let v = Value::from_expression(e).unwrap();
            EitherExpr::Val(v)
        }
        _ => {
            let k = Var::alloc(allocator);
            let e = Cexp::from_expression(e, Var::clone(&k), allocator);
            EitherExpr::Complex(k, e)
        }
    }
}

impl Value {
    fn from_expression(e: Expression<TypeExpression, String>) -> Option<Self> {
        use ExpressionVariant::*;
        match e.e {
            Variable(s) => Some(Value::Var(Var::User(s))),
            IntConstant(val) => {
                let t = e.t.try_into_atomic().unwrap().try_into_int_type().unwrap();
                Some(Value::IntConstant(val, t))
            }
            _ => None
        }
    }

    fn try_into_var(self) -> Result<Var, Self> {
        use Value::*;
        match self {
            Var(v) => Ok(v),
            _ => Err(self)
        }
    }
}

impl Var {
    fn alloc(allocator: &mut VarAllocator) -> Self {
        Var::Auto(allocator.alloc())
    }

    fn from_binding(b: Binding<TypeExpression, String>) -> Self {
        Var::User(b.name)
    }
}

impl fmt::Display for Var {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Var::User(s) => f.write_str(s),
            Var::Auto(n) => write!(f, "_{n}"),
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
