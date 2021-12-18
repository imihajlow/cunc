use std::fmt;
use itertools::Itertools;
use crate::type_context::TypeContext;
use crate::position::Position;
use crate::error::Error;
use crate::error::ErrorCause;
use crate::type_info::*;

pub enum Expression<Inner> {
    Application(Vec<Inner>),
    IntConstant(u64),
    Variable(String),
    Abstraction(Lambda<Inner>)
}

pub struct UntypedExpression {
    e: Expression<UntypedExpression>,
    p: Position,
}

pub struct TypedExpression {
    t: CuncType,
    e: Expression<TypedExpression>,
    p: Position,
}

pub struct Lambda<Inner> {
    params: Vec<Binding>,
    statements: Vec<Statement<Inner>>,
    tail: Box<Inner>,
    p: Position
}

#[derive(Clone)]
pub struct Binding {
    name: String,
    t: CuncType,
    p: Position,
}

pub enum Statement<Inner> {
    Expr(Box<Inner>),
    Let(Binding, Box<Inner>)
}

pub struct Function<Inner> {
    name: String,
    body: Lambda<Inner>,
    p: Position
}

pub struct Module<Inner> {
    functions: Vec<Function<Inner>>
}

impl<Inner: fmt::Display> fmt::Display for Expression<Inner> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Application(parts) => {
                f.write_str("(")?;
                for part in parts {
                    write!(f, "{} ", part)?;
                }
                f.write_str(")")
            }
            Self::IntConstant(x) => {
                write!(f, "{}", x)
            }
            Self::Variable(name) => {
                write!(f, "{}", name)
            }
            Self::Abstraction(fun) => {
                write!(f, "{}", fun)
            }
        }
    }
}

impl fmt::Display for UntypedExpression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.e)
    }
}

impl fmt::Display for TypedExpression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.e, self.t)
    }
}

impl<Inner: fmt::Display> fmt::Display for Lambda<Inner> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("(")?;
        for s in self.params.iter().map(|p| format!("{}", p)).intersperse(", ".to_string()) {
            f.write_str(&s)?;
        }
        f.write_str(") {\n")?;
        for s in self.statements.iter().map(|p| format!("{}", p)).intersperse(";\n".to_string()) {
            f.write_str(&s)?;
        }
        write!(f, "{}", self.tail)?;
        f.write_str("}")
    }
}

impl fmt::Display for Binding {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", &self.name, &self.t)
    }
}

impl<Inner: fmt::Display> fmt::Display for Statement<Inner> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Expr(e) => write!(f, "{}", e),
            Self::Let(b, e) => write!(f, "let {} = {}", b, e)
        }
    }
}

impl<Inner: fmt::Display> fmt::Display for Function<Inner> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "def {} = {}", self.name, self.body)
    }
}

impl<Inner: fmt::Display> fmt::Display for Module<Inner> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for fun in self.functions.iter() {
            write!(f, "{}\n\n", fun)?;
        }
        Ok(())
    }
}

fn match_types(outer_type: &CuncType, inner_expr: &TypedExpression) -> Result<(), Error> {
    if outer_type != &inner_expr.t {
        Err(Error::new(ErrorCause::TypesMismatch(
            CuncType::clone(&inner_expr.t),
            CuncType::clone(outer_type)), Position::clone(&inner_expr.p)))
    } else {
        Ok(())
    }
}

pub fn annotate(expr: UntypedExpression, context: &TypeContext) -> Result<TypedExpression, Error> {
    use Expression::*;
    match expr.e {
        Application(parts) => {
            Ok(if parts.len() == 0 {
                // WTF? TODO
                TypedExpression {
                    t: CuncType::Atomic(AtomicType::Void),
                    e: Expression::Application(Vec::new()),
                    p: expr.p
                }
            } else {
                let typed_parts_result : Result<Vec<_>, _> = 
                    parts.into_iter().map(|e| annotate(e, context)).collect();
                let typed_parts = typed_parts_result?;
                let mut parts_iter = typed_parts.iter();
                let head = parts_iter.next().unwrap();
                let head_type = &head.t;
                if let CuncType::Function(arg_types) = head_type {
                    let mut arg_type_iter = arg_types.iter();
                    loop {
                        let cur_part = if let Some(part) = parts_iter.next() {
                            part
                        } else {
                            break;
                        };
                        if let Some(t) = arg_type_iter.next() {
                            match_types(t, cur_part)?;
                        } else {
                            return Err(Error::new(ErrorCause::TooManyArguments, Position::clone(&cur_part.p)))
                        }
                    }
                    match collect_type(&mut arg_type_iter) {
                        Some(t) => {
                            TypedExpression {
                                t,
                                e: Expression::Application(typed_parts),
                                p: expr.p
                            }
                        }
                        None => {
                            return Err(Error::new(ErrorCause::TooManyArguments, expr.p))       
                        }
                    }
                } else {
                    return Err(Error::new(ErrorCause::NotAFunction, Position::clone(&head.p)));
                }
            })
        }
        IntConstant(x) => {
            Ok(TypedExpression {
                t: CuncType::Atomic(AtomicType::AnyNumber),
                e: Expression::IntConstant(x),
                p: expr.p
            })
        }
        Variable(name) => {
            if let Some(t) = context.get_type(&name) {
                Ok(TypedExpression {
                    t: CuncType::clone(t),
                    e: Expression::Variable(name),
                    p: expr.p
                })
            } else {
                Err(Error::new(ErrorCause::UnknownIdentifier(name), expr.p))
            }
        }
        Abstraction(Lambda {
            params,
            statements,
            tail,
            p
        }) => {
            let mut inner_context = context.push();
            for p in params.iter() {
                inner_context.set_type(&p.name, &p.t).map_err(|e| Error::new(e, Position::clone(&p.p)))?;
            }
            let mut annotated_statements: Vec<Statement<TypedExpression>> = Vec::new();
            for s in statements.into_iter() {
                annotated_statements.push(annotate_statement(s, &mut inner_context)?);
            }
            let annotated_tail: TypedExpression = annotate(*tail, &inner_context)?;
            Ok(TypedExpression {
                t: CuncType::clone(&annotated_tail.t),
                e: Abstraction(Lambda {
                    params: params,
                    statements: annotated_statements,
                    tail: Box::new(annotated_tail),
                    p
                }),
                p: expr.p
            })
        }
    }
}

pub fn annotate_statement(s: Statement<UntypedExpression>, context: &mut TypeContext) -> Result<Statement<TypedExpression>, Error> {
    use Statement::*;
    match s {
        Expr(e) => {
            Ok(Statement::Expr(Box::new(annotate(*e, context)?)))
        }
        Let(b, e) => {
            context.set_type(&b.name, &b.t).map_err(|e| Error::new(e, Position::clone(&b.p)))?;
            Ok(Statement::Let(b, Box::new(annotate(*e, &context)?)))
        }
    }
}
