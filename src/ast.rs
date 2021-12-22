
use std::collections::HashSet;
use crate::graph::ObjectGraph;
use crate::name_context::NameContext;
use std::fmt;
use itertools::Itertools;
use crate::position::Position;
use crate::type_info::TypeExpression;
use crate::type_info::TypeVars;


pub enum Expression<Inner> {
    Application(Vec<Inner>),
    IntConstant(u64),
    Variable(String),
    Abstraction(Lambda<Inner>)
}

pub trait AnyTypedExpression {
    fn get_expression(&self) -> &Expression<Self> where Self: Sized;
    fn get_position(&self) -> &Position;
}

pub struct UntypedExpression {
    e: Expression<UntypedExpression>,
    p: Position,
}

pub struct MaybeTypedExpression {
    t: Option<TypeExpression>,
    e: Expression<MaybeTypedExpression>,
    p: Position,
}

pub struct TypedExpression {
    t: TypeExpression,
    e: Expression<TypedExpression>,
    p: Position,
}

pub struct Lambda<Inner> {
    params: Vec<Binding>,
    return_type: Option<TypeExpression>,
    statements: Vec<Statement<Inner>>,
    tail: Box<Inner>,
    p: Position
}

#[derive(Clone)]
pub struct Binding {
    name: String,
    t: Option<TypeExpression>,
    p: Position,
}

pub enum Statement<Inner> {
    Expr(Box<Inner>),
    Let(Binding, Box<Inner>)
}

pub struct Function<Inner> {
    name: String,
    body: Lambda<Inner>,
    type_vars: TypeVars,
    p: Position
}

pub struct Module<Inner> {
    functions: Vec<Function<Inner>>
}

impl<Inner> Module<Inner> {
    pub fn new() -> Self {
        Self {
            functions: Vec::new()
        }
    }

    pub fn push_function(&mut self, f: Function<Inner>) {
        self.functions.push(f);
    }
}

impl<Inner> Module<Inner> where Inner: AnyTypedExpression {
    fn build_dependency_graph(&self) {
        let mut context = NameContext::new();
        for function in self.functions.iter() {
            context.add_name(&function.name);
        }
        let mut result: ObjectGraph<String> = ObjectGraph::new();
        for function in self.functions.iter() {
            let mut refs: HashSet<String> = HashSet::new();
            function.body.collect_refs(&mut context, &mut refs);
            for name in refs.into_iter() {
                result.add_edge_unique(&function.name, &name);
            }
        }

        todo!()
    }
}

impl<Inner> Expression<Inner> where Inner: AnyTypedExpression {
    /// Collect toplevel names referenced by this expression.
    fn collect_refs(&self, context: &mut NameContext, result: &mut HashSet<String>) {
        use Expression::*;
        match self {
            Application(v) => {
                for e in v.iter() {
                    e.get_expression().collect_refs(context, result);
                }
            }
            IntConstant(_) => (),
            Variable(n) => {
                if context.is_toplevel(n) {
                    result.insert(n.to_owned());
                }
            }
            Abstraction(l) => {
                l.collect_refs(context, result);
            }
        }
    }
}

impl UntypedExpression {
    pub fn new(e: Expression<UntypedExpression>, p: Position) -> Self {
        Self {
            e,
            p
        }
    }
}

impl AnyTypedExpression for UntypedExpression {
    fn get_expression(&self) -> &Expression<Self> {
        &self.e
    }

    fn get_position(&self) -> &Position {
        &self.p
    }
}

impl MaybeTypedExpression {
    pub fn new(e: Expression<MaybeTypedExpression>, p: Position) -> Self {
        Self {
            e,
            p,
            t: None
        }
    }

    pub fn new_with_type(e: Expression<MaybeTypedExpression>, p: Position, t: TypeExpression) -> Self {
        Self {
            e,
            p,
            t: Some(t)
        }
    }
}

impl AnyTypedExpression for MaybeTypedExpression {
    fn get_expression(&self) -> &Expression<Self> {
        &self.e
    }

    fn get_position(&self) -> &Position {
        &self.p
    }
}

impl AnyTypedExpression for TypedExpression {
    fn get_expression(&self) -> &Expression<Self> {
        &self.e
    }

    fn get_position(&self) -> &Position {
        &self.p
    }
}


impl<Inner> Function<Inner> {
    pub fn new(name: String, body: Lambda<Inner>, type_vars: TypeVars, p: Position) -> Self {
        Self {
            name,
            body,
            type_vars,
            p
        }
    }
}

impl Binding {
    pub fn new(name: String, t: TypeExpression, p: Position) -> Self {
        Self {
            name,
            t: Some(t),
            p
        }
    }

    pub fn new_untyped(name: String, p: Position) -> Self {
        Self {
            name,
            t: None,
            p
        }
    }

    pub fn new_with_option(name: String, t: Option<TypeExpression>, p: Position) -> Self {
        Self {
            name,
            t,
            p
        }
    }
}

impl<Inner> Statement<Inner> {
    pub fn new_expr(expr: Inner) -> Self {
        Statement::Expr(Box::new(expr))
    }

    pub fn new_let(binding: Binding, expr: Inner) -> Self {
        Statement::Let(binding, Box::new(expr))
    }
}

impl<Inner> Lambda<Inner> {
    pub fn new(params: Vec<Binding>, return_type: Option<TypeExpression>, statements: Vec<Statement<Inner>>, tail: Inner, p: Position) -> Self {
        Self {
            params,
            return_type,
            statements,
            tail: Box::new(tail),
            p
        }
    }
}


impl<Inner> Lambda<Inner> where Inner: AnyTypedExpression {
    fn collect_refs(&self, context: &mut NameContext, result: &mut HashSet<String>) {
        context.push();
        for n in self.params.iter() {
            context.add_name(&n.name);
        }
        for s in self.statements.iter() {
            use Statement::*;
            match s {
                Let(name, e) => {
                    e.get_expression().collect_refs(context, result);
                    context.add_name(&name.name);
                }
                Expr(e) => {
                    e.get_expression().collect_refs(context, result);
                }
            }
        }
        self.tail.get_expression().collect_refs(context, result);
        context.pop();
    }
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

impl fmt::Display for MaybeTypedExpression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.t {
            None => write!(f, "{}", self.e),
            Some(t) => write!(f, "{}: {}", self.e, t),
        }
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
        for s in self.statements.iter() {
            writeln!(f, "{};", &s)?;
        }
        write!(f, "{}\n", self.tail)?;
        f.write_str("}")?;
        if let Some(t) = &self.return_type {
            write!(f, " -> {}", t)?;
        }
        Ok(())
    }
}

impl fmt::Display for Binding {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.t {
            Some(t) => write!(f, "{}: {}", &self.name, t),
            None => write!(f, "{}", &self.name)
        }
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

