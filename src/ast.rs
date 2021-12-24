
use crate::error::ErrorCause;
use crate::type_constraint::TypeConstraint;
use crate::type_solver::Solution;
use crate::util::var_from_number;
use std::collections::HashMap;
use crate::error::Error;
use crate::name_context::TypeContext;
use crate::type_solver::Solver;
use crate::type_var_allocator::TypeVarAllocator;
use std::collections::HashSet;
use crate::graph::ObjectGraph;
use crate::name_context::NameContext;
use std::fmt;
use itertools::Itertools;
use crate::position::Position;
use crate::type_info::TypeExpression;
use crate::type_info::TypeVars;

/*
    Type inference system takes Module<OptionalType>,
    assigns type variables to every part of every expression producing VariableType-based objects,
    and after deducing variable values with type_solver::Solver substitutes variables with fixed types,
    producing Module<FixedType>.
 */

/// Type which can be specified or not.
#[derive(Debug, Clone)]
pub struct OptionalType(pub Option<TypeExpression>);

/// Type specified by a type variable.
#[derive(Debug, Clone)]
pub struct VariableType(pub usize);

/// Known (maybe generic) type.
#[derive(Debug, Clone)]
pub struct FixedType(pub TypeExpression);

#[derive(Debug, Clone)]
pub struct Expression<Type> {
    t: Type,
    e: ExpressionVariant<Type>,
    p: Position,
}

#[derive(Debug, Clone)]
pub enum ExpressionVariant<Type> {
    Application(Vec<Expression<Type>>),
    IntConstant(u64),
    Variable(String),
    Abstraction(Lambda<Type>)
}

#[derive(Debug, Clone)]
pub struct Lambda<Type> {
    params: Vec<Binding<Type>>,
    return_type: Type,
    statements: Vec<Statement<Type>>,
    tail: Box<Expression<Type>>,
    p: Position
}

#[derive(Debug, Clone)]
pub struct Binding<Type> {
    name: String,
    t: Type,
    p: Position,
}

#[derive(Debug, Clone)]
pub enum Statement<Type> {
    Expr(Box<Expression<Type>>),
    Let(Binding<Type>, Box<Expression<Type>>)
}

#[derive(Debug, Clone)]
pub struct Function<Type> {
    name: String,
    body: Lambda<Type>,
    type_vars: TypeVars,
    p: Position
}

#[derive(Debug, Clone)]
pub struct Module<Type> {
    functions: Vec<Function<Type>>
}

impl<Type> Module<Type> {
    pub fn new() -> Self {
        Self {
            functions: Vec::new()
        }
    }

    pub fn push_function(&mut self, f: Function<Type>) {
        self.functions.push(f);
    }
}

impl<Type> Module<Type> {
    pub fn build_dependency_graph(&self) -> ObjectGraph<String> {
        let mut context = NameContext::new();
        for function in self.functions.iter() {
            context.add_name(&function.name);
        }
        let mut result: ObjectGraph<String> = ObjectGraph::new();
        for function in self.functions.iter() {
            let mut refs: HashSet<String> = HashSet::new();
            function.body.collect_refs(&mut context, &mut refs);
            result.add_node_unique(&function.name);
            for name in refs.into_iter() {
                result.add_edge_unique(&function.name, &name);
            }
        }
        result
    }
}

/// Enum used in type context.
#[derive(Debug, Clone)]
enum TypeAssignment {
    ToplevelFunction(TypeVars, TypeExpression),
    LocalName(usize),
}

impl TypeAssignment {
    fn unwrap_local_name(&self) -> usize {
        match self {
            TypeAssignment::LocalName(x) => *x,
            _ => panic!("Not a local name: {:?}", self)
        }
    }
}

impl<> Module<OptionalType> {
    pub fn deduce_types(&self) -> Result<Module<FixedType>, Error> {
        let function_by_name: HashMap<String, &Function<_>> =
            HashMap::from_iter(self.functions.iter().map(|f| (f.name.to_string(), f)));
        let dep_graph = self.build_dependency_graph();
        let toporder = dep_graph.find_strongly_connected().inverse_topsort().unwrap();
        let mut result: Module<FixedType> = Module::new();
        let mut context: TypeContext<TypeAssignment> = TypeContext::new();
        for group in toporder.into_iter() {
            let mut local_context = context.push();
            let mut allocator = TypeVarAllocator::new();
            let mut solver = Solver::new();
            // First just assign indices to functions
            for fname in group.iter() {
                let pos = &function_by_name[fname].p;
                let index = allocator.allocate(pos);
                local_context.set(fname, &TypeAssignment::LocalName(index))
                    .map_err(|c| Error::new(c, Position::clone(pos)))?;
            }
            // Actually process functions
            let mut var_annotated_bodies: Vec<(String, Lambda<VariableType>)> = Vec::new();
            for fname in group.iter() {
                let function = function_by_name[fname];
                let index = local_context.get(fname).unwrap().unwrap_local_name();
                let function_context = local_context.push();
                allocator.enter_function(function.type_vars.get_vars_count(), &function.p);
                let (lambda, overall_type) =
                    function.body.assign_type_vars(&function_context, &mut solver, &mut allocator)?;
                solver.add_rule(index, overall_type);
                println!("{} {}\n", &fname, &lambda);
                var_annotated_bodies.push((fname.to_owned(), lambda));
                allocator.leave_function();
            }
            println!("{}", &solver);
            let solution = solver.solve().map_err(|e| e.as_error(&allocator))?;
            println!("\nSolution:\n{}", &solution);
            // Store functions in module and update context with their types
            for (name, body) in var_annotated_bodies.into_iter() {
                let deduced_body = body.translate_types(&solution);
                let new_type_vars = TypeVars::new(solution.get_free_vars_count(),
                    solution.clone_type_constraints());
                println!("\n{} {}", &name, &deduced_body);
                let old_function = function_by_name[&name];
                context.set(&name,
                    &TypeAssignment::ToplevelFunction(
                        TypeVars::clone(&new_type_vars),
                        deduced_body.get_overall_type()))
                    .map_err(|c| Error::new(c, Position::clone(&old_function.p)))?;
                let new_function: Function<FixedType> =
                    Function::new(name, deduced_body, new_type_vars, Position::clone(&old_function.p));
                result.push_function(new_function);
            }
        }
        Ok(result)
    }
}

// collect_refs
impl<Type> ExpressionVariant<Type> {
    /// Collect toplevel names referenced by this expression.
    fn collect_refs(&self, context: &mut NameContext, result: &mut HashSet<String>) {
        use ExpressionVariant::*;
        match self {
            Application(v) => {
                for e in v.iter() {
                    e.e.collect_refs(context, result);
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

impl<Type> Lambda<Type> {
    fn collect_refs(&self, context: &mut NameContext, result: &mut HashSet<String>) {
        context.push();
        for n in self.params.iter() {
            context.add_name(&n.name);
        }
        for s in self.statements.iter() {
            use Statement::*;
            match s {
                Let(name, e) => {
                    e.e.collect_refs(context, result);
                    context.add_name(&name.name);
                }
                Expr(e) => {
                    e.e.collect_refs(context, result);
                }
            }
        }
        self.tail.e.collect_refs(context, result);
        context.pop();
    }
}
// end collect_refs


// assign_type_vars
impl<> Expression<OptionalType> {
    /// Assign a new type variable to every part of the expression and to the expression itself,
    /// simultaniously adding rules to type solver.
    fn assign_type_vars(&self, context: &mut TypeContext<TypeAssignment>, solver: &mut Solver, allocator: &mut TypeVarAllocator) 
            -> Result<Expression<VariableType>, Error> {
        use ExpressionVariant::*;
        let my_var_index = allocator.allocate(&self.p);
        let my_position = Position::clone(&self.p);
        if let Some(t) = &self.t.0 {
            solver.add_rule(my_var_index, t.remap_vars(allocator));
        }
        match &self.e {
            Application(parts) => {
                let annotated_parts_r: Result<Vec<_>, Error> =
                    parts.iter().map(|t| t.assign_type_vars(context, solver, allocator)).collect();
                let annotated_parts = annotated_parts_r?;
                let mut assigned_indices_iter = annotated_parts.iter().map(|t| t.t.0);
                let head_index = assigned_indices_iter.next().unwrap();
                let mut rest_indices: Vec<_> = assigned_indices_iter.collect();
                rest_indices.push(my_var_index);
                let fn_type = TypeExpression::Function(
                    rest_indices.into_iter().map(|i| TypeExpression::Var(i)).collect());
                solver.add_rule(head_index, fn_type);
                Ok(Expression::<VariableType>::new(Application(annotated_parts), my_position, my_var_index))
            }
            IntConstant(x) => {
                solver.add_constraint(TypeConstraint::new_num(&TypeExpression::Var(my_var_index), &my_position));
                Ok(Expression::<VariableType>::new(IntConstant(*x), my_position, my_var_index))
            }
            Variable(name) => {
                match context.get(name) {
                    None => Err(Error::new(ErrorCause::UnknownIdentifier(name.to_string()), my_position)),
                    Some(a) => {
                        match a {
                            TypeAssignment::LocalName(var_index) =>
                                solver.add_rule(my_var_index, TypeExpression::Var(*var_index)),
                            TypeAssignment::ToplevelFunction(tv, te) => {
                                // Generic function. Remap generic variables.
                                allocator.enter_function(tv.get_vars_count(), &self.p);
                                solver.add_rule(my_var_index, te.remap_vars(allocator));
                                // TODO type constraints
                                allocator.leave_function();
                            }
                        }
                        Ok(Expression::<VariableType>::new(Variable(name.to_string()), my_position, my_var_index))
                    }
                }
            }
            Abstraction(_) => {
                todo!()
            }
        }
    }
}


impl<> Lambda<OptionalType> {
    /// Assign type variables, simultaniously adding rules to type solver.
    /// Returns annotated Lambda and its type.
    fn assign_type_vars(&self, context: &TypeContext<TypeAssignment>, solver: &mut Solver, allocator: &mut TypeVarAllocator) 
            -> Result<(Lambda<VariableType>, TypeExpression), Error> {
        let mut local_context = context.push();
        // Annotate params and create overall type
        let mut param_indices: Vec<usize> = Vec::new();
        let mut new_param_bindings: Vec<Binding<VariableType>> = Vec::new();
        for p in self.params.iter() {
            let index = allocator.allocate(&p.p);
            param_indices.push(index);
            local_context.set(&p.name, &TypeAssignment::LocalName(index))
                .map_err(|c| Error::new(c, Position::clone(&p.p)))?;
            if let Some(t) = &p.t.0 {
                solver.add_rule(index, t.remap_vars(allocator));
            }
            new_param_bindings.push(
                Binding::new(p.name.to_owned(), VariableType(index), Position::clone(&p.p)));
        }
        let return_type_index = allocator.allocate(&self.p);
        if let Some(t) = &self.return_type.0 {
            solver.add_rule(return_type_index, t.remap_vars(allocator));
        }
        param_indices.push(return_type_index);
        let overall_type = TypeExpression::Function(
                param_indices.into_iter().map(|i| TypeExpression::Var(i)).collect());
        // Annotate statements
        let new_statements_r: Result<Vec<_>, _> = self.statements.iter().map(|statement|
            statement.assign_type_vars(&mut local_context, solver, allocator)
        ).collect();
        let new_statements = new_statements_r?;
        // Annotate tail
        let new_tail = self.tail.assign_type_vars(&mut local_context, solver, allocator)?;
        // Add rule matching return type with tail type
        solver.add_rule(return_type_index, TypeExpression::Var(new_tail.t.0));
        Ok((Lambda::new(new_param_bindings, VariableType(return_type_index),
            new_statements, new_tail, Position::clone(&self.p)), overall_type))
    }
}

impl<> Statement<OptionalType> {
    fn assign_type_vars(&self, context: &mut TypeContext<TypeAssignment>, solver: &mut Solver, allocator: &mut TypeVarAllocator) 
            -> Result<Statement<VariableType>, Error> {
        use Statement::*;
        match self {
            Expr(e) => {
                Ok(Expr(Box::new(e.assign_type_vars(context, solver, allocator)?)))
            }
            Let(binding, e) => {
                let new_expr = e.assign_type_vars(context, solver, allocator)?;
                let new_var_index = allocator.allocate(&binding.p);
                solver.add_rule(new_var_index, TypeExpression::Var(new_expr.t.0));
                if let Some(t) = &binding.t.0 {
                    solver.add_rule(new_var_index, t.remap_vars(allocator));
                }
                context.set(&binding.name, &TypeAssignment::LocalName(new_var_index))
                    .map_err(|c| Error::new(c, Position::clone(&binding.p)))?;
                let new_binding = Binding::new(
                    binding.name.to_owned(),
                    VariableType(new_var_index),
                    Position::clone(&binding.p));
                Ok(Let(new_binding, Box::new(new_expr)))
            }
        }
    }
}

// end assign_type_vars

impl<> Lambda<FixedType> {
    fn get_overall_type(&self) -> TypeExpression {
        let mut param_types: Vec<TypeExpression> = self.params.iter().map(|t| TypeExpression::clone(&t.t.0)).collect();
        param_types.push(TypeExpression::clone(&self.return_type.0));
        TypeExpression::Function(param_types)
    }
}

// translate_types
impl<> Lambda<VariableType> {
    fn translate_types(self, solution: &Solution) -> Lambda<FixedType> {
        Lambda {
            params: self.params.into_iter().map(|b| b.translate_types(solution)).collect(),
            statements: self.statements.into_iter().map(|s| s.translate_types(solution)).collect(),
            tail: Box::new(self.tail.translate_types(solution)),
            return_type: FixedType(solution.translate_var_index(self.return_type.0)),
            p: self.p
        }
    }
}

impl<> Binding<VariableType> {
    fn translate_types(self, solution: &Solution) -> Binding<FixedType> {
        Binding {
            name: self.name,
            t: FixedType(solution.translate_var_index(self.t.0)),
            p: self.p
        }
    }
}

impl<> ExpressionVariant<VariableType> {
    fn translate_types(self, solution: &Solution) -> ExpressionVariant<FixedType> {
        use ExpressionVariant::*;
        match self {
            Application(v) => Application(v.into_iter().map(|e| e.translate_types(solution)).collect()),
            IntConstant(x) => IntConstant(x),
            Variable(name) => Variable(name),
            Abstraction(_) => todo!(),
        }
    }
}

impl<> Statement<VariableType> {
    fn translate_types(self, solution: &Solution) -> Statement<FixedType> {
        use Statement::*;
        match self {
            Expr(e) => Expr(Box::new(e.translate_types(solution))),
            Let(b, e) => Let(b.translate_types(solution), Box::new(e.translate_types(solution)))
        }
    }
}

impl<> Expression<VariableType> {
    fn translate_types(self, solution: &Solution) -> Expression<FixedType> {
        Expression {
            t: FixedType(solution.translate_var_index(self.t.0)),
            p: self.p,
            e: self.e.translate_types(solution),
        }
    }
}
// end translate_types

impl<> Expression<FixedType> {
    pub fn new(e: ExpressionVariant<FixedType>, p: Position, t: TypeExpression) -> Self {
        Self {
            e,
            p,
            t: FixedType(t),
        }
    }
}

impl<> Expression<OptionalType> {
    pub fn new(e: ExpressionVariant<OptionalType>, p: Position, t: Option<TypeExpression>) -> Self {
        Self {
            e,
            p,
            t: OptionalType(t),
        }
    }
}

impl<> Expression<VariableType> {
    pub fn new(e: ExpressionVariant<VariableType>, p: Position, index: usize) -> Self {
        Self {
            e,
            p,
            t: VariableType(index),
        }
    }
}

impl<Type> Function<Type> {
    pub fn new(name: String, body: Lambda<Type>, type_vars: TypeVars, p: Position) -> Self {
        Self {
            name,
            body,
            type_vars,
            p
        }
    }
}

impl<Type> Binding<Type> {
    pub fn new(name: String, t: Type, p: Position) -> Self {
        Self {
            name,
            t,
            p
        }
    }
}

impl<Type> Statement<Type> {
    pub fn new_expr(expr: Expression<Type>) -> Self {
        Statement::Expr(Box::new(expr))
    }

    pub fn new_let(binding: Binding<Type>, expr: Expression<Type>) -> Self {
        Statement::Let(binding, Box::new(expr))
    }
}

impl<Type> Lambda<Type> {
    pub fn new(params: Vec<Binding<Type>>, return_type: Type, statements: Vec<Statement<Type>>, tail: Expression<Type>, p: Position) -> Self {
        Self {
            params,
            return_type,
            statements,
            tail: Box::new(tail),
            p
        }
    }
}

pub trait PrefixFormatter {
    fn write_with_prefix(&self, f: &mut fmt::Formatter<'_>, prefix: &str) -> fmt::Result;
}

impl PrefixFormatter for OptionalType {
    fn write_with_prefix(&self, f: &mut fmt::Formatter<'_>, prefix: &str) -> fmt::Result {
        match &self.0 {
            Some(t) => write!(f, "{}{}", prefix, t),
            None => Ok(())
        }
    }
}

impl PrefixFormatter for VariableType {
    fn write_with_prefix(&self, f: &mut fmt::Formatter<'_>, prefix: &str) -> fmt::Result {
        write!(f, "{}{}", prefix, var_from_number(self.0))
    }
}

impl PrefixFormatter for FixedType {
    fn write_with_prefix(&self, f: &mut fmt::Formatter<'_>, prefix: &str) -> fmt::Result {
        write!(f, "{}{}", prefix, self.0)
    }
}

impl<Type: PrefixFormatter> fmt::Display for ExpressionVariant<Type>
where Expression<Type>: fmt::Display {
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

impl<Type: PrefixFormatter> fmt::Display for Expression<Type> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.e)?;
        self.t.write_with_prefix(f, ": ")
    }
}

impl<Type: PrefixFormatter> fmt::Display for Lambda<Type>
where Expression<Type>: fmt::Display {
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
        self.return_type.write_with_prefix(f, " -> ")
    }
}

impl<Type: PrefixFormatter> fmt::Display for Binding<Type> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", &self.name)?;
        self.t.write_with_prefix(f, ": ")
    }
}

impl<Type: PrefixFormatter> fmt::Display for Statement<Type> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Expr(e) => write!(f, "{}", e),
            Self::Let(b, e) => {
                write!(f, "let {} = {}", b, e)
            }
        }
    }
}

impl<Type: PrefixFormatter> fmt::Display for Function<Type> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.type_vars)?;
        write!(f, "def {} = {}", self.name, self.body)
    }
}

impl<Type: PrefixFormatter> fmt::Display for Module<Type> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for fun in self.functions.iter() {
            write!(f, "{}\n\n", fun)?;
        }
        Ok(())
    }
}

