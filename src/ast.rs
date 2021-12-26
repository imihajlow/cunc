
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
    pub t: Type,
    pub e: ExpressionVariant<Type>,
    pub p: Position,
}

#[derive(Debug, Clone)]
pub enum ExpressionVariant<Type> {
    Application(Box<Expression<Type>>, Box<Expression<Type>>),
    IntConstant(u64),
    Variable(String),
    Abstraction(Lambda<Type>),
    Let(Binding<Type>, Box<Expression<Type>>, Box<Expression<Type>>)
}

#[derive(Debug, Clone)]
pub struct Lambda<Type> {
    param: Binding<Type>,
    return_type: Type,
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
pub struct Function<Type> {
    name: String,
    body: Expression<Type>,
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
            function.body.e.collect_refs(&mut context, &mut refs);
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
pub enum TypeAssignment {
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
    pub fn deduce_types(&self, parent_context: &TypeContext<TypeAssignment>) -> Result<Module<FixedType>, Error> {
        let function_by_name: HashMap<String, &Function<_>> =
            HashMap::from_iter(self.functions.iter().map(|f| (f.name.to_string(), f)));
        let dep_graph = self.build_dependency_graph();
        let toporder = dep_graph.find_strongly_connected().inverse_topsort().unwrap();
        let mut result: Module<FixedType> = Module::new();
        let mut context: TypeContext<TypeAssignment> = parent_context.push();
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
            let mut var_annotated_bodies: Vec<(String, Expression<VariableType>)> = Vec::new();
            for fname in group.iter() {
                let function = function_by_name[fname];
                let index = local_context.get(fname).unwrap().unwrap_local_name();
                let function_context = local_context.push();
                allocator.enter_function(function.type_vars.get_vars_count(), &function.p);
                let body =
                    function.body.assign_type_vars(&function_context, &mut solver, &mut allocator)?;
                solver.add_rule(index, TypeExpression::Var(body.t.0));
                for c in function.type_vars.constraints_iter() {
                    solver.add_constraint(c.remap_vars(&allocator));
                }
                var_annotated_bodies.push((fname.to_owned(), body));
                allocator.leave_function();
            }
            // println!("{}", &solver);
            let solution = solver.solve().map_err(|e| e.as_error(&allocator))?;
            // println!("\nSolution:\n{}", &solution);
            // Store functions in module and update context with their types
            for (name, body) in var_annotated_bodies.into_iter() {
                let deduced_body = body.translate_types(&solution);
                let new_type_vars = TypeVars::new(solution.get_free_vars_count(),
                    solution.clone_type_constraints());
                // println!("\n{} {}", &name, &deduced_body);
                let old_function = function_by_name[&name];
                context.set(&name,
                    &TypeAssignment::ToplevelFunction(
                        TypeVars::clone(&new_type_vars),
                        TypeExpression::clone(&deduced_body.t.0)))
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
            Application(a, b) => {
                a.e.collect_refs(context, result);
                b.e.collect_refs(context, result);
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
            Let(b, val, body) => {
                val.e.collect_refs(context, result);
                context.push();
                context.add_name(&b.name);
                body.e.collect_refs(context, result);
                context.pop();
            }
        }
    }
}

impl<Type> Lambda<Type> {
    fn collect_refs(&self, context: &mut NameContext, result: &mut HashSet<String>) {
        context.push();
        context.add_name(&self.param.name);
        self.tail.e.collect_refs(context, result);
        context.pop();
    }
}
// end collect_refs


// assign_type_vars
impl<> Expression<OptionalType> {
    /// Assign a new type variable to every part of the expression and to the expression itself,
    /// simultaniously adding rules to type solver.
    fn assign_type_vars(&self, context: &TypeContext<TypeAssignment>, solver: &mut Solver, allocator: &mut TypeVarAllocator) 
            -> Result<Expression<VariableType>, Error> {
        use ExpressionVariant::*;
        let my_var_index = allocator.allocate(&self.p);
        let my_position = Position::clone(&self.p);
        if let Some(t) = &self.t.0 {
            solver.add_rule(my_var_index, t.remap_vars(allocator));
        }
        match &self.e {
            Application(a, b) => {
                let annotated_a = Box::new(a.assign_type_vars(context, solver, allocator)?);
                let annotated_b = Box::new(b.assign_type_vars(context, solver, allocator)?);
                let head_index = annotated_a.t.0;
                let tail_index = annotated_b.t.0;
                let fn_type = TypeExpression::new_function(
                    TypeExpression::Var(tail_index),
                    TypeExpression::Var(my_var_index));
                solver.add_rule(head_index, fn_type);
                Ok(Expression::<VariableType>::new(
                    Application(annotated_a, annotated_b),
                    my_position,
                    my_var_index))
            }
            IntConstant(x) => {
                solver.add_constraint(TypeConstraint::new_num(&TypeExpression::Var(my_var_index), &my_position));
                Ok(Expression::<VariableType>::new(
                    IntConstant(*x),
                    my_position,
                    my_var_index))
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
                                for c in tv.constraints_iter() {
                                    solver.add_constraint(c.remap_vars(allocator));
                                }
                                allocator.leave_function();
                            }
                        }
                        Ok(Expression::<VariableType>::new(
                            Variable(name.to_string()),
                            my_position,
                            my_var_index))
                    }
                }
            }
            Abstraction(l) => {
                let annotated_lambda = l.assign_type_vars(context, solver, allocator)?;
                solver.add_rule(my_var_index, annotated_lambda.get_overall_type());
                Ok(Expression::<VariableType>::new(
                    Abstraction(annotated_lambda),
                    my_position,
                    my_var_index))
            }
            Let(binding, val, body) => {
                let var_index = allocator.allocate(&binding.p);
                let annotated_binding: Binding<VariableType> =
                    Binding::new(binding.name.to_owned(), VariableType(var_index), Position::clone(&binding.p));
                let annotated_val = val.assign_type_vars(context, solver, allocator)?;
                let mut body_context = context.push();
                body_context.set(&binding.name, &TypeAssignment::LocalName(var_index))
                    .map_err(|c| Error::new(c, Position::clone(&binding.p)))?;
                let annotated_body = body.assign_type_vars(&body_context, solver, allocator)?;
                if let Some(t) = &binding.t.0 {
                    solver.add_rule(var_index, t.remap_vars(allocator));
                }
                solver.add_rule(my_var_index, TypeExpression::Var(annotated_body.t.0));
                solver.add_rule(var_index, TypeExpression::Var(annotated_val.t.0));
                
                Ok(Expression::<VariableType>::new(
                    Let(annotated_binding, Box::new(annotated_val), Box::new(annotated_body)),
                    my_position,
                    my_var_index))
            }
        }
    }
}


impl<> Lambda<OptionalType> {
    /// Assign type variables, simultaniously adding rules to type solver.
    /// Returns annotated Lambda and its type.
    fn assign_type_vars(&self, context: &TypeContext<TypeAssignment>, solver: &mut Solver, allocator: &mut TypeVarAllocator) 
            -> Result<Lambda<VariableType>, Error> {
        let mut local_context = context.push();
        // Annotate parameter
        let param_index = allocator.allocate(&self.param.p);
        let new_param_binding: Binding<VariableType> =
            Binding::new(self.param.name.to_owned(), VariableType(param_index), Position::clone(&self.param.p));
        local_context.set(&self.param.name, &TypeAssignment::LocalName(param_index))
            .map_err(|c| Error::new(c, Position::clone(&self.param.p)))?;
        if let Some(t) = &self.param.t.0 {
            solver.add_rule(param_index, t.remap_vars(allocator));
        }
        let return_type_index = allocator.allocate(&self.p);
        if let Some(t) = &self.return_type.0 {
            solver.add_rule(return_type_index, t.remap_vars(allocator));
        }
        // Annotate tail
        let new_tail = self.tail.assign_type_vars(&mut local_context, solver, allocator)?;
        // Add rule matching return type with tail type
        solver.add_rule(return_type_index, TypeExpression::Var(new_tail.t.0));

        Ok(Lambda::new(new_param_binding, VariableType(return_type_index),
            new_tail, Position::clone(&self.p)))
    }
}

// end assign_type_vars

impl<> Lambda<FixedType> {
    fn get_overall_type(&self) -> TypeExpression {
        TypeExpression::new_function(
            TypeExpression::clone(&self.param.t.0),
            TypeExpression::clone(&self.return_type.0)
        )
    }
}

impl<> Lambda<VariableType> {
    fn get_overall_type(&self) -> TypeExpression {
        TypeExpression::new_function(
            TypeExpression::Var(self.param.t.0),
            TypeExpression::Var(self.return_type.0)
        )
    }
}

// translate_types
impl<> Lambda<VariableType> {
    fn translate_types(self, solution: &Solution) -> Lambda<FixedType> {
        Lambda {
            param: self.param.translate_types(solution),
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
            Application(a, b) => Application(
                Box::new(a.translate_types(solution)),
                Box::new(b.translate_types(solution))),
            IntConstant(x) => IntConstant(x),
            Variable(name) => Variable(name),
            Abstraction(lambda) => Abstraction(lambda.translate_types(solution)),
            Let(binding, val, body) => Let(
                binding.translate_types(solution),
                Box::new(val.translate_types(solution)),
                Box::new(body.translate_types(solution)))
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

    pub fn new_application(left: Self, right: Self) -> Self {
        let common_p = left.p.merge(&right.p);
        Self {
            e: ExpressionVariant::Application(Box::new(left), Box::new(right)),
            p: common_p,
            t: OptionalType(None)
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
    pub fn new(name: String, body: Expression<Type>, type_vars: TypeVars, p: Position) -> Self {
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

impl<Type> Lambda<Type> {
    pub fn new(param: Binding<Type>, return_type: Type, tail: Expression<Type>, p: Position) -> Self {
        Self {
            param,
            return_type,
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
            Some(t) => write!(f, "{}[{}]", prefix, t),
            None => Ok(())
        }
    }
}

impl PrefixFormatter for VariableType {
    fn write_with_prefix(&self, f: &mut fmt::Formatter<'_>, prefix: &str) -> fmt::Result {
        write!(f, "{}[{}]", prefix, var_from_number(self.0))
    }
}

impl PrefixFormatter for FixedType {
    fn write_with_prefix(&self, f: &mut fmt::Formatter<'_>, prefix: &str) -> fmt::Result {
        write!(f, "{}[{}]", prefix, self.0)
    }
}

impl<Type: PrefixFormatter> fmt::Display for ExpressionVariant<Type>
where Expression<Type>: fmt::Display {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Application(a, b) => {
                match b.e {
                    Self::Application(_, _) => write!(f, "{} ({})", a, b),
                    _ => write!(f, "{} {}", a, b)
                }
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
            Self::Let(binding, val, body) => {
                write!(f, "let {} = {};\n{}", binding, val, body)
            }
        }
    }
}

impl<Type: PrefixFormatter> fmt::Display for Expression<Type> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.e)?;
        self.t.write_with_prefix(f, " :: ")
    }
}

impl<Type: PrefixFormatter> fmt::Display for Lambda<Type>
where Expression<Type>: fmt::Display {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let simply_nested = match self.tail.e {
            ExpressionVariant::Abstraction(_) => true,
            _ => false
        };
        if simply_nested {
            write!(f, "\\ {}, {}", &self.param.name, &self.tail.e)
        } else {
            write!(f, "\\ {} -> {{\n", &self.param.name)?;
            write!(f, "{}\n}}", self.tail)?;
            self.return_type.write_with_prefix(f, " :: ")
        }
        // write!(f, "\\{} -> {{\n{}\n}}", self.param, self.tail)?;
        // self.return_type.write_with_prefix(f, " -> ")
    }
}

impl<Type: PrefixFormatter> fmt::Display for Binding<Type> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", &self.name)?;
        self.t.write_with_prefix(f, " :: ")
    }
}

impl<Type: PrefixFormatter> fmt::Display for Function<Type> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[")?;
        write!(f, "{}", self.type_vars)?;
        self.body.t.write_with_prefix(f, "")?;
        write!(f, "]\n{} = {}.", self.name, self.body)
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

