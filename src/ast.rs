use crate::error::Error;
use crate::error::ErrorCause;
use crate::graph::ObjectGraph;
use crate::name_context::NameContext;
use crate::name_context::TypeContext;
use crate::position::Position;
use crate::type_info::AtomicKind;
use crate::type_info::AtomicType;
use crate::type_info::KindExpression;
use crate::type_info::TypeExpression;
use crate::type_info::TypeVars;
use crate::type_solver::Solution;
use crate::type_solver::Solver;
use crate::type_var_allocator::TypeVarAllocator;
use crate::util::var_from_number;
use itertools::Itertools;
use std::collections::HashMap;
use std::collections::HashSet;
use std::fmt;
use std::iter;

/*
   Type inference system takes Module<OptionalType>,
   assigns type variables to every part of every expression producing VariableType-based objects,
   and after deducing variable values with type_solver::Solver substitutes variables with fixed types,
   producing Module<FixedType>.
*/

/// Type which can be specified or not.
#[derive(Debug, Clone, PartialEq)]
pub struct OptionalType(pub Option<TypeExpression>);

/// Type specified by a type variable.
#[derive(Debug, Clone, PartialEq)]
pub struct VariableType(pub usize);

/// Known (maybe generic) type.
#[derive(Debug, Clone, PartialEq)]
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
    Let(Binding<Type>, Box<Expression<Type>>, Box<Expression<Type>>),
    Pmatch(Box<Expression<Type>>, Vec<Case<Type>>),
}

#[derive(Debug, Clone)]
pub struct Case<Type> {
    tc: TypeConstructor,
    params: Vec<Binding<Type>>,
    body: Expression<Type>,
    p: Position,
}

#[derive(Debug, Clone)]
pub struct Lambda<Type> {
    param: Binding<Type>,
    return_type: Type,
    tail: Box<Expression<Type>>,
    p: Position,
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
    context: ConstraintContext<Type>,
    body: Expression<Type>,
    type_vars: TypeVars,
    p: Position,
}

#[derive(Debug, Clone)]
pub struct Module<Type> {
    functions: Vec<Function<Type>>,
    types: Vec<SumType>,
}

#[derive(Debug, Clone)]
pub struct ConstraintContext<Type> {
    c: Vec<(Type, Position)>,
}

#[derive(Debug, Clone)]
pub struct TypeConstructor {
    pub name: String,
    pub enum_index: usize,
    pub params: Vec<TypeExpression>,
    pub parent_type: TypeExpression,
    pub type_vars: TypeVars,
    p: Position,
}

#[derive(Debug, Clone)]
pub struct SumType {
    pub name: String,
    pub arity: usize,
    pub constructors: Vec<TypeConstructor>,
    p: Position,
}

impl<Type> Case<Type> {
    pub fn new(
        tc: TypeConstructor,
        params: Vec<Binding<Type>>,
        body: Expression<Type>,
        p: Position,
    ) -> Self {
        Self {
            tc,
            params,
            body,
            p,
        }
    }
}

impl<Type> Module<Type> {
    pub fn new() -> Self {
        Self {
            functions: Vec::new(),
            types: Vec::new(),
        }
    }

    pub fn push_function(&mut self, f: Function<Type>) {
        self.functions.push(f);
    }

    pub fn push_type(&mut self, t: SumType) {
        self.types.push(t);
    }
}

impl TypeConstructor {
    pub fn new(
        name: String,
        enum_index: usize,
        params: Vec<TypeExpression>,
        parent_type: TypeExpression,
        type_vars: TypeVars,
        p: Position,
    ) -> Self {
        Self {
            name,
            enum_index,
            params,
            parent_type,
            type_vars,
            p,
        }
    }

    pub fn get_function_type(&self) -> (TypeVars, TypeExpression) {
        let mut parts = Vec::clone(&self.params);
        parts.push(TypeExpression::clone(&self.parent_type));
        (
            TypeVars::clone(&self.type_vars),
            TypeExpression::new_function_from_vec(parts),
        )
    }
}

impl SumType {
    pub fn new(
        name: String,
        arity: usize,
        constructors: Vec<TypeConstructor>,
        p: Position,
    ) -> Self {
        Self {
            name,
            arity,
            constructors,
            p,
        }
    }
}

impl<Type> Module<Type> {
    /// Build a graph of dependencies between functions.
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

    /// Build a graph of dependencies between custom types
    pub fn build_types_top_order(&self) -> Result<Vec<SumType>, Error> {
        let mut context = NameContext::new();
        let mut type_by_name: HashMap<String, &SumType> = HashMap::new();
        for t in self.types.iter() {
            context.add_name(&t.name);
            type_by_name.insert(t.name.to_owned(), t);
        }
        let mut dep_graph: ObjectGraph<String> = ObjectGraph::new();
        for t in self.types.iter() {
            let from = &t.name;
            for c in t.constructors.iter() {
                let mut refs: HashSet<String> = HashSet::new();
                for param in c.params.iter() {
                    param.collect_refs(&mut refs);
                }
                dep_graph.add_node_unique(from);
                for to in refs.into_iter() {
                    dep_graph.add_edge_unique(from, &to);
                }
            }
        }
        let toporder = dep_graph.inverse_topsort().map_err(|s| {
            let t = type_by_name[&s];
            Error::new(ErrorCause::RecursiveType(s), Position::clone(&t.p))
        })?;
        Ok(toporder
            .into_iter()
            .map(|s| SumType::clone(type_by_name[&s]))
            .collect())
    }
}

/// Enum used in type context.
#[derive(Debug, Clone)]
pub enum TypeAssignment {
    ToplevelFunction(TypeVars, TypeExpression, ConstraintContext<FixedType>),
    LocalName(usize),
}

impl TypeAssignment {
    fn unwrap_local_name(&self) -> usize {
        match self {
            TypeAssignment::LocalName(x) => *x,
            _ => panic!("Not a local name: {:?}", self),
        }
    }
}

impl Module<OptionalType> {
    pub fn deduce_types(
        &self,
        parent_context: &TypeContext<TypeAssignment>,
    ) -> Result<Module<FixedType>, Error> {
        let function_by_name: HashMap<String, &Function<_>> =
            HashMap::from_iter(self.functions.iter().map(|f| (f.name.to_string(), f)));
        let dep_graph = self.build_dependency_graph();
        let toporder = dep_graph
            .find_strongly_connected()
            .inverse_topsort()
            .unwrap();
        let mut result: Module<FixedType> = Module::new();
        let mut context: TypeContext<TypeAssignment> = parent_context.push();
        // Add type constructors into context
        for t in self.types.iter() {
            for c in t.constructors.iter() {
                let (tv, t) = c.get_function_type();
                context
                    .set(
                        &c.name,
                        &TypeAssignment::ToplevelFunction(tv, t, ConstraintContext::new()),
                    )
                    .map_err(|cause| Error::new(cause, Position::clone(&c.p)))?;
            }
        }
        for group in toporder.into_iter() {
            let mut group_context = context.push();
            let mut allocator = TypeVarAllocator::new();
            let mut solver = Solver::new();
            // First just assign indices to functions
            for fname in group.iter() {
                let pos = &function_by_name[fname].p;
                let index = allocator.allocate(pos);
                group_context
                    .set(fname, &TypeAssignment::LocalName(index))
                    .map_err(|c| Error::new(c, Position::clone(pos)))?;
            }
            // Actually process functions
            let mut var_annotated_fns: Vec<Function<VariableType>> = Vec::new();
            for fname in group.iter() {
                let function = function_by_name[fname];
                let annotated_function =
                    function.assign_type_vars(&group_context, &mut solver, &mut allocator)?;
                var_annotated_fns.push(annotated_function);
            }
            // println!("{}", &solver);
            let solution = solver.solve().map_err(|e| e.as_error(&allocator))?;
            // println!("\nSolution:\n{}", &solution);
            // Store functions in module and update context with their types
            for function in var_annotated_fns.into_iter() {
                let deduced_fn = function.apply_solution(&solution)?;
                // println!("\n{} {}", &name, &deduced_body);
                context
                    .set(
                        &deduced_fn.name,
                        &TypeAssignment::ToplevelFunction(
                            TypeVars::clone(&deduced_fn.type_vars),
                            TypeExpression::clone(&deduced_fn.body.t.0),
                            ConstraintContext::clone(&deduced_fn.context),
                        ),
                    )
                    .map_err(|c| Error::new(c, Position::clone(&deduced_fn.p)))?;
                result.push_function(deduced_fn);
            }
        }
        // copy custom types
        for t in self.types.iter() {
            result.push_type(SumType::clone(t));
        }
        Ok(result)
    }
}

impl Module<FixedType> {
    pub fn deduce_kinds(&self) -> Result<TypeContext<KindExpression>, Error> {
        let toporder = self.build_types_top_order()?;
        let mut context: TypeContext<KindExpression> = TypeContext::new();
        for t in toporder.into_iter() {
            let mut solver: Solver<AtomicKind> = Solver::new();
            let mut tva = TypeVarAllocator::new();
            tva.enter_function(t.arity, &t.p);
            for c in t.constructors.iter() {
                for param in c.params.iter() {
                    let index = param
                        .create_kind_rules(&mut tva, &context, &mut solver)
                        .map_err(|cause| Error::new(cause, Position::clone(&c.p)))?;
                    solver.add_rule(index, KindExpression::Atomic(AtomicKind::Type));
                }
            }
            let solution = solver
                .solve()
                .map_err(|e| e.as_error(&tva).with_position(Position::clone(&t.p)))?;
            let mut kind = (0..t.arity)
                .map(|i| solution.translate_var_index(i))
                .chain(iter::once(KindExpression::Atomic(AtomicKind::Type)))
                .rev()
                .reduce(|acc, b| KindExpression::Composite(Box::new(b), Box::new(acc)))
                .unwrap();
            // Assuming any remaining free var correspond to types.
            kind.substitute_free_vars(&KindExpression::Atomic(AtomicKind::Type));
            println!("{} :: {}", &t.name, &kind);
            context
                .set(&t.name, &kind)
                .map_err(|c| Error::new(c, t.p))?;
        }
        Ok(context)
    }

    pub fn check_kinds(&self) -> Result<(), Error> {
        let context = self.deduce_kinds()?;
        for f in self.functions.iter() {
            f.check_kinds(&context)?;
        }
        Ok(())
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
            Pmatch(e, v) => {
                e.e.collect_refs(context, result);
                for c in v.iter() {
                    c.collect_refs(context, result);
                }
            }
        }
    }
}

impl<Type> Case<Type> {
    fn collect_refs(&self, context: &mut NameContext, result: &mut HashSet<String>) {
        context.push();
        for b in self.params.iter() {
            context.add_name(&b.name);
        }
        self.body.e.collect_refs(context, result);
        context.pop();
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
impl Expression<OptionalType> {
    /// Assign a new type variable to every part of the expression and to the expression itself,
    /// simultaniously adding rules to type solver.
    fn assign_type_vars(
        &self,
        context: &TypeContext<TypeAssignment>,
        solver: &mut Solver<AtomicType>,
        allocator: &mut TypeVarAllocator,
        constraint_context: &mut ConstraintContext<VariableType>,
    ) -> Result<Expression<VariableType>, Error> {
        use ExpressionVariant::*;
        let my_var_index = allocator.allocate(&self.p);
        let my_position = Position::clone(&self.p);
        if let Some(t) = &self.t.0 {
            solver.add_rule(my_var_index, t.remap_vars(allocator));
        }
        match &self.e {
            Application(a, b) => {
                let annotated_a =
                    Box::new(a.assign_type_vars(context, solver, allocator, constraint_context)?);
                let annotated_b =
                    Box::new(b.assign_type_vars(context, solver, allocator, constraint_context)?);
                let head_index = annotated_a.t.0;
                let tail_index = annotated_b.t.0;
                let fn_type = TypeExpression::new_function(
                    TypeExpression::Var(tail_index),
                    TypeExpression::Var(my_var_index),
                );
                solver.add_rule(head_index, fn_type);
                Ok(Expression::<VariableType>::new(
                    Application(annotated_a, annotated_b),
                    my_position,
                    my_var_index,
                ))
            }
            IntConstant(x) => {
                let num_constraint = TypeExpression::Composite(
                    Box::new(TypeExpression::Atomic(AtomicType::Num)),
                    Box::new(TypeExpression::Var(my_var_index)),
                );
                let constraint_index = allocator.allocate(&my_position);
                solver.add_rule(constraint_index, num_constraint);
                constraint_context.add(VariableType(constraint_index), &my_position);
                Ok(Expression::<VariableType>::new(
                    IntConstant(*x),
                    my_position,
                    my_var_index,
                ))
            }
            Variable(name) => {
                match context.get(name) {
                    None => Err(Error::new(
                        ErrorCause::UnknownIdentifier(name.to_string()),
                        my_position,
                    )),
                    Some(a) => {
                        match a {
                            TypeAssignment::LocalName(var_index) => {
                                solver.add_rule(my_var_index, TypeExpression::Var(*var_index))
                            }
                            TypeAssignment::ToplevelFunction(tv, te, cc) => {
                                // Generic function. Remap generic variables.
                                allocator.enter_function(tv.get_vars_count(), &self.p);
                                solver.add_rule(my_var_index, te.remap_vars(allocator));
                                for (t, p) in cc.c.iter() {
                                    let index = allocator.allocate(p);
                                    let remapped_type = t.0.remap_vars(allocator);
                                    solver.add_rule(index, remapped_type);
                                    constraint_context.add(VariableType(index), p);
                                }
                                allocator.leave_function();
                            }
                        }
                        Ok(Expression::<VariableType>::new(
                            Variable(name.to_string()),
                            my_position,
                            my_var_index,
                        ))
                    }
                }
            }
            Abstraction(l) => {
                let annotated_lambda =
                    l.assign_type_vars(context, solver, allocator, constraint_context)?;
                solver.add_rule(my_var_index, annotated_lambda.get_overall_type());
                Ok(Expression::<VariableType>::new(
                    Abstraction(annotated_lambda),
                    my_position,
                    my_var_index,
                ))
            }
            Let(binding, val, body) => {
                let var_index = allocator.allocate(&binding.p);
                let annotated_binding: Binding<VariableType> = Binding::new(
                    binding.name.to_owned(),
                    VariableType(var_index),
                    Position::clone(&binding.p),
                );
                let annotated_val =
                    val.assign_type_vars(context, solver, allocator, constraint_context)?;
                let mut body_context = context.push();
                body_context
                    .set(&binding.name, &TypeAssignment::LocalName(var_index))
                    .map_err(|c| Error::new(c, Position::clone(&binding.p)))?;
                let annotated_body =
                    body.assign_type_vars(&body_context, solver, allocator, constraint_context)?;
                if let Some(t) = &binding.t.0 {
                    solver.add_rule(var_index, t.remap_vars(allocator));
                }
                solver.add_rule(my_var_index, TypeExpression::Var(annotated_body.t.0));
                solver.add_rule(var_index, TypeExpression::Var(annotated_val.t.0));

                Ok(Expression::<VariableType>::new(
                    Let(
                        annotated_binding,
                        Box::new(annotated_val),
                        Box::new(annotated_body),
                    ),
                    my_position,
                    my_var_index,
                ))
            }
            Pmatch(e, v) => {
                let annotated_e =
                    e.assign_type_vars(context, solver, allocator, constraint_context)?;
                let mut annotated_cases: Vec<Case<VariableType>> = Vec::new();
                for case in v.iter() {
                    let new_case = case.assign_type_vars(
                        context,
                        solver,
                        allocator,
                        constraint_context,
                        annotated_e.t.0,
                    )?;
                    solver.add_rule(my_var_index, TypeExpression::Var(new_case.body.t.0));
                    annotated_cases.push(new_case);
                }
                Ok(Expression::<VariableType>::new(
                    Pmatch(Box::new(annotated_e), annotated_cases),
                    my_position,
                    my_var_index,
                ))
            }
        }
    }
}

impl Case<OptionalType> {
    fn assign_type_vars(
        &self,
        context: &TypeContext<TypeAssignment>,
        solver: &mut Solver<AtomicType>,
        allocator: &mut TypeVarAllocator,
        constraint_context: &mut ConstraintContext<VariableType>,
        parent_var_index: usize,
    ) -> Result<Case<VariableType>, Error> {
        let type_arity = self
            .tc
            .parent_type
            .get_max_var_index()
            .map(|x| x + 1)
            .unwrap_or(0);
        allocator.enter_function(type_arity, &self.p);
        let mut local_context = context.push();
        assert_eq!(self.tc.params.len(), self.params.len());
        // The expression being matched should be of the type constructor's parent type:
        solver.add_rule(parent_var_index, self.tc.parent_type.remap_vars(&allocator));
        let mut annotated_params: Vec<Binding<VariableType>> = Vec::new();
        for (i, param) in self.params.iter().enumerate() {
            let tc_param = &self.tc.params[i];
            let param_var_index = allocator.allocate(&param.p);
            let param_type_from_tc = tc_param.remap_vars(&allocator);
            // First rule: a parameter must have type of type constructor's parameter
            solver.add_rule(param_var_index, param_type_from_tc);
            // Second rule: if there's a type hint, apply it
            if let Some(t) = &param.t.0 {
                solver.add_rule(param_var_index, TypeExpression::clone(t));
            }
            local_context
                .set(&param.name, &TypeAssignment::LocalName(param_var_index))
                .map_err(|c| Error::new(c, Position::clone(&param.p)))?;
            annotated_params.push(Binding::new(
                param.name.to_owned(),
                VariableType(param_var_index),
                Position::clone(&param.p),
            ))
        }
        let annotated_body =
            self.body
                .assign_type_vars(&local_context, solver, allocator, constraint_context)?;
        allocator.leave_function();
        Ok(Case::new(
            TypeConstructor::clone(&self.tc),
            annotated_params,
            annotated_body,
            Position::clone(&self.p),
        ))
    }
}

impl Lambda<OptionalType> {
    /// Assign type variables, simultaniously adding rules to type solver.
    /// Returns annotated Lambda and its type.
    fn assign_type_vars(
        &self,
        context: &TypeContext<TypeAssignment>,
        solver: &mut Solver<AtomicType>,
        allocator: &mut TypeVarAllocator,
        constraint_context: &mut ConstraintContext<VariableType>,
    ) -> Result<Lambda<VariableType>, Error> {
        let mut local_context = context.push();
        // Annotate parameter
        let param_index = allocator.allocate(&self.param.p);
        let new_param_binding: Binding<VariableType> = Binding::new(
            self.param.name.to_owned(),
            VariableType(param_index),
            Position::clone(&self.param.p),
        );
        local_context
            .set(&self.param.name, &TypeAssignment::LocalName(param_index))
            .map_err(|c| Error::new(c, Position::clone(&self.param.p)))?;
        if let Some(t) = &self.param.t.0 {
            solver.add_rule(param_index, t.remap_vars(allocator));
        }
        let return_type_index = allocator.allocate(&self.p);
        if let Some(t) = &self.return_type.0 {
            solver.add_rule(return_type_index, t.remap_vars(allocator));
        }
        // Annotate tail
        let new_tail = self.tail.assign_type_vars(
            &mut local_context,
            solver,
            allocator,
            constraint_context,
        )?;
        // Add rule matching return type with tail type
        solver.add_rule(return_type_index, TypeExpression::Var(new_tail.t.0));

        Ok(Lambda::new(
            new_param_binding,
            VariableType(return_type_index),
            new_tail,
            Position::clone(&self.p),
        ))
    }
}

impl Function<OptionalType> {
    fn assign_type_vars(
        &self,
        context: &TypeContext<TypeAssignment>,
        solver: &mut Solver<AtomicType>,
        allocator: &mut TypeVarAllocator,
    ) -> Result<Function<VariableType>, Error> {
        let my_index = context.get(&self.name).unwrap().unwrap_local_name();
        let function_context = context.push();
        // TODO type_vars.get_vars_count must take context into account
        allocator.enter_function(self.type_vars.get_vars_count(), &self.p);
        let mut constraint_context = self.context.assign_type_vars(solver, allocator)?;
        let body = self.body.assign_type_vars(
            &function_context,
            solver,
            allocator,
            &mut constraint_context,
        )?;
        solver.add_rule(my_index, TypeExpression::Var(body.t.0));
        allocator.leave_function();
        Ok(Function::new(
            self.name.to_owned(),
            constraint_context,
            body,
            TypeVars::new(0),
            Position::clone(&self.p),
        ))
    }
}

impl ConstraintContext<OptionalType> {
    fn assign_type_vars(
        &self,
        solver: &mut Solver<AtomicType>,
        allocator: &mut TypeVarAllocator,
    ) -> Result<ConstraintContext<VariableType>, Error> {
        let mut result: Vec<(VariableType, Position)> = Vec::new();
        for (ot, p) in self.c.iter() {
            if let Some(t) = &ot.0 {
                let idx = allocator.allocate(p);
                solver.add_rule(idx, t.remap_vars(allocator));
                result.push((VariableType(idx), Position::clone(p)));
            }
        }
        Ok(ConstraintContext::new_from_vec(result))
    }
}

impl Function<VariableType> {
    fn apply_solution(self, solution: &Solution<AtomicType>) -> Result<Function<FixedType>, Error> {
        let new_constraint_context = self.context.translate_types(solution).check_and_reduce()?;
        Ok(Function {
            name: self.name,
            body: self.body.translate_types(solution),
            context: new_constraint_context,
            type_vars: TypeVars::new(solution.get_free_vars_count()),
            p: self.p,
        })
    }
}
// end assign_type_vars

impl Lambda<FixedType> {
    fn get_overall_type(&self) -> TypeExpression {
        TypeExpression::new_function(
            TypeExpression::clone(&self.param.t.0),
            TypeExpression::clone(&self.return_type.0),
        )
    }
}

impl Lambda<VariableType> {
    fn get_overall_type(&self) -> TypeExpression {
        TypeExpression::new_function(
            TypeExpression::Var(self.param.t.0),
            TypeExpression::Var(self.return_type.0),
        )
    }
}

// translate_types
impl Lambda<VariableType> {
    fn translate_types(self, solution: &Solution<AtomicType>) -> Lambda<FixedType> {
        Lambda {
            param: self.param.translate_types(solution),
            tail: Box::new(self.tail.translate_types(solution)),
            return_type: FixedType(solution.translate_var_index(self.return_type.0)),
            p: self.p,
        }
    }
}

impl Binding<VariableType> {
    fn translate_types(self, solution: &Solution<AtomicType>) -> Binding<FixedType> {
        Binding {
            name: self.name,
            t: FixedType(solution.translate_var_index(self.t.0)),
            p: self.p,
        }
    }
}

impl ExpressionVariant<VariableType> {
    fn translate_types(self, solution: &Solution<AtomicType>) -> ExpressionVariant<FixedType> {
        use ExpressionVariant::*;
        match self {
            Application(a, b) => Application(
                Box::new(a.translate_types(solution)),
                Box::new(b.translate_types(solution)),
            ),
            IntConstant(x) => IntConstant(x),
            Variable(name) => Variable(name),
            Abstraction(lambda) => Abstraction(lambda.translate_types(solution)),
            Let(binding, val, body) => Let(
                binding.translate_types(solution),
                Box::new(val.translate_types(solution)),
                Box::new(body.translate_types(solution)),
            ),
            Pmatch(e, v) => Pmatch(
                Box::new(e.translate_types(solution)),
                v.into_iter().map(|c| c.translate_types(solution)).collect(),
            ),
        }
    }
}

impl Expression<VariableType> {
    fn translate_types(self, solution: &Solution<AtomicType>) -> Expression<FixedType> {
        Expression {
            t: FixedType(solution.translate_var_index(self.t.0)),
            p: self.p,
            e: self.e.translate_types(solution),
        }
    }
}

impl Case<VariableType> {
    fn translate_types(self, solution: &Solution<AtomicType>) -> Case<FixedType> {
        Case {
            tc: self.tc,
            params: self
                .params
                .into_iter()
                .map(|b| b.translate_types(solution))
                .collect(),
            body: self.body.translate_types(solution),
            p: self.p,
        }
    }
}
impl ConstraintContext<VariableType> {
    fn translate_types(self, solution: &Solution<AtomicType>) -> ConstraintContext<FixedType> {
        ConstraintContext {
            c: self
                .c
                .into_iter()
                .map(|(t, p)| (FixedType(solution.translate_var_index(t.0)), p))
                .collect(),
        }
    }
}
// end translate_types

// check_kinds
fn check_kinds_eq(a: KindExpression, b: KindExpression, p: &Position) -> Result<(), Error> {
    if a != b {
        Err(Error::new(
            ErrorCause::KindsMismatch(a, b),
            Position::clone(&p),
        ))
    } else {
        Ok(())
    }
}

fn check_kind_of_type(
    t: &TypeExpression,
    context: &TypeContext<KindExpression>,
    p: &Position,
) -> Result<(), Error> {
    let my_kind = t
        .get_kind(context)
        .map_err(|c| Error::new(c, Position::clone(p)))?;
    check_kinds_eq(my_kind, KindExpression::TYPE, p)
}

impl Function<FixedType> {
    fn check_kinds(&self, context: &TypeContext<KindExpression>) -> Result<(), Error> {
        self.body.check_kinds(context)?;
        self.context.check_kinds(context)
    }
}

impl Expression<FixedType> {
    fn check_kinds(&self, context: &TypeContext<KindExpression>) -> Result<(), Error> {
        check_kind_of_type(&self.t.0, context, &self.p)?;
        self.e.check_kinds(context)
    }
}

impl ExpressionVariant<FixedType> {
    fn check_kinds(&self, context: &TypeContext<KindExpression>) -> Result<(), Error> {
        use ExpressionVariant::*;
        match self {
            IntConstant(_) | Variable(_) => Ok(()),
            Application(a, b) => {
                a.check_kinds(context)?;
                b.check_kinds(context)
            }
            Abstraction(l) => l.check_kinds(context),
            Let(binding, value, body) => {
                binding.check_kinds(context)?;
                value.check_kinds(context)?;
                body.check_kinds(context)
            }
            Pmatch(e, v) => {
                e.check_kinds(context)?;
                for case in v.iter() {
                    case.check_kinds(context)?;
                }
                Ok(())
            }
        }
    }
}

impl Case<FixedType> {
    fn check_kinds(&self, context: &TypeContext<KindExpression>) -> Result<(), Error> {
        for b in self.params.iter() {
            b.check_kinds(context)?;
        }
        self.body.check_kinds(context)
    }
}

impl Lambda<FixedType> {
    fn check_kinds(&self, context: &TypeContext<KindExpression>) -> Result<(), Error> {
        self.param.check_kinds(context)?;
        check_kind_of_type(&self.return_type.0, context, &self.p)?;
        self.tail.check_kinds(context)
    }
}

impl Binding<FixedType> {
    fn check_kinds(&self, context: &TypeContext<KindExpression>) -> Result<(), Error> {
        check_kind_of_type(&self.t.0, context, &self.p)
    }
}

impl ConstraintContext<FixedType> {
    fn check_kinds(&self, context: &TypeContext<KindExpression>) -> Result<(), Error> {
        for (t, p) in self.c.iter() {
            let kind =
                t.0.get_kind(context)
                    .map_err(|c| Error::new(c, Position::clone(p)))?;
            check_kinds_eq(kind, KindExpression::CONSTRAINT, p)?;
        }
        Ok(())
    }
}
// end check_kinds

impl Expression<FixedType> {
    pub fn new(e: ExpressionVariant<FixedType>, p: Position, t: TypeExpression) -> Self {
        Self {
            e,
            p,
            t: FixedType(t),
        }
    }
}

impl Expression<OptionalType> {
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
            t: OptionalType(None),
        }
    }
}

impl Expression<VariableType> {
    pub fn new(e: ExpressionVariant<VariableType>, p: Position, index: usize) -> Self {
        Self {
            e,
            p,
            t: VariableType(index),
        }
    }
}

impl<Type> Function<Type> {
    pub fn new(
        name: String,
        context: ConstraintContext<Type>,
        body: Expression<Type>,
        type_vars: TypeVars,
        p: Position,
    ) -> Self {
        Self {
            name,
            context,
            body,
            type_vars,
            p,
        }
    }
}

impl<Type> Binding<Type> {
    pub fn new(name: String, t: Type, p: Position) -> Self {
        Self { name, t, p }
    }
}

impl<Type> Lambda<Type> {
    pub fn new(
        param: Binding<Type>,
        return_type: Type,
        tail: Expression<Type>,
        p: Position,
    ) -> Self {
        Self {
            param,
            return_type,
            tail: Box::new(tail),
            p,
        }
    }
}

impl<Type> ConstraintContext<Type> {
    pub fn new() -> Self {
        Self { c: Vec::new() }
    }

    pub fn new_from_vec(v: Vec<(Type, Position)>) -> Self {
        Self { c: v }
    }

    pub fn add(&mut self, t: Type, p: &Position) {
        self.c.push((t, Position::clone(p)));
    }
}

impl<Type> ConstraintContext<Type>
where
    Type: PartialEq,
{
    pub fn add_unique(&mut self, t: Type, p: &Position) {
        if self.c.iter().find(|(c, p)| c == &t).is_none() {
            self.c.push((t, Position::clone(p)));
        }
    }
}

impl ConstraintContext<FixedType> {
    pub fn check_and_reduce(self) -> Result<Self, Error> {
        let mut result = Self::new();
        for (t, p) in self.c.into_iter() {
            match t
                .0
                .check_constraint()
                .map_err(|c| Error::new(c, Position::clone(&p)))?
            {
                Some(t) => result.add_unique(FixedType(t), &p),
                None => (),
            }
        }
        Ok(result)
    }
}

pub trait PrefixFormatter {
    fn write_with_prefix(&self, f: &mut fmt::Formatter<'_>, prefix: &str) -> fmt::Result;
}

impl PrefixFormatter for OptionalType {
    fn write_with_prefix(&self, f: &mut fmt::Formatter<'_>, prefix: &str) -> fmt::Result {
        match &self.0 {
            Some(t) => write!(f, "{}[{}]", prefix, t),
            None => Ok(()),
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
where
    Expression<Type>: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Application(a, b) => match b.e {
                Self::Application(_, _) => write!(f, "{} ({})", a, b),
                _ => write!(f, "{} {}", a, b),
            },
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
            Self::Pmatch(e, v) => {
                write!(f, "match {} {{\n", e)?;
                for c in v.iter() {
                    write!(f, "{}", c)?;
                }
                f.write_str("}")
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
where
    Expression<Type>: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let simply_nested = match self.tail.e {
            ExpressionVariant::Abstraction(_) => true,
            _ => false,
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

impl<Type: PrefixFormatter> fmt::Display for Case<Type>
where
    Expression<Type>: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} ", self.tc.name)?;
        for p in self.params.iter() {
            write!(f, "{} ", p)?;
        }
        write!(f, "=> {},\n", self.body)
    }
}

impl fmt::Display for TypeConstructor {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name)?;
        for param in self.params.iter() {
            write!(f, " {}", param)?;
        }
        Ok(())
    }
}

impl fmt::Display for SumType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "data {}", self.name)?;
        for i in 0..self.arity {
            write!(f, " {}", var_from_number(i))?;
        }
        f.write_str(" = ")?;
        for s in self
            .constructors
            .iter()
            .map(|c| format!("{}", c))
            .intersperse(" | ".to_string())
        {
            f.write_str(&s)?;
        }
        f.write_str(".")
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
        write!(f, "{}", self.context)?;
        write!(f, "{}", self.type_vars)?;
        self.body.t.write_with_prefix(f, "")?;
        write!(f, "]\n{} = {}.", self.name, self.body)
    }
}

impl<Type: PrefixFormatter> fmt::Display for ConstraintContext<Type> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if !self.c.is_empty() {
            for (t, _) in self.c.iter() {
                t.write_with_prefix(f, "")?;
            }
            f.write_str(" => ")?;
        }
        Ok(())
    }
}

impl<Type: PrefixFormatter> fmt::Display for Module<Type> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for t in self.types.iter() {
            write!(f, "{}\n\n", t)?;
        }
        for fun in self.functions.iter() {
            write!(f, "{}\n\n", fun)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse::parse_str;

    #[test]
    fn test_deduce_kinds() {
        let code = "data Toto a b = Mo (b a).";
        let module = parse_str(code).unwrap();
        let typed = module.deduce_types(&TypeContext::new()).unwrap();
        let kind_context = typed.deduce_kinds().unwrap();
        let toto_kind = kind_context.get("Toto").unwrap();

        use crate::type_info::KindExpression;
        // * -> (* -> *) -> *
        let expected_toto_kind = KindExpression::mapping(
            KindExpression::TYPE,
            KindExpression::mapping(
                KindExpression::mapping(KindExpression::TYPE, KindExpression::TYPE),
                KindExpression::TYPE,
            ),
        );
        assert_eq!(toto_kind, &expected_toto_kind);
    }
}
