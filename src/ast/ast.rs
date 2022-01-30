use super::builtin_scope::BuiltinScope;
use super::concrete_type::ConcreteType;
use super::function_header::FunctionHeader;
use super::instance::Instance;
use super::instance::MangledId;
use super::scope::TypeScope;
use super::type_assignment::TypeAssignment;
use super::type_info::AtomicKind;
use super::type_info::AtomicType;
use super::type_info::IntBits;
use super::type_info::IntType;
use super::type_info::KindExpression;
use super::type_info::TypeExpression;
use super::type_solver::Solution;
use super::type_solver::Solver;
use super::type_var_allocator::TypeVarAllocator;
use super::type_vars::TypeVars;
use crate::error::Error;
use crate::error::ErrorCause;
use crate::graph::ObjectGraph;
use crate::position::Position;
use crate::util::var_from_number;
use itertools::Itertools;
use std::collections::HashMap;
use std::collections::HashSet;

use std::collections::VecDeque;
use std::fmt;
use std::iter;

/*
   Type inference system takes Module<OptionalType, String>,
   assigns type variables to every part of every expression producing VariableType-based objects,
   and after deducing variable values with type_solver::Solver substitutes variables with fixed types,
   producing Module<TypeExpression, String>.
*/

/// Type which can be specified or not.
#[derive(Debug, Clone, PartialEq)]
pub(super) struct OptionalType(pub Option<TypeExpression>);

/// Type specified by a type variable.
#[derive(Debug, Clone, PartialEq)]
struct VariableType(pub usize);

#[derive(Debug, Clone, PartialEq)]
pub struct Expression<Type, Id> {
    pub t: Type,
    pub e: ExpressionVariant<Type, Id>,
    pub p: Position,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ExpressionVariant<Type, Id> {
    Application(Box<Expression<Type, Id>>, Box<Expression<Type, Id>>),
    IntConstant(u64),
    Variable(Id),
    Abstraction(Lambda<Type, Id>),
    Let(
        Binding<Type, Id>,
        Box<Expression<Type, Id>>,
        Box<Expression<Type, Id>>,
    ),
    Pmatch(Box<Expression<Type, Id>>, Vec<Case<Type, Id>>),

    // The following cases are not constructed by the parser.
    Record(Vec<Expression<Type, Id>>), // Generated from type constructors
    Offset(Box<Expression<Type, Id>>, usize), // Generated from Pmatch
    Switch(Box<Expression<Type, Id>>, Vec<(u8, Expression<Type, Id>)>), // Generated from Pmatch
}

#[derive(Debug, Clone, PartialEq)]
pub struct Case<Type, Id> {
    tc: TypeConstructor,
    params: Vec<Binding<Type, Id>>,
    body: Expression<Type, Id>,
    p: Position,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Lambda<Type, Id> {
    param: Binding<Type, Id>,
    return_type: Type,
    tail: Box<Expression<Type, Id>>,
    p: Position,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Binding<Type, Id> {
    pub name: Id,
    t: Type,
    p: Position,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Function<Type, Id> {
    header: FunctionHeader<Type, Id>,
    pub(super) body: Expression<Type, Id>,
    p: Position,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Module<Type, Id> {
    functions: Vec<Function<Type, Id>>,
    types: Vec<SumType>,
    builtin_scope: Option<BuiltinScope>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ConstraintContext<Type> {
    c: Vec<(Type, Position)>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypeConstructor {
    pub name: String,
    pub enum_index: usize,
    pub params: Vec<TypeExpression>,
    pub parent_type: TypeExpression,
    // type_vars correspond to the parent type,
    // e.g for `data Foo a b = Bar a | Baz b.` both Bar and Baz shall have two type vars
    pub type_vars: TypeVars,
    p: Position,
}

#[derive(Debug, Clone, PartialEq)]
pub struct SumType {
    pub name: String,
    pub arity: usize,
    pub constructors: Vec<TypeConstructor>,
    p: Position,
}

#[derive(Debug, Clone, PartialEq)]
enum SymbolClass {
    Builtin,
    Global,
    Local,
}

impl<Type, Id> Case<Type, Id> {
    pub(super) fn new(
        tc: TypeConstructor,
        params: Vec<Binding<Type, Id>>,
        body: Expression<Type, Id>,
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

impl<Type, Id: PartialEq> Module<Type, Id> {
    pub(super) fn new(builtin_scope: Option<BuiltinScope>) -> Self {
        Self {
            functions: Vec::new(),
            types: Vec::new(),
            builtin_scope,
        }
    }

    pub(super) fn push_function(&mut self, f: Function<Type, Id>) {
        self.functions.push(f);
    }

    pub(super) fn push_type(&mut self, t: SumType) {
        self.types.push(t);
    }

    pub(super) fn get_type<'a>(&'a self, name: &str) -> Option<&'a SumType> {
        for t in self.types.iter() {
            if t.name == name {
                return Some(t);
            }
        }
        None
    }
}

// TODO generic implementation supporting name being &str for Id=String and &Id
impl<Type> Module<Type, String> {
    pub(super) fn get_function<'a>(&'a self, name: &str) -> Option<&'a Function<Type, String>> {
        for f in self.functions.iter() {
            if f.header.name == name {
                return Some(f);
            }
        }
        None
    }

    fn get_builtin<'a>(&'a self, name: &str) -> Option<&'a FunctionHeader<TypeExpression, String>> {
        self.builtin_scope
            .as_ref()
            .and_then(|scope| scope.get_function(name))
    }
}

impl TypeConstructor {
    pub(super) fn new(
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

    pub(super) fn get_function_type(&self) -> (TypeVars, TypeExpression) {
        let mut parts = Vec::clone(&self.params);
        parts.push(TypeExpression::clone(&self.parent_type));
        (
            TypeVars::clone(&self.type_vars),
            TypeExpression::new_function_from_vec(parts),
        )
    }

    /// Create the type constructor function.
    fn create_function(&self, has_enum_index: bool) -> Function<OptionalType, String> {
        let bindings: Vec<_> = self
            .params
            .iter()
            .enumerate()
            .map(|(i, t)| {
                Binding::<OptionalType, String>::new(
                    format!("_{i}"),
                    OptionalType(Some(t.to_owned())),
                    Position::Builtin,
                )
            })
            .collect();
        let parts_iter = self.params.iter().enumerate().map(|(i, t)| {
            Expression::<OptionalType, String>::new(
                ExpressionVariant::Variable(format!("_{i}")),
                Position::Builtin,
                Some(t.to_owned()),
            )
        });

        let record = if has_enum_index {
            ExpressionVariant::Record(
                std::iter::once(Expression::<OptionalType, String>::new(
                    ExpressionVariant::IntConstant(self.enum_index as u64),
                    Position::Builtin,
                    Some(TypeExpression::Atomic(AtomicType::Int(IntType::new(
                        false,
                        IntBits::B8,
                    )))),
                ))
                .chain(parts_iter)
                .collect(),
            )
        } else {
            ExpressionVariant::Record(parts_iter.collect())
        };
        let body = Expression::<OptionalType, String>::new(
            record,
            self.p.to_owned(),
            Some(self.parent_type.to_owned()),
        );
        let header = FunctionHeader::new(
            self.name.to_owned(),
            OptionalType(Some(self.parent_type.to_owned())),
            ConstraintContext::new(),
            self.type_vars.to_owned(),
        );
        Function::<OptionalType, String>::new_curry(header, bindings, body, self.p.to_owned())
    }

    fn as_tuple(
        &self,
        solution: &Solution<AtomicType>,
        m: &Module<TypeExpression, String>,
    ) -> Result<ConcreteType, ErrorCause> {
        match self.params.len() {
            0 => Ok(ConcreteType::Tuple(Vec::new())),
            1 => ConcreteType::new(
                &solution.translate_type(self.params.first().unwrap().to_owned()),
                m,
            ),
            _ => {
                let rv: Result<Vec<_>, _> = self
                    .params
                    .iter()
                    .map(|t| ConcreteType::new(&solution.translate_type(t.to_owned()), m))
                    .collect();
                Ok(ConcreteType::Tuple(rv?))
            }
        }
    }
}

impl SumType {
    pub(super) fn new(
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

    pub(super) fn as_concrete_type(
        &self,
        params: Vec<TypeExpression>,
        m: &Module<TypeExpression, String>,
    ) -> Result<ConcreteType, ErrorCause> {
        assert!(!self.constructors.is_empty());

        let solution = Solution::<AtomicType>::new(params, 0);
        let rv: Result<Vec<_>, _> = self
            .constructors
            .iter()
            .map(|tc| tc.as_tuple(&solution, m))
            .collect();
        let r = rv?;
        if self.constructors.len() > 1 {
            Ok(ConcreteType::Enum(
                r.into_iter()
                    .enumerate()
                    .map(|(i, t)| (i as u8, t))
                    .collect(),
            ))
        } else {
            Ok(r.into_iter().next().unwrap())
        }
    }
}

impl<Type> Module<Type, String> {
    /// Build a graph of dependencies between functions.
    fn build_dependency_graph(&self) -> Result<ObjectGraph<String>, Error> {
        let mut scope: TypeScope<SymbolClass> = TypeScope::new();
        if let Some(bi) = &self.builtin_scope {
            for name in bi.name_iter() {
                scope.set(name, &SymbolClass::Builtin).unwrap();
            }
        }
        for function in self.functions.iter() {
            scope
                .set(&function.header.name, &SymbolClass::Global)
                .map_err(|c| Error::new(c, function.p.to_owned()))?;
        }
        let mut result: ObjectGraph<String> = ObjectGraph::new();
        for function in self.functions.iter() {
            let mut refs: HashSet<String> = HashSet::new();
            let mut add_ref = |n: &str, _: &Type, _: &Position| {
                refs.insert(n.to_owned());
                ()
            };
            function.body.collect_refs(&scope, &mut add_ref)?;
            result.add_node_unique(&function.header.name);
            for name in refs.into_iter() {
                result.add_edge_unique(&function.header.name, &name);
            }
        }
        Ok(result)
    }

    /// Build a graph of dependencies between custom types
    fn build_types_top_order(&self) -> Result<Vec<SumType>, Error> {
        let mut type_by_name: HashMap<String, &SumType> = HashMap::new();
        for t in self.types.iter() {
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

impl Module<OptionalType, String> {
    pub(super) fn generate_type_constructors(&mut self) {
        for t in self.types.iter() {
            for c in t.constructors.iter() {
                let fun = c.create_function(!t.constructors.is_empty());
                self.functions.push(fun);
            }
        }
    }

    pub(super) fn deduce_types(&self) -> Result<Module<TypeExpression, String>, Error> {
        let function_by_name: HashMap<String, &Function<_, _>> = HashMap::from_iter(
            self.functions
                .iter()
                .map(|f| (f.header.name.to_string(), f)),
        );
        let dep_graph = self.build_dependency_graph()?;
        let toporder = dep_graph
            .find_strongly_connected()
            .inverse_topsort()
            .unwrap();
        let mut result: Module<TypeExpression, String> = Module::new(self.builtin_scope.clone());
        let mut scope: TypeScope<TypeAssignment> = match &self.builtin_scope {
            Some(bi) => bi.as_type_scope(),
            None => TypeScope::new(),
        };

        for group in toporder.into_iter() {
            let mut group_scope = scope.push();
            let mut allocator = TypeVarAllocator::new();
            let mut solver = Solver::new();
            // First just assign indices to functions
            for fname in group.iter() {
                let pos = &function_by_name[fname].p;
                let index = allocator.allocate(pos);
                group_scope
                    .set(fname, &TypeAssignment::LocalName(index))
                    .map_err(|c| Error::new(c, Position::clone(pos)))?;
            }
            // Actually process functions
            let mut var_annotated_fns: Vec<Function<VariableType, String>> = Vec::new();
            for fname in group.iter() {
                let function = function_by_name[fname];
                let annotated_function =
                    function.assign_type_vars(&group_scope, &mut solver, &mut allocator)?;
                var_annotated_fns.push(annotated_function);
            }
            // println!("{}", &solver);
            let solution = solver.solve().map_err(|e| e.into_error(&allocator))?;
            // println!("\nSolution:\n{}", &solution);
            // Store functions in module and update scope with their types
            for function in var_annotated_fns.into_iter() {
                let deduced_fn = function.apply_solution(&solution)?;
                // println!("\n{} {}", &name, &deduced_body);
                scope
                    .set(
                        &deduced_fn.header.name,
                        &TypeAssignment::ToplevelFunction(
                            TypeVars::clone(&deduced_fn.header.type_vars),
                            TypeExpression::clone(&deduced_fn.body.t),
                            ConstraintContext::clone(&deduced_fn.header.constraints),
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

impl Module<TypeExpression, String> {
    pub(super) fn deduce_data_kinds(&self) -> Result<TypeScope<KindExpression>, Error> {
        let toporder = self.build_types_top_order()?;
        let mut scope: TypeScope<KindExpression> = TypeScope::new();
        for t in toporder.into_iter() {
            let mut solver: Solver<AtomicKind> = Solver::new();
            let mut tva = TypeVarAllocator::new();
            tva.enter_function(t.arity, &t.p);
            for c in t.constructors.iter() {
                for param in c.params.iter() {
                    let index = param
                        .create_kind_rules(&mut tva, &scope, &mut solver)
                        .map_err(|cause| Error::new(cause, Position::clone(&c.p)))?;
                    solver.add_rule(index, KindExpression::Atomic(AtomicKind::Type));
                }
            }
            let solution = solver
                .solve()
                .map_err(|e| e.into_error(&tva).with_position(Position::clone(&t.p)))?;
            let mut kind = (0..t.arity)
                .map(|i| solution.translate_var_index(i))
                .chain(iter::once(KindExpression::Atomic(AtomicKind::Type)))
                .rev()
                .reduce(|acc, b| KindExpression::Composite(Box::new(b), Box::new(acc)))
                .unwrap();
            // Assuming any remaining free var correspond to types.
            kind.substitute_free_vars(&KindExpression::Atomic(AtomicKind::Type));
            scope.set(&t.name, &kind).map_err(|c| Error::new(c, t.p))?;
        }
        Ok(scope)
    }

    pub(super) fn check_kinds(&self) -> Result<(), Error> {
        let scope = self.deduce_data_kinds()?;
        let mut solver: Solver<AtomicKind> = Solver::new();
        let mut tva = TypeVarAllocator::new();
        for f in self.functions.iter() {
            f.create_kind_rules(&mut tva, &scope, &mut solver)?
        }
        solver.solve().map_err(|e| e.into_error(&tva))?;
        Ok(())
    }
}

// collect_refs
impl<Type> Expression<Type, String> {
    /// Collect toplevel names referenced by this expression.
    /// For each referenced name together with its type a function is called.
    fn collect_refs(
        &self,
        scope: &TypeScope<SymbolClass>,
        f: &mut dyn FnMut(&str, &Type, &Position) -> (),
    ) -> Result<(), Error> {
        use ExpressionVariant::*;
        match &self.e {
            Application(a, b) => {
                a.collect_refs(scope, f)?;
                b.collect_refs(scope, f)
            }
            IntConstant(_) => Ok(()),
            Variable(n) => {
                let class = scope.get(n).unwrap();
                if class == &SymbolClass::Global {
                    f(n, &self.t, &self.p);
                }
                Ok(())
            }
            Abstraction(l) => l.collect_refs(scope, f),
            Let(b, val, body) => {
                val.collect_refs(scope, f)?;
                let mut inner_scope = scope.push();
                inner_scope
                    .set(&b.name, &SymbolClass::Local)
                    .map_err(|c| Error::new(c, self.p.to_owned()))?;
                body.collect_refs(&inner_scope, f)
            }
            Pmatch(e, v) => {
                e.collect_refs(scope, f)?;
                for c in v.iter() {
                    c.collect_refs(scope, f)?;
                }
                Ok(())
            }
            Record(v) => {
                for e in v.iter() {
                    e.collect_refs(scope, f)?;
                }
                Ok(())
            }
            Offset(_, _) => unreachable!(),
            Switch(_, _) => unreachable!(),
        }
    }
}

impl<Type> Case<Type, String> {
    fn collect_refs(
        &self,
        scope: &TypeScope<SymbolClass>,
        f: &mut dyn FnMut(&str, &Type, &Position) -> (),
    ) -> Result<(), Error> {
        let mut inner_scope = scope.push();
        for b in self.params.iter() {
            inner_scope
                .set(&b.name, &SymbolClass::Local)
                .map_err(|c| Error::new(c, self.p.to_owned()))?;
        }
        self.body.collect_refs(&inner_scope, f)
    }
}

impl<Type> Lambda<Type, String> {
    fn collect_refs(
        &self,
        scope: &TypeScope<SymbolClass>,
        f: &mut dyn FnMut(&str, &Type, &Position) -> (),
    ) -> Result<(), Error> {
        let mut inner_scope = scope.push();
        inner_scope
            .set(&self.param.name, &SymbolClass::Local)
            .map_err(|c| Error::new(c, self.p.to_owned()))?;
        self.tail.collect_refs(&inner_scope, f)
    }
}
// end collect_refs

// assign_type_vars
impl Expression<OptionalType, String> {
    /// Assign a new type variable to every part of the expression and to the expression itself,
    /// simultaniously adding rules to type solver.
    fn assign_type_vars(
        &self,
        scope: &TypeScope<TypeAssignment>,
        solver: &mut Solver<AtomicType>,
        allocator: &mut TypeVarAllocator,
        constraint_context: &mut ConstraintContext<VariableType>,
    ) -> Result<Expression<VariableType, String>, Error> {
        use ExpressionVariant::*;
        let my_var_index = allocator.allocate(&self.p);
        let my_position = Position::clone(&self.p);
        if let Some(t) = &self.t.0 {
            solver.add_rule(my_var_index, t.remap_vars(allocator));
        }
        match &self.e {
            Application(a, b) => {
                let annotated_a =
                    Box::new(a.assign_type_vars(scope, solver, allocator, constraint_context)?);
                let annotated_b =
                    Box::new(b.assign_type_vars(scope, solver, allocator, constraint_context)?);
                let head_index = annotated_a.t.0;
                let tail_index = annotated_b.t.0;
                let fn_type = TypeExpression::new_function(
                    TypeExpression::Var(tail_index),
                    TypeExpression::Var(my_var_index),
                );
                solver.add_rule(head_index, fn_type);
                Ok(Expression::<VariableType, String>::new(
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
                Ok(Expression::<VariableType, String>::new(
                    IntConstant(*x),
                    my_position,
                    my_var_index,
                ))
            }
            Variable(name) => {
                match scope.get(name) {
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
                                    let remapped_type = t.remap_vars(allocator);
                                    solver.add_rule(index, remapped_type);
                                    constraint_context.add(VariableType(index), p);
                                }
                                allocator.leave_function();
                            }
                        }
                        Ok(Expression::<VariableType, String>::new(
                            Variable(name.to_string()),
                            my_position,
                            my_var_index,
                        ))
                    }
                }
            }
            Abstraction(l) => {
                let annotated_lambda =
                    l.assign_type_vars(scope, solver, allocator, constraint_context)?;
                solver.add_rule(my_var_index, annotated_lambda.get_overall_type());
                Ok(Expression::<VariableType, String>::new(
                    Abstraction(annotated_lambda),
                    my_position,
                    my_var_index,
                ))
            }
            Let(binding, val, body) => {
                let var_index = allocator.allocate(&binding.p);
                let annotated_binding: Binding<VariableType, String> = Binding::new(
                    binding.name.to_owned(),
                    VariableType(var_index),
                    Position::clone(&binding.p),
                );
                let annotated_val =
                    val.assign_type_vars(scope, solver, allocator, constraint_context)?;
                let mut body_scope = scope.push();
                body_scope
                    .set(&binding.name, &TypeAssignment::LocalName(var_index))
                    .map_err(|c| Error::new(c, Position::clone(&binding.p)))?;
                let annotated_body =
                    body.assign_type_vars(&body_scope, solver, allocator, constraint_context)?;
                if let Some(t) = &binding.t.0 {
                    solver.add_rule(var_index, t.remap_vars(allocator));
                }
                solver.add_rule(my_var_index, TypeExpression::Var(annotated_body.t.0));
                solver.add_rule(var_index, TypeExpression::Var(annotated_val.t.0));

                Ok(Expression::<VariableType, String>::new(
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
                    e.assign_type_vars(scope, solver, allocator, constraint_context)?;
                let mut annotated_cases: Vec<Case<VariableType, String>> = Vec::new();
                for case in v.iter() {
                    let new_case = case.assign_type_vars(
                        scope,
                        solver,
                        allocator,
                        constraint_context,
                        annotated_e.t.0,
                    )?;
                    solver.add_rule(my_var_index, TypeExpression::Var(new_case.body.t.0));
                    annotated_cases.push(new_case);
                }
                Ok(Expression::<VariableType, String>::new(
                    Pmatch(Box::new(annotated_e), annotated_cases),
                    my_position,
                    my_var_index,
                ))
            }
            Record(v) => {
                let mut annotated_v: Vec<Expression<VariableType, String>> = Vec::new();
                for e in v.iter() {
                    let annotated_e =
                        e.assign_type_vars(scope, solver, allocator, constraint_context)?;
                    let var_index = allocator.allocate(&e.p);
                    solver.add_rule(var_index, e.t.0.as_ref().unwrap().to_owned()); // Records are always annotated
                    annotated_v.push(annotated_e);
                }
                Ok(Expression::<VariableType, String>::new(
                    Record(annotated_v),
                    my_position,
                    my_var_index,
                ))
            }
            Offset(_, _) => unreachable!(),
            Switch(_, _) => unreachable!(),
        }
    }
}

impl Case<OptionalType, String> {
    fn assign_type_vars(
        &self,
        scope: &TypeScope<TypeAssignment>,
        solver: &mut Solver<AtomicType>,
        allocator: &mut TypeVarAllocator,
        constraint_context: &mut ConstraintContext<VariableType>,
        parent_var_index: usize,
    ) -> Result<Case<VariableType, String>, Error> {
        let type_arity = self
            .tc
            .parent_type
            .get_max_var_index()
            .map(|x| x + 1)
            .unwrap_or(0);
        allocator.enter_function(type_arity, &self.p);
        let mut local_scope = scope.push();
        assert_eq!(self.tc.params.len(), self.params.len());
        // The expression being matched should be of the type constructor's parent type:
        solver.add_rule(parent_var_index, self.tc.parent_type.remap_vars(&allocator));
        let mut annotated_params: Vec<Binding<VariableType, String>> = Vec::new();
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
            local_scope
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
                .assign_type_vars(&local_scope, solver, allocator, constraint_context)?;
        allocator.leave_function();
        Ok(Case::new(
            TypeConstructor::clone(&self.tc),
            annotated_params,
            annotated_body,
            Position::clone(&self.p),
        ))
    }
}

impl Lambda<OptionalType, String> {
    /// Assign type variables, simultaniously adding rules to type solver.
    /// Returns annotated Lambda and its type.
    fn assign_type_vars(
        &self,
        scope: &TypeScope<TypeAssignment>,
        solver: &mut Solver<AtomicType>,
        allocator: &mut TypeVarAllocator,
        constraint_context: &mut ConstraintContext<VariableType>,
    ) -> Result<Lambda<VariableType, String>, Error> {
        let mut local_scope = scope.push();
        // Annotate parameter
        let param_index = allocator.allocate(&self.param.p);
        let new_param_binding: Binding<VariableType, String> = Binding::new(
            self.param.name.to_owned(),
            VariableType(param_index),
            Position::clone(&self.param.p),
        );
        local_scope
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
        let new_tail =
            self.tail
                .assign_type_vars(&mut local_scope, solver, allocator, constraint_context)?;
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

impl Function<OptionalType, String> {
    fn assign_type_vars(
        &self,
        scope: &TypeScope<TypeAssignment>,
        solver: &mut Solver<AtomicType>,
        allocator: &mut TypeVarAllocator,
    ) -> Result<Function<VariableType, String>, Error> {
        let my_index = scope.get(&self.header.name).unwrap().unwrap_local_name();
        let function_scope = scope.push();
        // TODO type_vars.get_vars_count must take context into account
        allocator.enter_function(self.header.type_vars.get_vars_count(), &self.p);
        let mut constraint_context = self
            .header
            .constraints
            .assign_type_vars(solver, allocator)?;
        let body = self.body.assign_type_vars(
            &function_scope,
            solver,
            allocator,
            &mut constraint_context,
        )?;
        solver.add_rule(my_index, TypeExpression::Var(body.t.0));
        allocator.leave_function();
        let header = FunctionHeader::new(
            self.header.name.to_owned(),
            VariableType(my_index),
            constraint_context,
            TypeVars::new(0),
        );
        Ok(Function::new(header, body, self.p.to_owned()))
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

impl Function<VariableType, String> {
    fn apply_solution(
        self,
        solution: &Solution<AtomicType>,
    ) -> Result<Function<TypeExpression, String>, Error> {
        Ok(Function {
            header: self.header.apply_solution(solution)?,
            body: self.body.translate_types(solution),
            p: self.p,
        })
    }
}

impl FunctionHeader<VariableType, String> {
    fn apply_solution(
        self,
        solution: &Solution<AtomicType>,
    ) -> Result<FunctionHeader<TypeExpression, String>, Error> {
        let new_constraint_context = self
            .constraints
            .translate_types(solution)
            .check_and_reduce()?;
        Ok(FunctionHeader {
            name: self.name,
            t: solution.translate_var_index(self.t.0),
            constraints: new_constraint_context,
            type_vars: TypeVars::new(solution.get_free_vars_count()),
        })
    }
}
// end assign_type_vars

impl Lambda<TypeExpression, String> {
    fn get_overall_type(&self) -> TypeExpression {
        TypeExpression::new_function(
            TypeExpression::clone(&self.param.t),
            TypeExpression::clone(&self.return_type),
        )
    }
}

impl Lambda<VariableType, String> {
    fn get_overall_type(&self) -> TypeExpression {
        TypeExpression::new_function(
            TypeExpression::Var(self.param.t.0),
            TypeExpression::Var(self.return_type.0),
        )
    }
}

// translate_types
impl Lambda<VariableType, String> {
    fn translate_types(self, solution: &Solution<AtomicType>) -> Lambda<TypeExpression, String> {
        Lambda {
            param: self.param.translate_types(solution),
            tail: Box::new(self.tail.translate_types(solution)),
            return_type: solution.translate_var_index(self.return_type.0),
            p: self.p,
        }
    }
}

impl Binding<VariableType, String> {
    fn translate_types(self, solution: &Solution<AtomicType>) -> Binding<TypeExpression, String> {
        Binding {
            name: self.name,
            t: solution.translate_var_index(self.t.0),
            p: self.p,
        }
    }
}

impl ExpressionVariant<VariableType, String> {
    fn translate_types(
        self,
        solution: &Solution<AtomicType>,
    ) -> ExpressionVariant<TypeExpression, String> {
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
            Record(v) => Record(v.into_iter().map(|c| c.translate_types(solution)).collect()),
            Offset(_, _) => unreachable!(),
            Switch(_, _) => unreachable!(),
        }
    }
}

impl Expression<VariableType, String> {
    fn translate_types(
        self,
        solution: &Solution<AtomicType>,
    ) -> Expression<TypeExpression, String> {
        Expression {
            t: solution.translate_var_index(self.t.0),
            p: self.p,
            e: self.e.translate_types(solution),
        }
    }
}

impl Case<VariableType, String> {
    fn translate_types(self, solution: &Solution<AtomicType>) -> Case<TypeExpression, String> {
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
    fn translate_types(self, solution: &Solution<AtomicType>) -> ConstraintContext<TypeExpression> {
        ConstraintContext {
            c: self
                .c
                .into_iter()
                .map(|(t, p)| (solution.translate_var_index(t.0), p))
                .collect(),
        }
    }
}
// end translate_types

// create_kind_rules
impl Expression<TypeExpression, String> {
    fn create_kind_rules(
        &self,
        tva: &mut TypeVarAllocator,
        scope: &TypeScope<KindExpression>,
        solver: &mut Solver<AtomicKind>,
    ) -> Result<(), Error> {
        let index = self
            .t
            .create_kind_rules(tva, scope, solver)
            .map_err(|c| Error::new(c, self.p.to_owned()))?;
        solver.add_rule(index, KindExpression::TYPE);
        self.e.create_kind_rules(tva, scope, solver)
    }
}

impl ExpressionVariant<TypeExpression, String> {
    fn create_kind_rules(
        &self,
        tva: &mut TypeVarAllocator,
        scope: &TypeScope<KindExpression>,
        solver: &mut Solver<AtomicKind>,
    ) -> Result<(), Error> {
        use ExpressionVariant::*;
        match self {
            IntConstant(_) | Variable(_) => Ok(()),
            Application(a, b) => {
                a.create_kind_rules(tva, scope, solver)?;
                b.create_kind_rules(tva, scope, solver)
            }
            Abstraction(l) => l.create_kind_rules(tva, scope, solver),
            Let(binding, value, body) => {
                binding.create_kind_rules(tva, scope, solver)?;
                value.create_kind_rules(tva, scope, solver)?;
                body.create_kind_rules(tva, scope, solver)
            }
            Pmatch(e, v) => {
                e.create_kind_rules(tva, scope, solver)?;
                for case in v.iter() {
                    case.create_kind_rules(tva, scope, solver)?;
                }
                Ok(())
            }
            Record(v) => {
                for e in v.iter() {
                    e.create_kind_rules(tva, scope, solver)?;
                }
                Ok(())
            }
            Offset(_, _) => unreachable!(),
            Switch(_, _) => unreachable!(),
        }
    }
}

impl Case<TypeExpression, String> {
    fn create_kind_rules(
        &self,
        tva: &mut TypeVarAllocator,
        scope: &TypeScope<KindExpression>,
        solver: &mut Solver<AtomicKind>,
    ) -> Result<(), Error> {
        for param in self.params.iter() {
            param.create_kind_rules(tva, scope, solver)?;
        }
        self.body.create_kind_rules(tva, scope, solver)
    }
}

impl Lambda<TypeExpression, String> {
    fn create_kind_rules(
        &self,
        tva: &mut TypeVarAllocator,
        scope: &TypeScope<KindExpression>,
        solver: &mut Solver<AtomicKind>,
    ) -> Result<(), Error> {
        let index = self
            .return_type
            .create_kind_rules(tva, scope, solver)
            .map_err(|c| Error::new(c, self.p.to_owned()))?;
        solver.add_rule(index, KindExpression::TYPE);
        self.param.create_kind_rules(tva, scope, solver)?;
        self.tail.create_kind_rules(tva, scope, solver)
    }
}

impl Binding<TypeExpression, String> {
    fn create_kind_rules(
        &self,
        tva: &mut TypeVarAllocator,
        scope: &TypeScope<KindExpression>,
        solver: &mut Solver<AtomicKind>,
    ) -> Result<(), Error> {
        let index = self
            .t
            .create_kind_rules(tva, scope, solver)
            .map_err(|c| Error::new(c, self.p.to_owned()))?;
        solver.add_rule(index, KindExpression::TYPE);
        Ok(())
    }
}

impl ConstraintContext<TypeExpression> {
    fn create_kind_rules(
        &self,
        tva: &mut TypeVarAllocator,
        scope: &TypeScope<KindExpression>,
        solver: &mut Solver<AtomicKind>,
    ) -> Result<(), Error> {
        for (t, p) in self.c.iter() {
            let index = t
                .create_kind_rules(tva, scope, solver)
                .map_err(|t| Error::new(t, p.to_owned()))?;
            solver.add_rule(index, KindExpression::CONSTRAINT);
        }
        Ok(())
    }
}

impl Function<TypeExpression, String> {
    fn create_kind_rules(
        &self,
        tva: &mut TypeVarAllocator,
        scope: &TypeScope<KindExpression>,
        solver: &mut Solver<AtomicKind>,
    ) -> Result<(), Error> {
        let function_scope = scope.push();
        tva.enter_function(self.header.type_vars.get_vars_count(), &self.p);
        let body_index = self
            .body
            .t
            .create_kind_rules(tva, &function_scope, solver)
            .map_err(|c| Error::new(c, self.p.to_owned()))?;
        solver.add_rule(body_index, KindExpression::TYPE);
        self.header
            .constraints
            .create_kind_rules(tva, &function_scope, solver)?;
        self.body.create_kind_rules(tva, &function_scope, solver)?;
        tva.leave_function();
        Ok(())
    }
}
// end create_kind_rules

impl Expression<TypeExpression, String> {
    pub(super) fn new(
        e: ExpressionVariant<TypeExpression, String>,
        p: Position,
        t: TypeExpression,
    ) -> Self {
        Self { e, p, t }
    }
}

impl Expression<OptionalType, String> {
    pub(super) fn new(
        e: ExpressionVariant<OptionalType, String>,
        p: Position,
        t: Option<TypeExpression>,
    ) -> Self {
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

impl Expression<VariableType, String> {
    pub(super) fn new(
        e: ExpressionVariant<VariableType, String>,
        p: Position,
        index: usize,
    ) -> Self {
        Self {
            e,
            p,
            t: VariableType(index),
        }
    }
}

impl<Type, Id> Expression<Type, Id> {
    fn new_var(id: Id, t: Type, p: Position) -> Self {
        Self {
            e: ExpressionVariant::Variable(id),
            t,
            p,
        }
    }

    pub(super) fn into_application_vec(self) -> Vec<Self> {
        use ExpressionVariant::*;
        match self.e {
            Application(a, b) => {
                let mut v = a.into_application_vec();
                v.push(*b);
                v
            }
            _ => vec![self],
        }
    }
}

impl<Type, Id> Function<Type, Id> {
    pub(super) fn new(
        header: FunctionHeader<Type, Id>,
        body: Expression<Type, Id>,
        p: Position,
    ) -> Self {
        Self { header, body, p }
    }
}

impl Function<OptionalType, String> {
    fn new_curry(
        header: FunctionHeader<OptionalType, String>,
        params: Vec<Binding<OptionalType, String>>,
        body: Expression<OptionalType, String>,
        p: Position,
    ) -> Self {
        let mut tail = body;
        for param in params.into_iter().rev() {
            let new_pos = param.p.merge(&tail.p);
            tail = Expression::<OptionalType, String>::new(
                ExpressionVariant::Abstraction(Lambda::new(
                    param,
                    tail.t.to_owned(),
                    tail,
                    new_pos.to_owned(),
                )),
                new_pos,
                None,
            )
        }
        Self {
            header,
            body: tail,
            p,
        }
    }
}

impl<Type, Id> Binding<Type, Id> {
    pub(super) fn new(name: Id, t: Type, p: Position) -> Self {
        Self { name, t, p }
    }
}

impl<Type, Id> Lambda<Type, Id> {
    pub(super) fn new(
        param: Binding<Type, Id>,
        return_type: Type,
        tail: Expression<Type, Id>,
        p: Position,
    ) -> Self {
        Self {
            param,
            return_type,
            tail: Box::new(tail),
            p,
        }
    }

    // Deconstruct Lambda into parameter name and body
    pub fn explode(self) -> (Id, Expression<Type, Id>) {
        (self.param.name, *self.tail)
    }
}

impl<Type> ConstraintContext<Type> {
    pub(super) fn new() -> Self {
        Self { c: Vec::new() }
    }

    pub(super) fn new_from_vec(v: Vec<(Type, Position)>) -> Self {
        Self { c: v }
    }

    pub(super) fn add(&mut self, t: Type, p: &Position) {
        self.c.push((t, Position::clone(p)));
    }
}

impl<Type> ConstraintContext<Type>
where
    Type: PartialEq,
{
    pub(super) fn add_unique(&mut self, t: Type, p: &Position) {
        if self.c.iter().find(|(c, _)| c == &t).is_none() {
            self.c.push((t, Position::clone(p)));
        }
    }
}

impl ConstraintContext<TypeExpression> {
    pub(super) fn check_and_reduce(self) -> Result<Self, Error> {
        let mut result = Self::new();
        for (t, p) in self.c.into_iter() {
            match t
                .check_constraint()
                .map_err(|c| Error::new(c, Position::clone(&p)))?
            {
                Some(t) => result.add_unique(t, &p),
                None => (),
            }
        }
        Ok(result)
    }
}

// instantiation
impl Expression<TypeExpression, String> {
    fn instantiate(
        &self,
        sol: &Solution<AtomicType>,
        m: &Module<TypeExpression, String>,
        scope: &TypeScope<SymbolClass>,
    ) -> Result<Expression<ConcreteType, MangledId>, Error> {
        let translated_type = sol.translate_type(self.t.to_owned());
        let concrete_type =
            ConcreteType::new(&translated_type, m).map_err(|c| Error::new(c, self.p.to_owned()))?;

        use ExpressionVariant::*;
        let ev: ExpressionVariant<ConcreteType, MangledId> = match &self.e {
            IntConstant(n) => IntConstant(*n),
            Variable(name) => {
                let id = match scope
                    .get(&name)
                    .expect(&format!("scope doesn't contain {name}"))
                {
                    SymbolClass::Global => {
                        m.get_function(&name)
                            .unwrap()
                            .header
                            .instantiate(&translated_type, m)
                            .map_err(|c| Error::new(c, self.p.to_owned()))?
                            .0
                            .name
                    }
                    SymbolClass::Local => MangledId::Local(name.to_owned()),
                    SymbolClass::Builtin => {
                        m.builtin_scope
                            .as_ref()
                            .expect("no builtin scope")
                            .get_function(&name)
                            .expect(&format!("builtins do not contain {name}"))
                            .instantiate(&translated_type, m)
                            .map_err(|c| Error::new(c, self.p.to_owned()))?
                            .0
                            .name
                    }
                };
                Variable(id)
            }
            Application(a, b) => Application(
                Box::new(a.instantiate(sol, m, scope)?),
                Box::new(b.instantiate(sol, m, scope)?),
            ),
            Let(var, val, body) => {
                let mut inner_scope = scope.push();
                inner_scope.set(&var.name, &SymbolClass::Local).unwrap();
                Let(
                    var.instantiate(sol, m)?,
                    Box::new(val.instantiate(sol, m, scope)?),
                    Box::new(body.instantiate(sol, m, &inner_scope)?),
                )
            }
            Abstraction(l) => Abstraction(l.instantiate(sol, m, scope)?),
            Pmatch(e, cases) => {
                pmatch_to_switch(&e, &concrete_type, &self.p, &cases, sol, m, scope)?
            }
            Record(parts) => {
                let rv: Result<Vec<_>, _> =
                    parts.iter().map(|e| e.instantiate(sol, m, scope)).collect();
                Record(rv?)
            }
            Offset(_, _) => unreachable!(),
            Switch(_, _) => unreachable!(),
        };
        Ok(Expression {
            t: concrete_type,
            e: ev,
            p: self.p.to_owned(),
        })
    }
}

fn pmatch_to_switch(
    e: &Expression<TypeExpression, String>,
    result_type: &ConcreteType,
    outer_pos: &Position,
    cases: &Vec<Case<TypeExpression, String>>,
    sol: &Solution<AtomicType>,
    m: &Module<TypeExpression, String>,
    scope: &TypeScope<SymbolClass>,
) -> Result<ExpressionVariant<ConcreteType, MangledId>, Error> {
    //! Transforms this:
    //!     match e {
    //!         Foo a b => c,
    //!         Bar d f => g,
    //!     }
    //!
    //! Into this:
    //!     let switch_var = e;
    //!     switch OFFSET(e, 0) {
    //!         case 0:
    //!             let a = OFFSET(e, 1);
    //!             let b = OFFSET(e, 5);
    //!             f,
    //!         case 1:
    //!             let d = OFFSET(e, 1);
    //!             let f = OFFSET(e, 2);
    //!             g,
    //!     }

    assert!(cases.len() >= 1);
    let has_enum_index = cases.len() > 1; // TODO check parent type instead
    let e_inst = e.instantiate(sol, m, scope)?;
    let switch_var = MangledId::new_auto();

    let inner_expr = if has_enum_index {
        // enum index is at offset zero and is a byte
        let switch_val_offset: Expression<ConcreteType, MangledId> = Expression {
            e: ExpressionVariant::Offset(
                Box::new(Expression::new_var(
                    switch_var.to_owned(),
                    e_inst.t.to_owned(),
                    e_inst.p.to_owned(),
                )),
                0,
            ),
            t: ConcreteType::Int(IntType::new(false, IntBits::B8)),
            p: e.p.to_owned(),
        };
        let rcases: Result<Vec<(u8, Expression<ConcreteType, MangledId>)>, Error> = cases
            .iter()
            .map(|case| {
                let index = case.tc.enum_index as u8;
                let case_expr = case.as_let_offset(&switch_var, true, sol, m, scope)?;
                Ok((index, case_expr))
            })
            .collect();
        Expression::<ConcreteType, MangledId> {
            e: ExpressionVariant::Switch(Box::new(switch_val_offset), rcases?),
            t: result_type.to_owned(),
            p: outer_pos.to_owned(),
        }
    } else {
        let case = cases.first().unwrap();
        case.as_let_offset(&switch_var, false, sol, m, scope)?
    };
    let outer_let = ExpressionVariant::<ConcreteType, MangledId>::Let(
        Binding::new(switch_var, e_inst.t.to_owned(), e_inst.p.to_owned()),
        Box::new(e_inst),
        Box::new(inner_expr),
    );
    Ok(outer_let)
}

impl Case<TypeExpression, String> {
    /// Produce nested `let`s to deconstruct `var` according to this match case.
    fn as_let_offset(
        &self,
        var: &MangledId,
        has_enum_offset: bool,
        sol: &Solution<AtomicType>,
        m: &Module<TypeExpression, String>,
        scope: &TypeScope<SymbolClass>,
    ) -> Result<Expression<ConcreteType, MangledId>, Error> {
        let mut offset: usize = if has_enum_offset { 1 } else { 0 };
        let mut inner_scope = scope.push();
        for binding in self.params.iter() {
            inner_scope
                .set(&binding.name, &SymbolClass::Local)
                .map_err(|c| Error::new(c, binding.p.to_owned()))?;
        }
        let mut body = self.body.instantiate(sol, m, &inner_scope)?;
        let ret_type = body.t.to_owned();
        for binding in self.params.iter() {
            let instantiated_binding = binding.instantiate(sol, m)?;
            let offset_expr = Expression {
                e: ExpressionVariant::Offset(
                    Box::new(Expression::new_var(
                        var.to_owned(),
                        instantiated_binding.t.to_owned(),
                        instantiated_binding.p.to_owned(),
                    )),
                    offset,
                ),
                t: instantiated_binding.t.to_owned(),
                p: instantiated_binding.p.to_owned(),
            };
            offset += instantiated_binding.t.get_size();
            body = Expression {
                e: ExpressionVariant::Let(
                    instantiated_binding,
                    Box::new(offset_expr),
                    Box::new(body),
                ),
                t: ret_type.to_owned(),
                p: self.p.to_owned(),
            };
        }
        Ok(body)
    }
}

impl Binding<TypeExpression, String> {
    fn instantiate(
        &self,
        sol: &Solution<AtomicType>,
        m: &Module<TypeExpression, String>,
    ) -> Result<Binding<ConcreteType, MangledId>, Error> {
        let translated_type = sol.translate_type(self.t.to_owned());
        let concrete_type =
            ConcreteType::new(&translated_type, m).map_err(|c| Error::new(c, self.p.to_owned()))?;
        Ok(Binding {
            name: MangledId::Local(self.name.clone()),
            t: concrete_type,
            p: self.p.to_owned(),
        })
    }
}

impl Lambda<TypeExpression, String> {
    fn instantiate(
        &self,
        sol: &Solution<AtomicType>,
        m: &Module<TypeExpression, String>,
        scope: &TypeScope<SymbolClass>,
    ) -> Result<Lambda<ConcreteType, MangledId>, Error> {
        let translated_type = sol.translate_type(self.return_type.to_owned());
        let mut inner_scope = scope.push();
        inner_scope
            .set(&self.param.name, &SymbolClass::Local)
            .unwrap();
        Ok(Lambda {
            param: self.param.instantiate(sol, m)?,
            return_type: ConcreteType::new(&translated_type, m)
                .map_err(|c| Error::new(c, self.p.to_owned()))?,
            tail: Box::new(self.tail.instantiate(sol, m, &inner_scope)?),
            p: self.p.to_owned(),
        })
    }
}

impl FunctionHeader<TypeExpression, String> {
    /// Assign generic type variables to specific values given defined type of this function.
    fn instantiate(
        &self,
        t: &TypeExpression,
        m: &Module<TypeExpression, String>,
    ) -> Result<
        (
            FunctionHeader<ConcreteType, MangledId>,
            Solution<AtomicType>,
        ),
        ErrorCause,
    > {
        let mut solver: Solver<AtomicType> = Solver::new();
        solver.announce_vars(&self.type_vars);
        let index = self.type_vars.get_vars_count();
        solver.add_rule(index, t.to_owned());
        solver.add_rule(index, self.t.to_owned());
        let solution = solver.solve().map_err(|e| e.into_error_cause())?;
        if solution.get_free_vars_count() != 0 {
            return Err(ErrorCause::UnresolvedGenericVars);
        }
        let id = MangledId::Global(
            self.name.to_owned(),
            self.type_vars.instantiate(m, &solution)?,
        );
        let translated_type = solution.translate_type(self.t.to_owned());
        Ok((
            FunctionHeader {
                name: id,
                t: ConcreteType::new(&translated_type, m)?,
                constraints: ConstraintContext::new(),
                type_vars: TypeVars::new(0),
            },
            solution,
        ))
    }
}

impl Function<TypeExpression, String> {
    fn instantiate(
        &self,
        t: &TypeExpression,
        m: &Module<TypeExpression, String>,
        scope: &TypeScope<SymbolClass>,
    ) -> Result<Function<ConcreteType, MangledId>, Error> {
        let (header, sol) = self
            .header
            .instantiate(t, m)
            .map_err(|c| Error::new(c, Position::Unknown))?;
        let body = self.body.instantiate(&sol, m, scope)?;
        Ok(Function {
            header,
            body,
            p: self.p.to_owned(),
        })
    }
}

impl Module<TypeExpression, String> {
    pub fn instantiate(&self, entry: (&str, &TypeExpression)) -> Result<Instance, Error> {
        let mut result = Instance::new();
        let instances = self.collect_instance_refs(entry)?;
        let mut scope = TypeScope::new();
        for (n, c, _) in instances.iter() {
            scope.set_dup(n, c).unwrap();
        }
        for (n, c, t) in instances.into_iter() {
            match c {
                SymbolClass::Global => {
                    let fun = self.get_function(&n).unwrap();
                    let instance = fun.instantiate(&t, self, &scope)?;
                    result.push_function(instance);
                }
                SymbolClass::Builtin => {
                    let fun = self
                        .builtin_scope
                        .as_ref()
                        .unwrap()
                        .get_function(&n)
                        .unwrap();
                    let instance = fun
                        .instantiate(&t, self)
                        .map_err(|c| Error::new(c, Position::Unknown))?
                        .0;
                    result.push_builtin(instance);
                }
                SymbolClass::Local => unreachable!(),
            }
        }
        Ok(result)
    }

    fn collect_instance_refs(
        &self,
        entry: (&str, &TypeExpression),
    ) -> Result<Vec<(String, SymbolClass, TypeExpression)>, Error> {
        let mut processed: HashSet<(String, TypeExpression)> = HashSet::new();
        let mut bfs_queue: VecDeque<(String, TypeExpression)> = VecDeque::new();
        let mut result: Vec<(String, SymbolClass, TypeExpression)> = Vec::new();

        bfs_queue.push_back((entry.0.to_owned(), entry.1.to_owned()));

        let mut global_scope = TypeScope::new();

        for fun in self.functions.iter() {
            global_scope
                .set(&fun.header.name, &SymbolClass::Global)
                .unwrap();
        }

        if let Some(builtins) = &self.builtin_scope {
            for name in builtins.name_iter() {
                // builtins are marked as globals to let collect_refs collect them
                global_scope.set(name, &SymbolClass::Global).unwrap();
            }
        }

        while let Some((name, t)) = bfs_queue.pop_front() {
            if processed.contains(&(name.to_owned(), t.to_owned())) {
                continue;
            }
            if let Some(fun) = self.get_function(&name) {
                let mut solver = Solver::new();
                let index = fun.header.type_vars.get_vars_count();
                solver.add_rule(index, t.to_owned());
                solver.add_rule(index, fun.header.t.to_owned());
                let solution = solver.solve().unwrap();
                fun.body
                    .collect_refs(&global_scope, &mut |ref_name, ref_type, _ref_pos| {
                        let ref_type_inst = solution.translate_type(ref_type.to_owned());
                        let entry = (ref_name.to_string(), ref_type_inst);
                        if !processed.contains(&entry) {
                            println!("insert {} {}", entry.0, entry.1);
                            bfs_queue.push_back(entry);
                        }
                    })?;
                result.push((name.to_owned(), SymbolClass::Global, t.to_owned()));
            } else if self.get_builtin(&name).is_some() {
                result.push((name.to_owned(), SymbolClass::Builtin, t.to_owned()));
            } else {
                unreachable!() // names are already checked before
            }
            processed.insert((name, t));
        }
        Ok(result)
    }
}
// end instantiation

impl From<TypeAssignment> for SymbolClass {
    fn from(v: TypeAssignment) -> Self {
        match v {
            TypeAssignment::ToplevelFunction(..) => SymbolClass::Builtin,
            TypeAssignment::LocalName(..) => SymbolClass::Local,
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
            None => Ok(()),
        }
    }
}

impl PrefixFormatter for VariableType {
    fn write_with_prefix(&self, f: &mut fmt::Formatter<'_>, prefix: &str) -> fmt::Result {
        write!(f, "{}[{}]", prefix, var_from_number(self.0))
    }
}

impl PrefixFormatter for TypeExpression {
    fn write_with_prefix(&self, f: &mut fmt::Formatter<'_>, prefix: &str) -> fmt::Result {
        write!(f, "{}[{}]", prefix, self)
    }
}

impl PrefixFormatter for ConcreteType {
    fn write_with_prefix(&self, f: &mut fmt::Formatter<'_>, prefix: &str) -> fmt::Result {
        write!(f, "{}[{}]", prefix, self)
    }
}

impl<Type: PrefixFormatter, Id: fmt::Display> fmt::Display for ExpressionVariant<Type, Id>
where
    Expression<Type, Id>: fmt::Display,
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
            Self::Record(v) => {
                f.write_str("{")?;
                for s in v
                    .iter()
                    .map(|e| format!("{e}"))
                    .intersperse(", ".to_string())
                {
                    f.write_str(&s)?;
                }
                f.write_str("}")
            }
            Self::Offset(e, offset) => {
                write!(f, "OFFSET({e}, {offset})")
            }
            Self::Switch(e, v) => {
                write!(f, "switch {e} {{\n")?;
                for (i, c) in v.iter() {
                    write!(f, "case {i}: {c}\\n")?;
                }
                f.write_str("}")
            }
        }
    }
}

impl<Type: PrefixFormatter, Id: fmt::Display> fmt::Display for Expression<Type, Id> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.e)?;
        self.t.write_with_prefix(f, " :: ")
    }
}

impl<Type: PrefixFormatter, Id: fmt::Display> fmt::Display for Lambda<Type, Id>
where
    Expression<Type, Id>: fmt::Display,
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

impl<Type: PrefixFormatter, Id: fmt::Display> fmt::Display for Case<Type, Id>
where
    Expression<Type, Id>: fmt::Display,
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

impl<Type: PrefixFormatter, Id: fmt::Display> fmt::Display for Binding<Type, Id> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", &self.name)?;
        self.t.write_with_prefix(f, " :: ")
    }
}

impl<Type: PrefixFormatter, Id: fmt::Display> fmt::Display for Function<Type, Id> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} = {}.", self.header, self.body)
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

impl<Type: PrefixFormatter, Id: fmt::Display> fmt::Display for Module<Type, Id> {
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
    use crate::ast::type_info::CompositeExpression;

    use super::super::parse::parse_str;
    use super::*;

    #[test]
    fn test_deduce_kinds() {
        let code = "data Toto a b = Mo (b a).";
        let mut module = parse_str(code).unwrap();
        module.generate_type_constructors();
        let typed = module.deduce_types().unwrap();
        let kind_scope = typed.deduce_data_kinds().unwrap();
        let toto_kind = kind_scope.get("Toto").unwrap();

        use super::super::type_info::KindExpression;
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

    #[test]
    fn test_check_kinds_error() {
        let code = "data Foo a b = Bar (b a) | Baz b.";
        let mut module = parse_str(code).unwrap();
        module.generate_type_constructors();
        let typed = module.deduce_types().unwrap();
        assert!(typed.check_kinds().is_err());
    }

    #[test]
    fn test_check_kinds_ok() {
        let code = "data Foo a b = Bar (b a) | Baz.";
        let mut module = parse_str(code).unwrap();
        module.generate_type_constructors();
        let typed = module.deduce_types().unwrap();
        assert!(typed.check_kinds().is_ok());
    }

    #[test]
    fn test_instantiate_smoke() {
        let code = "
            data Foo a b = Bar a b | Baz.

            foo x = match x {
                Bar y z => y + z,
                Baz => 0,
            }.

            [U16 -> U16]
            main x = foo (Bar x x).
        ";
        let mut module = parse_str(code).unwrap();
        module.generate_type_constructors();
        let typed = module.deduce_types().unwrap();
        assert!(typed.check_kinds().is_ok());
        let main = typed.get_function("main").unwrap();

        let t: TypeExpression = TypeExpression::new_function(
            CompositeExpression::Atomic(AtomicType::Int(IntType::new(false, IntBits::B16))),
            CompositeExpression::Atomic(AtomicType::Int(IntType::new(false, IntBits::B16))),
        );
        let mut scope = TypeScope::new();
        scope.set("__add__", &SymbolClass::Builtin).unwrap();
        scope.set("foo", &SymbolClass::Global).unwrap();
        scope.set("Bar", &SymbolClass::Global).unwrap();
        scope.set("Baz", &SymbolClass::Global).unwrap();
        main.instantiate(&t, &typed, &scope).unwrap();
    }

    #[test]
    fn test_instantiate_fn() {
        let code = "
            foo x = x.
        ";
        let mut module = parse_str(code).unwrap();
        module.generate_type_constructors();
        let typed = module.deduce_types().unwrap();
        assert!(typed.check_kinds().is_ok());
        let foo = typed.get_function("foo").unwrap();

        let tu16 = IntType::new(false, IntBits::B16);
        let t: TypeExpression = TypeExpression::new_function(
            CompositeExpression::Atomic(AtomicType::Int(tu16.to_owned())),
            CompositeExpression::Atomic(AtomicType::Int(tu16.to_owned())),
        );
        let scope = TypeScope::new();
        let instance = foo.instantiate(&t, &typed, &scope).unwrap();
        assert_eq!(
            instance.header.name,
            MangledId::Global("foo".to_string(), vec![ConcreteType::Int(tu16.to_owned())])
        );
        assert_eq!(
            instance.header.t,
            ConcreteType::Function(
                Box::new(ConcreteType::Int(tu16.to_owned())),
                Box::new(ConcreteType::Int(tu16.to_owned()))
            )
        );
    }

    #[test]
    fn test_collect_instance_refs() {
        let code = "
            data Foo a b = Bar a b | Baz.

            foo x = match x {
                Bar y z => y + z,
                Baz => 0,
            }.

            [U16 -> U16]
            main x = foo (Bar x x).
        ";
        let mut module = parse_str(code).unwrap();
        module.generate_type_constructors();
        let typed = module.deduce_types().unwrap();
        assert!(typed.check_kinds().is_ok());

        let tu16 = IntType::new(false, IntBits::B16);
        let main_type: TypeExpression = TypeExpression::new_function(
            CompositeExpression::Atomic(AtomicType::Int(tu16.to_owned())),
            CompositeExpression::Atomic(AtomicType::Int(tu16.to_owned())),
        );
        let data_foo_type: TypeExpression = CompositeExpression::Composite(
            Box::new(CompositeExpression::Composite(
                Box::new(CompositeExpression::Atomic(AtomicType::User(
                    "Foo".to_owned(),
                ))),
                Box::new(CompositeExpression::Atomic(AtomicType::Int(
                    tu16.to_owned(),
                ))),
            )),
            Box::new(CompositeExpression::Atomic(AtomicType::Int(
                tu16.to_owned(),
            ))),
        );
        let bar_type: TypeExpression = TypeExpression::new_function_from_vec(vec![
            CompositeExpression::Atomic(AtomicType::Int(tu16.to_owned())),
            CompositeExpression::Atomic(AtomicType::Int(tu16.to_owned())),
            data_foo_type.to_owned(),
        ]);
        let foo_type = TypeExpression::new_function(
            data_foo_type.to_owned(),
            CompositeExpression::Atomic(AtomicType::Int(tu16.to_owned())),
        );
        let add_type = TypeExpression::new_function_from_vec(vec![
            CompositeExpression::Atomic(AtomicType::Int(tu16.to_owned())),
            CompositeExpression::Atomic(AtomicType::Int(tu16.to_owned())),
            CompositeExpression::Atomic(AtomicType::Int(tu16.to_owned())),
        ]);

        let inst_refs = typed.collect_instance_refs(("main", &main_type)).unwrap();
        assert_eq!(inst_refs.len(), 4);
        assert!(inst_refs.contains(&(
            "main".to_string(),
            SymbolClass::Global,
            main_type
        )));
        assert!(inst_refs.contains(&("Bar".to_string(), SymbolClass::Global, bar_type)));
        assert!(inst_refs.contains(&("foo".to_string(), SymbolClass::Global, foo_type)));
        assert!(inst_refs.contains(&(
            "__add__".to_string(),
            SymbolClass::Builtin,
            add_type
        )));
    }
}
