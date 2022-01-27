use super::ast::ConstraintContext;
use super::type_assignment::TypeAssignment;
use super::scope::TypeScope;
use super::type_info::AtomicType;
use super::type_info::TypeExpression;
use super::type_vars::TypeVars;
use crate::position::Position;

#[derive(Debug, PartialEq, Clone)]
pub struct BuiltinFunction {
    name: String,
    t: TypeExpression,
    constraints: ConstraintContext<TypeExpression>,
    type_vars: TypeVars,
}

#[derive(Debug, PartialEq, Clone)]
pub struct BuiltinScope {
    fns: Vec<BuiltinFunction>,
}

impl BuiltinScope {
    pub(super) fn new() -> Self {
        BuiltinScope {
            fns: vec![
                BuiltinFunction {
                    name: "__add__".to_string(),
                    t: TypeExpression::new_function(
                        TypeExpression::Var(0),
                        TypeExpression::new_function(
                            TypeExpression::Var(0),
                            TypeExpression::Var(0),
                        ),
                    ),
                    constraints: ConstraintContext::new_from_vec(vec![(
                        TypeExpression::Composite(
                            Box::new(TypeExpression::Atomic(AtomicType::Num)),
                            Box::new(TypeExpression::Var(0)),
                        ),
                        Position::Builtin,
                    )]),
                    type_vars: TypeVars::new(1),
                },
                BuiltinFunction {
                    name: "__sub__".to_string(),
                    t: TypeExpression::new_function(
                        TypeExpression::Var(0),
                        TypeExpression::new_function(
                            TypeExpression::Var(0),
                            TypeExpression::Var(0),
                        ),
                    ),
                    constraints: ConstraintContext::new_from_vec(vec![(
                        TypeExpression::Composite(
                            Box::new(TypeExpression::Atomic(AtomicType::Num)),
                            Box::new(TypeExpression::Var(0)),
                        ),
                        Position::Builtin,
                    )]),
                    type_vars: TypeVars::new(1),
                },
                BuiltinFunction {
                    name: "__mul__".to_string(),
                    t: TypeExpression::new_function(
                        TypeExpression::Var(0),
                        TypeExpression::new_function(
                            TypeExpression::Var(0),
                            TypeExpression::Var(0),
                        ),
                    ),
                    constraints: ConstraintContext::new_from_vec(vec![(
                        TypeExpression::Composite(
                            Box::new(TypeExpression::Atomic(AtomicType::Num)),
                            Box::new(TypeExpression::Var(0)),
                        ),
                        Position::Builtin,
                    )]),
                    type_vars: TypeVars::new(1),
                },
                BuiltinFunction {
                    name: "__div__".to_string(),
                    t: TypeExpression::new_function(
                        TypeExpression::Var(0),
                        TypeExpression::new_function(
                            TypeExpression::Var(0),
                            TypeExpression::Var(0),
                        ),
                    ),
                    constraints: ConstraintContext::new_from_vec(vec![(
                        TypeExpression::Composite(
                            Box::new(TypeExpression::Atomic(AtomicType::Num)),
                            Box::new(TypeExpression::Var(0)),
                        ),
                        Position::Builtin,
                    )]),
                    type_vars: TypeVars::new(1),
                },
                BuiltinFunction {
                    name: "__mod__".to_string(),
                    t: TypeExpression::new_function(
                        TypeExpression::Var(0),
                        TypeExpression::new_function(
                            TypeExpression::Var(0),
                            TypeExpression::Var(0),
                        ),
                    ),
                    constraints: ConstraintContext::new_from_vec(vec![(
                        TypeExpression::Composite(
                            Box::new(TypeExpression::Atomic(AtomicType::Num)),
                            Box::new(TypeExpression::Var(0)),
                        ),
                        Position::Builtin,
                    )]),
                    type_vars: TypeVars::new(1),
                },
                BuiltinFunction {
                    name: "__convert__".to_string(),
                    t: TypeExpression::new_function(TypeExpression::Var(0), TypeExpression::Var(1)),
                    constraints: ConstraintContext::new_from_vec(vec![
                        (
                            TypeExpression::Composite(
                                Box::new(TypeExpression::Atomic(AtomicType::Num)),
                                Box::new(TypeExpression::Var(0)),
                            ),
                            Position::Builtin,
                        ),
                        (
                            TypeExpression::Composite(
                                Box::new(TypeExpression::Atomic(AtomicType::Num)),
                                Box::new(TypeExpression::Var(1)),
                            ),
                            Position::Builtin,
                        ),
                    ]),
                    type_vars: TypeVars::new(2),
                },
            ],
        }
    }

    pub(super) fn get_function<'a>(&'a self, name: &str) -> Option<&'a BuiltinFunction> {
        for f in self.fns.iter() {
            if f.name == name {
                return Some(f);
            }
        }
        None
    }

    pub(super) fn as_type_scope(&self) -> TypeScope<TypeAssignment> {
        let mut scope = TypeScope::new();
        for f in self.fns.iter() {
            scope.set(
                &f.name,
                &TypeAssignment::ToplevelFunction(
                    f.type_vars.to_owned(),
                    f.t.to_owned(),
                    f.constraints.to_owned(),
                ),
            );
        }
        scope
    }

    pub(super) fn name_iter<'a>(&'a self) -> impl Iterator<Item=&'a String> {
        self.fns.iter().map(|f| &f.name)
    }
}

pub(super) fn create_builtin_scope() -> TypeScope<'static, TypeAssignment> {
    // let mut scope: TypeScope<TypeAssignment> = TypeScope::new();
    // for b in BUILTINS.fns.iter() {
    //     scope
    //         .set(
    //             &b.name,
    //             &TypeAssignment::ToplevelFunction(
    //                 b.type_vars.to_owned(),
    //                 b.t.to_owned(),
    //                 b.constraints.to_owned(),
    //             ),
    //         )
    //         .unwrap();
    // }
    // scope

    todo!()
}
