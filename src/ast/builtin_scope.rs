use super::ast::ConstraintContext;
use super::type_assignment::TypeAssignment;
use super::scope::TypeScope;
use super::type_info::AtomicType;
use super::type_info::TypeExpression;
use super::type_vars::TypeVars;
use super::function_header::FunctionHeader;
use crate::position::Position;

#[derive(Debug, PartialEq, Clone)]
pub struct BuiltinScope {
    fns: Vec<FunctionHeader<TypeExpression, String>>,
}

impl BuiltinScope {
    pub(super) fn new() -> Self {
        BuiltinScope {
            fns: vec![
                FunctionHeader {
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
                FunctionHeader {
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
                FunctionHeader {
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
                FunctionHeader {
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
                FunctionHeader {
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
                FunctionHeader {
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

    pub(super) fn get_function<'a>(&'a self, name: &str) -> Option<&'a FunctionHeader<TypeExpression, String>> {
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
            ).unwrap();
        }
        scope
    }

    pub(super) fn name_iter<'a>(&'a self) -> impl Iterator<Item=&'a String> {
        self.fns.iter().map(|f| &f.name)
    }
}
