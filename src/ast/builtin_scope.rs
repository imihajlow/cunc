use super::ast::ConstraintContext;
use super::ast::TypeAssignment;
use super::scope::TypeScope;
use super::type_info::AtomicType;
use super::type_info::{TypeExpression, TypeVars};
use crate::position::Position;

pub(super) fn create_builtin_scope() -> TypeScope<'static, TypeAssignment> {
    let mut scope: TypeScope<TypeAssignment> = TypeScope::new();
    scope
        .set(
            "__add__",
            &TypeAssignment::ToplevelFunction(
                TypeVars::new(1),
                TypeExpression::new_function(
                    TypeExpression::Var(0),
                    TypeExpression::new_function(TypeExpression::Var(0), TypeExpression::Var(0)),
                ),
                ConstraintContext::new_from_vec(vec![(
                    TypeExpression::Composite(
                        Box::new(TypeExpression::Atomic(AtomicType::Num)),
                        Box::new(TypeExpression::Var(0)),
                    ),
                    Position::Builtin,
                )]),
            ),
        )
        .unwrap();

    scope
        .set(
            "__sub__",
            &TypeAssignment::ToplevelFunction(
                TypeVars::new(1),
                TypeExpression::new_function(
                    TypeExpression::Var(0),
                    TypeExpression::new_function(TypeExpression::Var(0), TypeExpression::Var(0)),
                ),
                ConstraintContext::new_from_vec(vec![(
                    TypeExpression::Composite(
                        Box::new(TypeExpression::Atomic(AtomicType::Num)),
                        Box::new(TypeExpression::Var(0)),
                    ),
                    Position::Builtin,
                )]),
            ),
        )
        .unwrap();

    scope
        .set(
            "__mul__",
            &TypeAssignment::ToplevelFunction(
                TypeVars::new(1),
                TypeExpression::new_function(
                    TypeExpression::Var(0),
                    TypeExpression::new_function(TypeExpression::Var(0), TypeExpression::Var(0)),
                ),
                ConstraintContext::new_from_vec(vec![(
                    TypeExpression::Composite(
                        Box::new(TypeExpression::Atomic(AtomicType::Num)),
                        Box::new(TypeExpression::Var(0)),
                    ),
                    Position::Builtin,
                )]),
            ),
        )
        .unwrap();

    scope
        .set(
            "__div__",
            &TypeAssignment::ToplevelFunction(
                TypeVars::new(1),
                TypeExpression::new_function(
                    TypeExpression::Var(0),
                    TypeExpression::new_function(TypeExpression::Var(0), TypeExpression::Var(0)),
                ),
                ConstraintContext::new_from_vec(vec![(
                    TypeExpression::Composite(
                        Box::new(TypeExpression::Atomic(AtomicType::Num)),
                        Box::new(TypeExpression::Var(0)),
                    ),
                    Position::Builtin,
                )]),
            ),
        )
        .unwrap();

    scope
        .set(
            "__mod__",
            &TypeAssignment::ToplevelFunction(
                TypeVars::new(1),
                TypeExpression::new_function(
                    TypeExpression::Var(0),
                    TypeExpression::new_function(TypeExpression::Var(0), TypeExpression::Var(0)),
                ),
                ConstraintContext::new_from_vec(vec![(
                    TypeExpression::Composite(
                        Box::new(TypeExpression::Atomic(AtomicType::Num)),
                        Box::new(TypeExpression::Var(0)),
                    ),
                    Position::Builtin,
                )]),
            ),
        )
        .unwrap();

    scope
        .set(
            "convert",
            &TypeAssignment::ToplevelFunction(
                TypeVars::new(2),
                TypeExpression::new_function(TypeExpression::Var(0), TypeExpression::Var(1)),
                ConstraintContext::new_from_vec(vec![
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
            ),
        )
        .unwrap();
    scope
}
