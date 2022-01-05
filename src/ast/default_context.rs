use super::name_context::TypeContext;
use super::type_info::{TypeExpression, TypeVars};
use super::ast::ConstraintContext;
use super::ast::FixedType;
use super::ast::TypeAssignment;
use super::type_info::AtomicType;
use crate::position::Position;

pub(super) fn create_default_context() -> TypeContext<'static, TypeAssignment> {
    let mut context: TypeContext<TypeAssignment> = TypeContext::new();
    context.set("__add__", &TypeAssignment::ToplevelFunction(
        TypeVars::new(1),
        TypeExpression::new_function(
            TypeExpression::Var(0),
            TypeExpression::new_function(
                TypeExpression::Var(0),
                TypeExpression::Var(0))),
        ConstraintContext::new_from_vec(vec![
            (FixedType(TypeExpression::Composite(
                Box::new(TypeExpression::Atomic(AtomicType::Num)),
                Box::new(TypeExpression::Var(0)))),
            Position::Builtin)
        ]))).unwrap();

    context.set("__sub__", &TypeAssignment::ToplevelFunction(
        TypeVars::new(1),
        TypeExpression::new_function(
            TypeExpression::Var(0),
            TypeExpression::new_function(
                TypeExpression::Var(0),
                TypeExpression::Var(0))),
        ConstraintContext::new_from_vec(vec![
            (FixedType(TypeExpression::Composite(
                Box::new(TypeExpression::Atomic(AtomicType::Num)),
                Box::new(TypeExpression::Var(0)))),
            Position::Builtin)
        ]))).unwrap();

    context.set("__mul__", &TypeAssignment::ToplevelFunction(
        TypeVars::new(1),
        TypeExpression::new_function(
            TypeExpression::Var(0),
            TypeExpression::new_function(
                TypeExpression::Var(0),
                TypeExpression::Var(0))),
        ConstraintContext::new_from_vec(vec![
            (FixedType(TypeExpression::Composite(
                Box::new(TypeExpression::Atomic(AtomicType::Num)),
                Box::new(TypeExpression::Var(0)))),
            Position::Builtin)
        ]))).unwrap();

    context.set("__div__", &TypeAssignment::ToplevelFunction(
        TypeVars::new(1),
        TypeExpression::new_function(
            TypeExpression::Var(0),
            TypeExpression::new_function(
                TypeExpression::Var(0),
                TypeExpression::Var(0))),
        ConstraintContext::new_from_vec(vec![
            (FixedType(TypeExpression::Composite(
                Box::new(TypeExpression::Atomic(AtomicType::Num)),
                Box::new(TypeExpression::Var(0)))),
            Position::Builtin)
        ]))).unwrap();

    context.set("__mod__", &TypeAssignment::ToplevelFunction(
        TypeVars::new(1),
        TypeExpression::new_function(
            TypeExpression::Var(0),
            TypeExpression::new_function(
                TypeExpression::Var(0),
                TypeExpression::Var(0))),
        ConstraintContext::new_from_vec(vec![
            (FixedType(TypeExpression::Composite(
                Box::new(TypeExpression::Atomic(AtomicType::Num)),
                Box::new(TypeExpression::Var(0)))),
            Position::Builtin)
        ]))).unwrap();
    
    context.set("convert", &TypeAssignment::ToplevelFunction(
        TypeVars::new(2),
        TypeExpression::new_function(
            TypeExpression::Var(0),
            TypeExpression::Var(1)),
        ConstraintContext::new_from_vec(vec![
            (FixedType(TypeExpression::Composite(
                Box::new(TypeExpression::Atomic(AtomicType::Num)),
                Box::new(TypeExpression::Var(0)))),
            Position::Builtin),
            (FixedType(TypeExpression::Composite(
                Box::new(TypeExpression::Atomic(AtomicType::Num)),
                Box::new(TypeExpression::Var(1)))),
            Position::Builtin),
        ]))).unwrap();
    context
}
