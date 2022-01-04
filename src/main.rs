mod ast;
mod type_info;
mod type_solver;
mod error;
mod position;
mod parse;
mod util;
mod graph;
mod name_context;
mod type_var_allocator;
// mod type_constraint;
use crate::ast::Module;
use crate::error::Error;
use crate::ast::FixedType;
use crate::type_info::TypeExpression;
use crate::type_info::TypeVars;
use crate::{parse::parse_file, name_context::TypeContext, ast::TypeAssignment};
use crate::position::Position;
use argparse::{ArgumentParser, Store};
use ast::ConstraintContext;

use type_info::AtomicType;
#[macro_use]
extern crate pest_derive;
// use crate::parse::parse;

fn create_default_context() -> TypeContext<'static, TypeAssignment> {
    let mut context: TypeContext<TypeAssignment> = TypeContext::new();
    context.set("sum", &TypeAssignment::ToplevelFunction(
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

fn parse_and_deduce(fname: &str) -> Result<Module<FixedType>, Error> {
    let m = parse_file(fname)?;
    let context = create_default_context();
    let deduced = m.deduce_types(&context)?;
    println!("=== DEDUCED ===\n{}", deduced);
    deduced.check_kinds()?;
    Ok(deduced)
}

fn main() {
    let mut fname = String::new();
    {
        let mut ap = ArgumentParser::new();
        ap.set_description("Cunc compiler");
        ap.refer(&mut fname).add_argument("file", Store, "Program file");
        ap.parse_args_or_exit();
    }
    match parse_and_deduce(&fname) {
        Ok(deduced) => println!("=================\n\n{}", &deduced),
        Err(e) => eprintln!("{}", &e)
    }
}
