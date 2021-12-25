mod ast;
mod type_info;
mod type_solver;
mod generic_context;
mod error;
mod position;
mod parse;
mod util;
mod graph;
mod name_context;
mod type_var_allocator;
mod type_constraint;
use crate::type_info::TypeExpression;
use crate::type_info::TypeVars;
use crate::{parse::parse, name_context::TypeContext, ast::TypeAssignment};
use crate::position::Position;
use argparse::{ArgumentParser, Store};
use type_constraint::TypeConstraint;
#[macro_use]
extern crate pest_derive;
// use crate::parse::parse;

fn create_default_context() -> TypeContext<'static, TypeAssignment> {
    let mut context: TypeContext<TypeAssignment> = TypeContext::new();
    context.set("sum", &TypeAssignment::ToplevelFunction(
        TypeVars::new(1, vec![TypeConstraint::new_num(&TypeExpression::Var(0), &Position::Builtin)]),
        TypeExpression::Function(
            Box::new(TypeExpression::Var(0)),
            Box::new(TypeExpression::Function(
                Box::new(TypeExpression::Var(0)),
                Box::new(TypeExpression::Var(0))))))).unwrap();
    
    context.set("convert", &TypeAssignment::ToplevelFunction(
        TypeVars::new(2, vec![TypeConstraint::new_num(&TypeExpression::Var(0), &Position::Builtin), TypeConstraint::new_num(&TypeExpression::Var(1), &Position::Builtin)]),
        TypeExpression::Function(
            Box::new(TypeExpression::Var(0)),
            Box::new(TypeExpression::Var(1))))).unwrap();
    context
}

fn main() {
    let mut fname = String::new();
    {
        let mut ap = ArgumentParser::new();
        ap.set_description("Cunc compiler");
        ap.refer(&mut fname).add_argument("file", Store, "Program file");
        ap.parse_args_or_exit();
    }
    let m = parse(&fname).unwrap();
    println!("{:#?}\n\n\n", &m);
    println!("{}", &m);
    let context = create_default_context();
    match m.deduce_types(&context) {
        Ok(deduced) => println!("+++++++++++++++++++\n\n{}", &deduced),
        Err(e) => eprintln!("{}", &e)
    }
}
