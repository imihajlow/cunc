mod ast;
mod scope;
mod parse;
pub mod type_info;
mod type_var_allocator;
mod type_solver;
mod builtin_scope;
mod sizeof;

use type_info::TypeExpression;
use crate::error::Error;
use ast::Module;

pub use ast::Expression;
pub use ast::ExpressionVariant;
pub use ast::Binding;
pub use sizeof::Sizeof;

pub fn parse_and_deduce(fname: &str) -> Result<Module<TypeExpression>, Error> {
    let m = parse::parse_file(fname)?;
    let builtin = builtin_scope::create_builtin_scope();
    let deduced = m.deduce_types(&builtin)?;
    println!("=== DEDUCED ===\n{}", deduced);
    deduced.check_kinds()?;
    Ok(deduced)
}
