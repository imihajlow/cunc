mod ast;
mod name_context;
mod parse;
pub mod type_info;
mod type_var_allocator;
mod type_solver;
mod default_context;

use crate::error::Error;
use ast::Module;
use ast::FixedType;

pub fn parse_and_deduce(fname: &str) -> Result<Module<FixedType>, Error> {
    let m = parse::parse_file(fname)?;
    let context = default_context::create_default_context();
    let deduced = m.deduce_types(&context)?;
    println!("=== DEDUCED ===\n{}", deduced);
    deduced.check_kinds()?;
    Ok(deduced)
}
