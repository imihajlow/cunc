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
use crate::parse::parse;
use argparse::{ArgumentParser, Store};
#[macro_use]
extern crate pest_derive;
// use crate::parse::parse;


fn main() {
    let mut fname = String::new();
    {
        let mut ap = ArgumentParser::new();
        ap.set_description("Cunc compiler");
        ap.refer(&mut fname).add_argument("file", Store, "Program file");
        ap.parse_args_or_exit();
    }
    let m = parse(&fname).unwrap();
    println!("{}", &m);
    let deduced = m.deduce_types().unwrap();
    println!("+++++++++++++++++++\n\n{}", &deduced);
}
