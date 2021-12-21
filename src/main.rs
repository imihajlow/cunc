mod ast;
mod type_info;
mod type_solver;
mod type_context;
mod generic_context;
mod error;
mod position;
// mod parse;
mod util;
mod graph;
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
    // println!("{}", parse(&fname).unwrap());
}
