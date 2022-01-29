#![allow(dead_code)]
#![allow(unstable_name_collisions)]
#![deny(unused_must_use)]
use argparse::ArgumentParser;

use argparse::Store;

mod ast;
mod cps;
mod error;
mod graph;
mod position;
mod util;

#[macro_use]
extern crate pest_derive;

fn main() {
    let mut fname = String::new();
    {
        let mut ap = ArgumentParser::new();
        ap.set_description("Cunc compiler");
        ap.refer(&mut fname)
            .add_argument("file", Store, "Program file");
        ap.parse_args_or_exit();
    }
    match ast::parse_and_deduce(&fname) {
        Ok(deduced) => println!("=================\n\n{}", &deduced),
        Err(e) => eprintln!("{}", &e),
    }
}
