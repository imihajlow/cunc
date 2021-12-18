use crate::position::position_from_span;
use pest::iterators::Pair;
use crate::error::Error;
use crate::type_context::TypeContext;
use crate::type_info::{CuncType, AtomicType};
use crate::{ast::*, error::ErrorCause};
use pest::Parser;

#[derive(Parser)]
#[grammar = "cunc.pest"]
pub struct CuncParser;

pub fn parse(fname: &str) -> Result<Module<UntypedExpression>, Error> {
    let code = std::fs::read_to_string(&fname).unwrap();
    let root = match CuncParser::parse(Rule::main, &code) {
        Ok(ast) => ast,
        Err(e) => {
            return Err(Error::new(ErrorCause::SyntaxError(e.to_string()), e.line_col));
        }
    };
    println!("{}", &root);
    let mut context = TypeContext::new();
    for node in root.into_iter() {
        match node.as_rule() {
            Rule::fn_decl => {
                let mut inner = node.into_inner();
                let type_spec = build_type(inner.next().unwrap())?;
                println!("{}", &type_spec);

                let mut local_context = context.push();
                let fc_idents = inner.next().unwrap().into_inner();
                let fn_body = inner.next().unwrap().into_inner();

            }
            Rule::EOI => (),
            _ => unreachable!()
        }
    }
    todo!();
}

// pair: type_fn
fn build_type(pair: Pair<Rule>) -> Result<CuncType, Error> {
    match pair.as_rule() {
        Rule::type_single => {
            let inner = pair.into_inner().next().unwrap();
            match inner.as_rule() {
                Rule::type_fn |
                Rule::uc_ident |
                Rule::lc_ident |
                _ if inner.as_str() == "()" => build_type(inner),
                _ => {
                    unreachable!();
                }
            }
        }
        Rule::type_fn => {
            Ok(CuncType::Function(
                pair
                    .into_inner()
                    .map(build_type)
                    .collect::<Result<Vec<_>,_>>()?))

        }
        Rule::type_spec => {
            let inner = pair.into_inner().next().unwrap();
            if let Rule::type_fn = inner.as_rule() {
                build_type(inner)
            } else {
                todo!()
            }
        }
        Rule::uc_ident => {
            let at = pair.as_str().parse::<AtomicType>()
                .map_err(|e| Error::new(
                    ErrorCause::AtomicTypeParseError(e),
                    position_from_span(&pair.as_span())
                ))?;
            Ok(CuncType::Atomic(at))
        }
        Rule::lc_ident => {
            todo!()
        }
        _ if pair.as_str() == "()" => Ok(CuncType::Atomic(AtomicType::Void)),
        _ => {
            unreachable!()
        }
    }
}
