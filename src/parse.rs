use std::collections::HashMap;
use crate::position::{position_from_span, position_from_linecol};
use crate::type_info::TypeVars;
use pest::iterators::Pair;
use crate::error::Error;

use crate::type_info::{TypeExpression, AtomicType};
use crate::{ast::*, error::ErrorCause};
use pest::Parser;

#[derive(Parser)]
#[grammar = "cunc.pest"]
pub struct CuncParser;

pub fn parse(fname: &str) -> Result<Module<OptionalType>, Error> {
    let code = std::fs::read_to_string(&fname).unwrap();
    let root = match CuncParser::parse(Rule::main, &code) {
        Ok(ast) => ast,
        Err(e) => {
            return Err(Error::new(ErrorCause::SyntaxError(e.to_string()), position_from_linecol(e.line_col)));
        }
    };
    // println!("{}", &root);

    let mut result: Module<OptionalType> = Module::new();
    for node in root.into_iter() {
        match node.as_rule() {
            Rule::fn_decl => {
                let fun = parse_function(node)?;
                result.push_function(fun);
            }
            Rule::EOI => (),
            _ => unreachable!()
        }
    }

    Ok(result)
}

struct TypeVarAllocator {
    m: HashMap<String, usize>,
    cur_index: usize,
    new_vars_allowed: bool,
}

impl TypeVarAllocator {
    fn new() -> Self {
        Self {
            m: HashMap::new(),
            cur_index: 0,
            new_vars_allowed: true,
        }
    }

    fn disallow_new_vars(&mut self) {
        self.new_vars_allowed = false;
    }

    fn allocate_type_var(&mut self, name: &str) -> Result<usize, ErrorCause> {
        match self.m.get(name) {
            Some(index) => Ok(*index),
            None => {
                if self.new_vars_allowed {
                    self.m.insert(name.to_string(), self.cur_index);
                    self.cur_index += 1;
                    Ok(self.cur_index - 1)
                } else {
                    Err(ErrorCause::UnknownIdentifier(name.to_string()))
                }
            }
        }
    }

    fn as_type_vars(&self) -> TypeVars {
        TypeVars::new(self.cur_index)
    }
}


fn parse_function(pair: Pair<Rule>) -> Result<Function<OptionalType>, Error> {
    // pair: fn_decl
    // type_spec? ~ fn_idents ~ fn_body
    let pos = position_from_span(&pair.as_span());
    let mut inner = pair.into_inner();
    let mut tva = TypeVarAllocator::new();
    let (type_spec, idents) = {
        let p = inner.next().unwrap();
        match p.as_rule() {
            Rule::type_spec =>
                (Some(build_type(p, &mut tva)?), inner.next().unwrap()),
            Rule::fn_idents => (None, p),
            _ => unreachable!()
        }
    };
    tva.disallow_new_vars();
    let fn_body = inner.next().unwrap();
    let body_pos = position_from_span(&fn_body.as_span());
    let (statements, tail) = parse_fn_body(fn_body, &mut tva)?;
    let (name, bindings, ret_type) = build_bindings(idents, type_spec)?;
    let lambda = Lambda::new(bindings, OptionalType(ret_type), statements, tail, body_pos);
    Ok(Function::new(name, lambda, tva.as_type_vars(), pos))
}

fn build_bindings(fn_idents: Pair<Rule>, type_spec: Option<TypeExpression>) ->
        Result<(String, Vec<Binding<OptionalType>>, Option<TypeExpression>), Error> {
    // fn_idents = { lc_ident+ }
    let idents_pos = position_from_span(&fn_idents.as_span());
    let mut idents_iter = fn_idents.into_inner().into_iter();
    let name = idents_iter.next().unwrap().as_str().to_owned();
    let mut strpos = idents_iter.map(|p| {
        assert!(p.as_rule() == Rule::lc_ident);
        let pos = position_from_span(&p.as_span());
        let s = p.as_str().to_owned();
        (s, pos)
    });
    match type_spec {
        None => {
            // No type spec => untyped bindings
            Ok((name, strpos.map(|(s,p)| {
                Binding::new(s, OptionalType(None), p)
            }).collect(), None))
        }
        Some(ref t) => match t {
            TypeExpression::Function(ts) => {
                // Function type => create bindings
                let mut bindings: Vec<Binding<OptionalType>> = Vec::new();
                for (i, (s, pos)) in strpos.enumerate() {
                    match ts.get(i) {
                        Some(t) =>
                            bindings.push(Binding::new(s, OptionalType(Some(TypeExpression::clone(t))), pos)),
                        None =>
                            return Err(Error::new(ErrorCause::TooManyArguments, pos))
                    }
                }
                match ts.get(bindings.len()..) {
                    None =>
                        Err(Error::new(ErrorCause::TooManyArguments, idents_pos)),
                    Some(a) if a.len() == 1 =>
                        Ok((name, bindings, Some(TypeExpression::clone(a.first().unwrap())))),
                    Some(a) =>
                        Ok((name, bindings, Some(TypeExpression::Function(a.to_vec()))))
                }
            }
            _ => {
                if strpos.next().is_none() {
                    Ok((name, Vec::new(), type_spec))
                } else {
                    Err(Error::new(ErrorCause::IsAFunction, idents_pos))
                }
            }
        }
    }
}

fn parse_fn_body(body: Pair<Rule>, tva: &mut TypeVarAllocator) ->
    Result<(Vec<Statement<OptionalType>>, Expression<OptionalType>), Error> {
    // body: fn_body
    let inner = body.into_inner();
    let mut tail: Option<Expression<OptionalType>> = None;
    let mut statements: Vec<Statement<OptionalType>> = Vec::new();
    for pair in inner.into_iter() {
        match pair.as_rule() {
            Rule::statement => {
                statements.push(parse_statement(pair, tva)?);
            }
            Rule::expression => {
                tail = Some(parse_expression(pair)?);
                break;
            }
            _ => unreachable!()
        }
    }
    Ok((statements, tail.unwrap()))
}

fn parse_statement(pair: Pair<Rule>, tva: &mut TypeVarAllocator)
        -> Result<Statement<OptionalType>, Error> {
    let inner = pair.into_inner().next().unwrap();
    match inner.as_rule() {
        Rule::expression => {
            Ok(Statement::new_expr(parse_expression(inner)?))
        }
        Rule::assignment => {
            // "let" ~ lc_ident ~ (":" ~ type_single)? ~ "=" ~ expression
            let mut parts = inner.into_inner();
            let name_pair = parts.next().unwrap();
            let name_pos = position_from_span(&name_pair.as_span());
            let name = name_pair.as_str();
            let (t, expr) = {
                let part2 = parts.next().unwrap();
                match part2.as_rule() {
                    Rule::var_type_spec => {
                        (Some(build_type(part2, tva)?), parse_expression(parts.next().unwrap())?)
                    }
                    Rule::expression => {
                        (None, parse_expression(part2)?)
                    }
                    _ => unreachable!()
                }
            };
            let binding = Binding::new(name.to_string(), OptionalType(t), name_pos);
            Ok(Statement::new_let(binding, expr))
        }
        _ => unreachable!()
    }
}

fn parse_expression(pair: Pair<Rule>) -> Result<Expression<OptionalType>, Error> {
    let pos = position_from_span(&pair.as_span());
    let inner = pair.into_inner().next().unwrap();
    match inner.as_rule() {
        Rule::application => {
            let mut parsed_parts: Vec<Expression<OptionalType>> = Vec::new();
            for part in inner.into_inner() {
                let part_position = position_from_span(&part.as_span());
                let parsed_part: Expression<OptionalType> = if let Rule::expression = part.as_rule() {
                    parse_expression(part)?
                } else {
                    let parsed_part = match part.as_rule() {
                        Rule::lc_ident => {
                            ExpressionVariant::Variable(part.as_str().to_string())
                        }
                        Rule::dec_constant => {
                            ExpressionVariant::IntConstant(
                                parse_dec_constant(part)?)
                        }
                        Rule::hex_constant => {
                            ExpressionVariant::IntConstant(
                                parse_hex_constant(part)?)
                        }
                        Rule::bin_constant => {
                            ExpressionVariant::IntConstant(
                                parse_bin_constant(part)?)
                        }
                        _ => unreachable!()
                    };
                    Expression::<OptionalType>::new(parsed_part, part_position, None)
                };
                parsed_parts.push(parsed_part);
            }
            match parsed_parts.len() {
                0 => unreachable!(),
                1 => Ok(parsed_parts.pop().unwrap()),
                _ =>
                    Ok(Expression::<OptionalType>::new(
                        ExpressionVariant::Application(parsed_parts), pos, None))
            }
        }
        _ => unreachable!()
    }
}

fn parse_dec_constant(pair: Pair<Rule>) -> Result<u64, Error> {
    Ok(u64::from_str_radix(pair.as_str(), 16).unwrap()) // TODO handle error
}

fn parse_hex_constant(pair: Pair<Rule>) -> Result<u64, Error> {
    let (_, sn) = pair.as_str().split_at(2);
    Ok(u64::from_str_radix(sn, 16).unwrap()) // TODO handle error
}

fn parse_bin_constant(pair: Pair<Rule>) -> Result<u64, Error> {
    let (_, sn) = pair.as_str().split_at(2);
    Ok(u64::from_str_radix(sn, 2).unwrap()) // TODO handle error
}

fn build_type(pair: Pair<Rule>, tva: &mut TypeVarAllocator) -> Result<TypeExpression, Error> {
    match pair.as_rule() {
        Rule::var_type_spec => build_type(pair.into_inner().next().unwrap(), tva),
        Rule::type_fn => {
            Ok(TypeExpression::Function(
                pair
                    .into_inner()
                    .map(|p| build_type(p, tva))
                    .collect::<Result<Vec<_>,_>>()?))

        }
        Rule::type_spec => {
            let inner = pair.into_inner().next().unwrap();
            if let Rule::type_fn = inner.as_rule() {
                build_type(inner, tva)
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
            Ok(TypeExpression::AtomicType(at))
        }
        Rule::lc_ident => {
            Ok(TypeExpression::Var(
                tva.allocate_type_var(pair.as_str())
                    .map_err(|c| Error::new(c, position_from_span(&pair.as_span())))?
                    ))
        }
        _ if pair.as_str() == "()" => Ok(TypeExpression::AtomicType(AtomicType::Void)),
        _ => {
            unreachable!()
        }
    }
}
