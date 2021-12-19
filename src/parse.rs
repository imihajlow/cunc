use crate::position::Position;
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

pub fn parse(fname: &str) -> Result<Module<TypedExpression>, Error> {
    let code = std::fs::read_to_string(&fname).unwrap();
    let root = match CuncParser::parse(Rule::main, &code) {
        Ok(ast) => ast,
        Err(e) => {
            return Err(Error::new(ErrorCause::SyntaxError(e.to_string()), e.line_col));
        }
    };
    println!("{}", &root);

    // collect all functions
    struct FunctionRec<'a> {
        t: CuncType,
        idents: Pair<'a, Rule>,
        body: Pair<'a, Rule>,
        pos: Position
    }
    let mut functions: Vec<FunctionRec> = Vec::new();
    for node in root.into_iter() {
        match node.as_rule() {
            Rule::fn_decl => {
                let pos = position_from_span(&node.as_span());
                let mut inner = node.into_inner();
                let type_spec = build_type(inner.next().unwrap())?;
                let fc_idents = inner.next().unwrap();
                let fn_body = inner.next().unwrap();
                functions.push(FunctionRec {
                    t: type_spec,
                    idents: fc_idents,
                    body: fn_body,
                    pos: pos
                })

            }
            Rule::EOI => (),
            _ => unreachable!()
        }
    }

    // store function types in a type context
    let mut context = TypeContext::new();
    struct FunctionBodyRec<'a> {
        name: &'a str,
        t: CuncType,
        param_names: Vec<(&'a str, Position)>,
        body: Pair<'a, Rule>,
        pos: Position
    }
    let mut bodies: Vec<FunctionBodyRec> = Vec::new();
    for rec in functions.into_iter() {
        let mut fc_idents_iter = rec.idents.into_inner()
            .map(|p| (p.as_str(), position_from_span(&p.as_span())));
        let (fn_name, fn_name_pos) = fc_idents_iter.next().unwrap();
        context.set_type(fn_name, &rec.t)
            .map_err(|cause| Error::new(cause, fn_name_pos))?;
        bodies.push(FunctionBodyRec {
            name: fn_name,
            t: rec.t,
            param_names: fc_idents_iter.collect(),
            body: rec.body,
            pos: rec.pos
        });
    }

    // process function bodies
    let mut module: Module<TypedExpression> = Module::new();
    for rec in bodies.into_iter() {
        let mut remaining_type = rec.t;
        let mut param_bindings: Vec<Binding> = Vec::new();
        let mut inner_context = context.push();
        for (name, pos) in rec.param_names.into_iter() {
            let (head, tail) = remaining_type.split_param_type()
                .map_err(|cause| Error::new(cause, Position::clone(&pos)))?;
            remaining_type = tail;
            inner_context.set_type(name, &head).map_err(|c| Error::new(c, Position::clone(&pos)))?;
            param_bindings.push(Binding::new(name.to_owned(), head, pos));
        }
        let body_pos = position_from_span(&rec.body.as_span());
        let mut statements: Vec<Statement<TypedExpression>> = Vec::new();
        let mut tail: Option<TypedExpression> = None;
        for pair in rec.body.into_inner() {
            match pair.as_rule() {
                Rule::statement => {
                    let untyped = parse_statement(pair)?;
                    statements.push(annotate_statement(untyped, &mut inner_context)?);
                }
                Rule::expression => {
                    let expr = parse_expression(pair)?;
                    tail = Some(annotate(expr, &inner_context)?);
                }
                _ => unreachable!()
            }
        }
        let lambda = Lambda::new(param_bindings, statements, tail.unwrap(), body_pos);
        let function = Function::new(rec.name.to_string(), lambda, rec.pos);
        module.push_function(function);
    }
    Ok(module)
}

fn parse_statement(pair: Pair<Rule>) -> Result<Statement<UntypedExpression>, Error> {
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
                        (build_type(part2)?, parse_expression(parts.next().unwrap())?)
                    }
                    Rule::expression => {
                        (CuncType::Unknown, parse_expression(part2)?)
                    }
                    _ => unreachable!()
                }
            };
            let binding = Binding::new(name.to_string(), t, name_pos);
            Ok(Statement::new_let(binding, expr))
        }
        _ => unreachable!()
    }
}

fn parse_expression(pair: Pair<Rule>) -> Result<UntypedExpression, Error> {
    let pos = position_from_span(&pair.as_span());
    let inner = pair.into_inner().next().unwrap();
    match inner.as_rule() {
        Rule::application => {
            let mut parsed_parts: Vec<UntypedExpression> = Vec::new();
            for part in inner.into_inner() {
                let part_position = position_from_span(&part.as_span());
                let parsed_part = if let Rule::expression = part.as_rule() {
                    parse_expression(part)?
                } else {
                    let parsed_part = match part.as_rule() {
                        Rule::lc_ident => {
                            Expression::<UntypedExpression>::Variable(part.as_str().to_string())
                        }
                        Rule::dec_constant => {
                            Expression::<UntypedExpression>::IntConstant(
                                parse_dec_constant(part)?)
                        }
                        Rule::hex_constant => {
                            Expression::<UntypedExpression>::IntConstant(
                                parse_hex_constant(part)?)
                        }
                        Rule::bin_constant => {
                            Expression::<UntypedExpression>::IntConstant(
                                parse_bin_constant(part)?)
                        }
                        _ => unreachable!()
                    };
                    UntypedExpression::new(parsed_part, part_position)
                };
                parsed_parts.push(parsed_part);
            }
            Ok(UntypedExpression::new(Expression::Application(parsed_parts), pos))
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

fn build_type(pair: Pair<Rule>) -> Result<CuncType, Error> {
    match pair.as_rule() {
        Rule::var_type_spec => build_type(pair.into_inner().next().unwrap()),
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
