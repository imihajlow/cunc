use std::collections::HashSet;
use pest::iterators::Pairs;
use std::collections::HashMap;
use crate::position::{position_from_span, position_from_linecol, Position};
use crate::type_constraint::TypeConstraint;
use crate::type_info::TypeVars;
use pest::iterators::Pair;
use crate::error::Error;
use crate::type_info::{TypeExpression, AtomicType};
use crate::{ast::*, error::ErrorCause};
use pest::Parser;
use itertools::Itertools;

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
            Rule::type_def => {
                let t = parse_type_definition(node.into_inner())?;
                result.push_type(t);
            }
            Rule::EOI => (),
            _ => unreachable!()
        }
    }

    Ok(result)
}

#[derive(Debug)]
struct TypeVarAllocator {
    m: HashMap<String, usize>,
    constraints: Vec<TypeConstraint>,
    cur_index: usize,
    new_vars_allowed: bool,
}

impl TypeVarAllocator {
    fn new() -> Self {
        Self {
            m: HashMap::new(),
            constraints: Vec::new(),
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

    fn add_constraint(&mut self, c: TypeConstraint) {
        self.constraints.push(c);
    }

    fn into_type_vars(self) -> TypeVars {
        TypeVars::new(self.cur_index, self.constraints)
    }

    fn get_type_vars(&self) -> TypeVars {
        TypeVars::new(self.cur_index, Vec::clone(&self.constraints))
    }

    fn get_arity(&self) -> usize {
        self.cur_index
    }
}


fn parse_function(pair: Pair<Rule>) -> Result<Function<OptionalType>, Error> {
    // pair: fn_decl
    // type_spec? ~ fn_idents ~ fn_body
    let pos = position_from_span(&pair.as_span());
    let mut inner = pair.into_inner();
    let mut tva = TypeVarAllocator::new();
    let (type_spec, name, param_idents) = {
        let p = inner.next().unwrap();
        match p.as_rule() {
            Rule::type_spec =>
                (
                    Some(parse_type(p, &mut tva)?),
                    inner.next().unwrap().as_str(),
                    inner.next().unwrap()
                ),
            Rule::lc_ident =>
                (
                    None,
                    p.as_str(),
                    inner.next().unwrap()
                ),
            _ => unreachable!()
        }
    };
    tva.disallow_new_vars();
    let body_pair = inner.next().unwrap();
    let body_expr = parse_expression(body_pair, &mut tva)?;
    let body = build_lambda(param_idents.into_inner(), type_spec, body_expr)?;
    Ok(Function::new(name.to_string(), body, tva.into_type_vars(), pos))
}

fn substitute_return_type(body: Expression<OptionalType>, rt: Option<TypeExpression>)
    -> Result<Expression<OptionalType>, Error> {
    match (&body.t.0, rt) {
        (None, None) => Ok(body),
        (Some(_), None) => Ok(body),
        (None, Some(t)) => Ok(Expression::<OptionalType>::new(body.e, body.p, Some(t))),
        (Some(_), Some(_)) => Err(Error::new(ErrorCause::MultipleTypeSpecification, body.p))
    }
}

/// Build maybe nested lambda expression from a list of params, type and body.
fn build_lambda(mut param_idents: Pairs<Rule>,
                types: Option<TypeExpression>,
                body: Expression<OptionalType>)
            -> Result<Expression<OptionalType>, Error> {
    match param_idents.next() {
        None => {
            substitute_return_type(body, types)
        }
        Some(p) if p.as_str().len() == 0 => {
            substitute_return_type(body, types)
        }
        Some(p) => {
            let param_pos = position_from_span(&p.as_span());
            let param_name = p.as_str().to_string();
            // It's at least a function with one argument.
            // If a type is specified, it must be a function type.
            let (param_type, rest_types) = if let Some(t) = types {
                if let Some((a, b)) = t.match_function() {
                    (Some(TypeExpression::clone(a)), Some(TypeExpression::clone(b)))
                } else {
                    return Err(Error::new(ErrorCause::TooManyArguments, param_pos))
                }                    
            } else {
                (None, None)
            };
            let binding: Binding<OptionalType> =
                Binding::new(param_name, OptionalType(param_type), Position::clone(&param_pos));
            let inner_expression =
                build_lambda(param_idents, rest_types, body)?;
            let my_position = param_pos.merge(&inner_expression.p);
            let lambda: Lambda<OptionalType> =
                Lambda::new(binding,
                    OptionalType(None),
                    inner_expression,
                    Position::clone(&my_position));
            let abstraction: ExpressionVariant<OptionalType> =
                ExpressionVariant::Abstraction(lambda);
            Ok(Expression::<OptionalType>::new(abstraction, my_position, None))
        }
    }
}

fn parse_expression(pair: Pair<Rule>, tva: &mut TypeVarAllocator) -> Result<Expression<OptionalType>, Error> {
    let pos = position_from_span(&pair.as_span());
    match pair.as_rule() {
        Rule::expression => {
            parse_expression(pair.into_inner().next().unwrap(), tva)
        }
        Rule::application => {
            let mut collected_expr: Option<Expression<OptionalType>> = None;
            for part in pair.into_inner() {
                let part_position = position_from_span(&part.as_span());
                let parsed_part: Expression<OptionalType> = if let Rule::expression = part.as_rule() {
                    parse_expression(part, tva)?
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
                collected_expr = match collected_expr {
                    None => Some(parsed_part),
                    Some(e) => Some(Expression::new_application(e, parsed_part))
                }
            }
            Ok(collected_expr.unwrap())
        }
        Rule::assignment => {
            let mut inner = pair.into_inner();
            let name_pair = inner.next().unwrap();
            assert_eq!(name_pair.as_rule(), Rule::lc_ident);
            let name_pos = position_from_span(&name_pair.as_span());
            let name = name_pair.as_str().to_string();
            let (var_type_spec, value) = {
                let next = inner.next().unwrap();
                match next.as_rule() {
                    Rule::var_type_spec => {
                        let e_pair = inner.next().unwrap();
                        assert!(e_pair.as_rule() == Rule::expression);
                        (Some(parse_type(next, tva)?), parse_expression(e_pair, tva)?)
                    }
                    Rule::expression => {
                        (None, parse_expression(next, tva)?)
                    }
                    _ => unreachable!()
                }
            };
            let body_pair = inner.next().unwrap();
            assert!(body_pair.as_rule() == Rule::expression);
            let body = parse_expression(body_pair, tva)?;
            let binding: Binding<OptionalType> =
                Binding::new(name, OptionalType(var_type_spec), name_pos);
            let ev = ExpressionVariant::Let(binding, Box::new(value), Box::new(body));
            Ok(Expression::<OptionalType>::new(ev, pos, None))
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

fn parse_type(pair: Pair<Rule>, tva: &mut TypeVarAllocator) -> Result<TypeExpression, Error> {
    match pair.as_rule() {
        Rule::var_type_spec => parse_type(pair.into_inner().next().unwrap(), tva),
        Rule::arrow_type => {
            let mut inner = pair.into_inner();
            let head = parse_type(inner.next().unwrap(), tva)?;
            let tail = match inner.next() {
                Some(t) => {
                    assert_eq!(t.as_rule(), Rule::arrow_type);
                    Some(parse_type(t, tva)?)
                }
                None => None
            };
            Ok(match tail {
                None => head,
                Some(t) => TypeExpression::new_function(head, t)
            })
        }
        Rule::application_type => {
            let mut inner = pair.into_inner();
            let first = parse_type(inner.next().unwrap(), tva)?;
            inner
                .map(|pair| parse_type(pair, tva))
                .fold_ok(first, |acc, t|
                    TypeExpression::Composite(
                        Box::new(acc),
                        Box::new(t)))
        }
        Rule::type_spec => {
            let mut inner = pair.into_inner();
            let first = inner.next().unwrap();
            if let Rule::arrow_type = first.as_rule() {
                parse_type(first, tva)
            } else {
                assert_eq!(first.as_rule(), Rule::constraints_decl);
                let type_fn = inner.next().unwrap();
                assert_eq!(type_fn.as_rule(), Rule::arrow_type);
                parse_type_constraints(first.into_inner(), tva)?;
                parse_type(type_fn, tva)
            }
        }
        Rule::terminal_type => {
            parse_type(pair.into_inner().next().unwrap(), tva)
        }
        Rule::uc_ident => {
            let at = pair.as_str().parse::<AtomicType>()
                .map_err(|e| Error::new(
                    ErrorCause::AtomicTypeParseError(e),
                    position_from_span(&pair.as_span())
                ))?;
            Ok(TypeExpression::Atomic(at))
        }
        Rule::lc_ident => {
            Ok(TypeExpression::Var(
                tva.allocate_type_var(pair.as_str())
                    .map_err(|c| Error::new(c, position_from_span(&pair.as_span())))?
                    ))
        }
        x => {
            println!("{:?}", x);
            unreachable!()
        }
    }
}

fn parse_type_constraints(inner: Pairs<Rule>, tva: &mut TypeVarAllocator)
    -> Result<(), Error> {
    for pair in inner {
        assert_eq!(pair.as_rule(), Rule::constraint_decl);
        let pos = position_from_span(&pair.as_span());
        let mut parts = pair.into_inner();
        let name_part = parts.next().unwrap();
        assert_eq!(name_part.as_rule(), Rule::uc_ident);
        let name_pos = position_from_span(&name_part.as_span());
        match name_part.as_str() {
            "Num" => {
                let var_part = parts.next().unwrap();
                assert_eq!(var_part.as_rule(), Rule::lc_ident);
                let var_pos = position_from_span(&var_part.as_span());
                if let Some(_) = parts.peek() {
                    let pos = position_from_span(&parts.next().unwrap().as_span());
                    return Err(Error::new(ErrorCause::TooManyArguments, pos))
                }
                let var_index = tva.allocate_type_var(var_part.as_str())
                    .map_err(|c| Error::new(c, var_pos))?;
                tva.add_constraint(TypeConstraint::new_num(
                    &TypeExpression::Var(var_index),
                    &pos));
            }
            _ => return Err(Error::new(ErrorCause::UnknownConstraint(name_part.as_str().to_owned()), name_pos))
        }
    }
    Ok(())
}

fn parse_type_definition(mut inner: Pairs<Rule>)
        -> Result<SumType, Error> {
    // uc_ident ~ type_def_param_idents ~ type_sum_spec
    let name_pair = inner.next().unwrap();
    assert_eq!(name_pair.as_rule(), Rule::uc_ident);
    let name_pos = position_from_span(&name_pair.as_span());
    let name = name_pair.as_str();

    let mut tva = TypeVarAllocator::new();
    let params_pair = inner.next().unwrap();
    assert_eq!(params_pair.as_rule(), Rule::type_def_param_idents);
    let new_type = {
        let mut new_type = TypeExpression::Atomic(AtomicType::User(name.to_string()));
        for param_pair in params_pair.into_inner() {
            assert_eq!(param_pair.as_rule(), Rule::lc_ident);
            let param_pos = position_from_span(&param_pair.as_span());
            let param_name = param_pair.as_str();
            let param_index = tva.allocate_type_var(param_name).map_err(|c| Error::new(c, param_pos))?;
            new_type = TypeExpression::Composite(
                Box::new(new_type),
                Box::new(TypeExpression::Var(param_index)));
        }
        new_type
    };
    tva.disallow_new_vars();
    let mut type_constructors: Vec<TypeConstructor> = Vec::new();
    // tc = type constructor
    let mut tc_names: HashSet<String> = HashSet::new();
    let sum_pair = inner.next().unwrap();
    assert_eq!(sum_pair.as_rule(), Rule::type_sum_spec);
    for product_pair in sum_pair.into_inner() {
        assert_eq!(product_pair.as_rule(), Rule::type_product_spec);
        // let product_pos = position_from_span(&product_pair.as_span());
        let mut product_pair_inner = product_pair.into_inner();
        let tc_pair = product_pair_inner.next().unwrap();
        assert_eq!(tc_pair.as_rule(), Rule::uc_ident);
        let tc_pos = position_from_span(&tc_pair.as_span());
        let tc_name = tc_pair.as_str().to_string();
        let mut fn_vec: Vec<TypeExpression> = Vec::new();
        for tc_param_pair in product_pair_inner {
            assert_eq!(tc_param_pair.as_rule(), Rule::terminal_type);
            let tc_param_type = parse_type(tc_param_pair, &mut tva)?;
            fn_vec.push(tc_param_type);
        }
        if tc_names.contains(&tc_name) {
            return Err(Error::new(ErrorCause::Redefinition(tc_name), tc_pos))
        } else {
            tc_names.insert(String::clone(&tc_name));
            fn_vec.push(TypeExpression::clone(&new_type));
            let tc = TypeConstructor::new(
                tc_name,
                TypeExpression::new_function_from_vec(fn_vec),
                tva.get_type_vars(),
                tc_pos);
            type_constructors.push(tc);
        }
    }
    Ok(SumType::new(name.to_string(), tva.get_arity(), type_constructors, name_pos))
}
