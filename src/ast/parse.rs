use super::ast::*;
use super::type_info::TypeVars;
use super::type_info::{AtomicType, TypeExpression};
use crate::error::Error;
use crate::error::ErrorCause;
use crate::position::{position_from_linecol, position_from_span, Position};
use itertools::Itertools;
use pest::iterators::Pair;
use pest::iterators::Pairs;
use pest::prec_climber::Assoc;
use pest::prec_climber::Operator;
use pest::prec_climber::PrecClimber;
use pest::Parser;
use std::collections::HashMap;
use std::collections::HashSet;

#[derive(Parser)]
#[grammar = "cunc.pest"]
pub struct CuncParser;

type TcMap = HashMap<String, TypeConstructor>;

pub(super) fn parse_file(fname: &str) -> Result<Module<OptionalType>, Error> {
    let code = std::fs::read_to_string(&fname).unwrap();
    parse_str(&code)
}

pub(super) fn parse_str(code: &str) -> Result<Module<OptionalType>, Error> {
    let root = match CuncParser::parse(Rule::main, &code) {
        Ok(ast) => ast,
        Err(e) => {
            return Err(Error::new(
                ErrorCause::SyntaxError(e.to_string()),
                position_from_linecol(e.line_col),
            ));
        }
    };
    // println!("{}", &root);

    let mut result: Module<OptionalType> = Module::new();
    let mut tc_map: TcMap = HashMap::new();
    for node in root.into_iter() {
        match node.as_rule() {
            Rule::fn_decl => {
                let fun = parse_function(node, &tc_map)?;
                result.push_function(fun);
            }
            Rule::type_def => {
                let t = parse_type_definition(node.into_inner(), &mut tc_map)?;
                result.push_type(t);
            }
            Rule::EOI => (),
            _ => unreachable!(),
        }
    }

    Ok(result)
}

#[derive(Debug)]
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

    fn into_type_vars(self) -> TypeVars {
        TypeVars::new(self.cur_index)
    }

    fn get_type_vars(&self) -> TypeVars {
        TypeVars::new(self.cur_index)
    }

    fn get_arity(&self) -> usize {
        self.cur_index
    }
}

fn parse_function(pair: Pair<Rule>, tc_map: &TcMap) -> Result<Function<OptionalType>, Error> {
    // pair: fn_decl
    // type_spec? ~ fn_idents ~ fn_body
    let pos = position_from_span(&pair.as_span());
    let mut inner = pair.into_inner();
    let mut tva = TypeVarAllocator::new();
    let (type_spec, name, param_idents) = {
        let p = inner.next().unwrap();
        match p.as_rule() {
            Rule::type_spec => (
                Some(parse_type_spec(p, &mut tva)?),
                inner.next().unwrap().as_str(),
                inner.next().unwrap(),
            ),
            Rule::lc_ident => (None, p.as_str(), inner.next().unwrap()),
            _ => unreachable!(),
        }
    };
    let (fn_type, context) = match type_spec {
        Some((t, context)) => (Some(t), context),
        None => (None, ConstraintContext::new()),
    };
    tva.disallow_new_vars();
    let body_pair = inner.next().unwrap();
    let body_expr = parse_expression(body_pair, &mut tva, tc_map)?;
    let body = build_lambda(param_idents.into_inner(), fn_type, body_expr)?;
    Ok(Function::new(
        name.to_string(),
        context,
        body,
        tva.into_type_vars(),
        pos,
    ))
}

fn substitute_return_type(
    body: Expression<OptionalType>,
    rt: Option<TypeExpression>,
) -> Result<Expression<OptionalType>, Error> {
    match (&body.t.0, rt) {
        (None, None) => Ok(body),
        (Some(_), None) => Ok(body),
        (None, Some(t)) => Ok(Expression::<OptionalType>::new(body.e, body.p, Some(t))),
        (Some(_), Some(_)) => Err(Error::new(ErrorCause::MultipleTypeSpecification, body.p)),
    }
}

/// Build maybe nested lambda expression from a list of params, type and body.
fn build_lambda(
    mut param_idents: Pairs<Rule>,
    types: Option<TypeExpression>,
    body: Expression<OptionalType>,
) -> Result<Expression<OptionalType>, Error> {
    match param_idents.next() {
        None => substitute_return_type(body, types),
        Some(p) if p.as_str().len() == 0 => substitute_return_type(body, types),
        Some(p) => {
            let param_pos = position_from_span(&p.as_span());
            let param_name = p.as_str().to_string();
            // It's at least a function with one argument.
            // If a type is specified, it must be a function type.
            let (param_type, rest_types) = if let Some(t) = types {
                if let Some((a, b)) = t.match_function() {
                    (
                        Some(TypeExpression::clone(a)),
                        Some(TypeExpression::clone(b)),
                    )
                } else {
                    return Err(Error::new(ErrorCause::TooManyArguments, param_pos));
                }
            } else {
                (None, None)
            };
            let binding: Binding<OptionalType> = Binding::new(
                param_name,
                OptionalType(param_type),
                Position::clone(&param_pos),
            );
            let inner_expression = build_lambda(param_idents, rest_types, body)?;
            let my_position = param_pos.merge(&inner_expression.p);
            let lambda: Lambda<OptionalType> = Lambda::new(
                binding,
                OptionalType(None),
                inner_expression,
                Position::clone(&my_position),
            );
            let abstraction: ExpressionVariant<OptionalType> =
                ExpressionVariant::Abstraction(lambda);
            Ok(Expression::<OptionalType>::new(
                abstraction,
                my_position,
                None,
            ))
        }
    }
}

fn parse_expression(
    pair: Pair<Rule>,
    tva: &mut TypeVarAllocator,
    tc_map: &TcMap,
) -> Result<Expression<OptionalType>, Error> {
    let pos = position_from_span(&pair.as_span());
    match pair.as_rule() {
        Rule::expression => parse_expression(pair.into_inner().next().unwrap(), tva, tc_map),
        Rule::application => {
            let mut collected_expr: Option<Expression<OptionalType>> = None;
            for part in pair.into_inner() {
                let part_position = position_from_span(&part.as_span());
                let parsed_part: Expression<OptionalType> =
                    if let Rule::op_expression = part.as_rule() {
                        parse_expression(part, tva, tc_map)?
                    } else {
                        let parsed_part = match part.as_rule() {
                            Rule::lc_ident | Rule::uc_ident => {
                                ExpressionVariant::Variable(part.as_str().to_string())
                            }
                            Rule::dec_constant => {
                                ExpressionVariant::IntConstant(parse_dec_constant(part)?)
                            }
                            Rule::hex_constant => {
                                ExpressionVariant::IntConstant(parse_hex_constant(part)?)
                            }
                            Rule::bin_constant => {
                                ExpressionVariant::IntConstant(parse_bin_constant(part)?)
                            }
                            _ => unreachable!("{}", part),
                        };
                        Expression::<OptionalType>::new(parsed_part, part_position, None)
                    };
                collected_expr = match collected_expr {
                    None => Some(parsed_part),
                    Some(e) => Some(Expression::new_application(e, parsed_part)),
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
                        assert!(e_pair.as_rule() == Rule::op_expression);
                        (
                            Some(parse_type(next, tva)?),
                            parse_expression(e_pair, tva, tc_map)?,
                        )
                    }
                    Rule::op_expression => (None, parse_expression(next, tva, tc_map)?),
                    _ => unreachable!(),
                }
            };
            let body_pair = inner.next().unwrap();
            assert!(body_pair.as_rule() == Rule::op_expression);
            let body = parse_expression(body_pair, tva, tc_map)?;
            let binding: Binding<OptionalType> =
                Binding::new(name, OptionalType(var_type_spec), name_pos);
            let ev = ExpressionVariant::Let(binding, Box::new(value), Box::new(body));
            Ok(Expression::<OptionalType>::new(ev, pos, None))
        }
        Rule::pmatch => {
            let mut inner = pair.into_inner();
            let expr_pair = inner.next().unwrap();
            let expr = parse_expression(expr_pair, tva, tc_map)?;
            let mut cases: Vec<Case<OptionalType>> = Vec::new();
            for p in inner {
                cases.push(parse_case(p, tva, tc_map)?);
            }
            let ev = ExpressionVariant::Pmatch(Box::new(expr), cases);
            Ok(Expression::<OptionalType>::new(ev, pos, None))
        }
        Rule::op_expression => {
            let climber = PrecClimber::new(vec![
                Operator::new(Rule::op_add, Assoc::Left) | Operator::new(Rule::op_sub, Assoc::Left),
                Operator::new(Rule::op_mul, Assoc::Left)
                    | Operator::new(Rule::op_div, Assoc::Left)
                    | Operator::new(Rule::op_mod, Assoc::Left),
            ]);
            let primary = |p| parse_expression(p, tva, tc_map);
            let infix = |lhs: Result<Expression<OptionalType>, Error>,
                         op: Pair<Rule>,
                         rhs: Result<Expression<OptionalType>, Error>|
             -> Result<Expression<OptionalType>, Error> {
                let lhs_ok = lhs?;
                let rhs_ok = rhs?;
                let op_name = match op.as_rule() {
                    Rule::op_add => "__add__",
                    Rule::op_sub => "__sub__",
                    Rule::op_mul => "__mul__",
                    Rule::op_div => "__div__",
                    Rule::op_mod => "__mod__",
                    _ => unreachable!(),
                };
                let op_ev = ExpressionVariant::<OptionalType>::Variable(op_name.to_string());
                let op_pos = position_from_span(&op.as_span());
                let op_expr = Expression::<OptionalType>::new(op_ev, op_pos, None);
                let op = Expression::new_application(
                    Expression::new_application(op_expr, lhs_ok),
                    rhs_ok,
                );
                Ok(op)
            };
            climber.climb(pair.into_inner(), primary, infix)
        }
        _ => unreachable!(),
    }
}

fn parse_case(
    pair: Pair<Rule>,
    tva: &mut TypeVarAllocator,
    tc_map: &TcMap,
) -> Result<Case<OptionalType>, Error> {
    assert_eq!(pair.as_rule(), Rule::case);
    let mut inner = pair.into_inner();
    let pattern_p = inner.next().unwrap();
    assert_eq!(pattern_p.as_rule(), Rule::pattern);
    let pattern_pos = position_from_span(&pattern_p.as_span());
    let mut pattern_inner = pattern_p.into_inner();
    let tc_p = pattern_inner.next().unwrap();
    let tc_pos = position_from_span(&tc_p.as_span());
    let tc_name = tc_p.as_str();
    let tc = match tc_map.get(tc_name) {
        Some(tc) => tc,
        None => {
            return Err(Error::new(
                ErrorCause::TypeConstructorNotFound(tc_name.to_owned()),
                tc_pos,
            ))
        }
    };
    let tc_params: Vec<_> = pattern_inner
        .map(|p| {
            let param_pos = position_from_span(&p.as_span());
            Binding::<OptionalType>::new(p.as_str().to_owned(), OptionalType(None), param_pos)
        })
        .collect();
    let body_p = inner.next().unwrap();
    assert_eq!(body_p.as_rule(), Rule::op_expression);
    let body = parse_expression(body_p, tva, tc_map)?;

    Ok(Case::<OptionalType>::new(
        TypeConstructor::clone(&tc),
        tc_params,
        body,
        pattern_pos,
    ))
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

fn parse_type_spec(
    pair: Pair<Rule>,
    tva: &mut TypeVarAllocator,
) -> Result<(TypeExpression, ConstraintContext<OptionalType>), Error> {
    assert_eq!(pair.as_rule(), Rule::type_spec);
    let mut inner = pair.into_inner();
    let first = inner.next().unwrap();
    if let Rule::arrow_type = first.as_rule() {
        Ok((parse_type(first, tva)?, ConstraintContext::new()))
    } else {
        assert_eq!(first.as_rule(), Rule::context);
        let type_fn = inner.next().unwrap();
        assert_eq!(type_fn.as_rule(), Rule::arrow_type);
        Ok((parse_type(type_fn, tva)?, parse_context(first, tva)?))
    }
}

fn parse_context(
    pair: Pair<Rule>,
    tva: &mut TypeVarAllocator,
) -> Result<ConstraintContext<OptionalType>, Error> {
    assert_eq!(pair.as_rule(), Rule::context);
    let mut result: ConstraintContext<OptionalType> = ConstraintContext::new();
    for p in pair.into_inner() {
        let pos = position_from_span(&p.as_span());
        let t = parse_type(p, tva)?;
        result.add(OptionalType(Some(t)), &pos);
    }
    Ok(result)
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
                None => None,
            };
            Ok(match tail {
                None => head,
                Some(t) => TypeExpression::new_function(head, t),
            })
        }
        Rule::application_type => {
            let mut inner = pair.into_inner();
            let first = parse_type(inner.next().unwrap(), tva)?;
            inner
                .map(|pair| parse_type(pair, tva))
                .fold_ok(first, |acc, t| {
                    TypeExpression::Composite(Box::new(acc), Box::new(t))
                })
        }
        Rule::terminal_type => {
            let mut inner = pair.into_inner();
            let unique_flag_p = inner.next().unwrap();
            assert_eq!(unique_flag_p.as_rule(), Rule::unique_flag);
            let t = parse_type(inner.next().unwrap(), tva)?;
            if unique_flag_p.as_str() == "*" {
                Ok(TypeExpression::new_unique(t))
            } else {
                Ok(t)
            }
        }
        Rule::uc_ident => {
            let at = pair.as_str().parse::<AtomicType>().map_err(|e| {
                Error::new(
                    ErrorCause::AtomicTypeParseError(e),
                    position_from_span(&pair.as_span()),
                )
            })?;
            Ok(TypeExpression::Atomic(at))
        }
        Rule::lc_ident => Ok(TypeExpression::Var(
            tva.allocate_type_var(pair.as_str())
                .map_err(|c| Error::new(c, position_from_span(&pair.as_span())))?,
        )),
        x => {
            println!("{:?}", x);
            unreachable!()
        }
    }
}

fn parse_type_definition(mut inner: Pairs<Rule>, tc_map: &mut TcMap) -> Result<SumType, Error> {
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
            let param_index = tva
                .allocate_type_var(param_name)
                .map_err(|c| Error::new(c, param_pos))?;
            new_type = TypeExpression::Composite(
                Box::new(new_type),
                Box::new(TypeExpression::Var(param_index)),
            );
        }
        new_type
    };
    tva.disallow_new_vars();
    let mut type_constructors: Vec<TypeConstructor> = Vec::new();
    // tc = type constructor
    let mut tc_names: HashSet<String> = HashSet::new();
    let sum_pair = inner.next().unwrap();
    assert_eq!(sum_pair.as_rule(), Rule::type_sum_spec);
    for (index, product_pair) in sum_pair.into_inner().enumerate() {
        assert_eq!(product_pair.as_rule(), Rule::type_product_spec);
        // let product_pos = position_from_span(&product_pair.as_span());
        let mut product_pair_inner = product_pair.into_inner();
        let tc_pair = product_pair_inner.next().unwrap();
        assert_eq!(tc_pair.as_rule(), Rule::uc_ident);
        let tc_pos = position_from_span(&tc_pair.as_span());
        let tc_name = tc_pair.as_str();
        let mut params: Vec<TypeExpression> = Vec::new();
        for tc_param_pair in product_pair_inner {
            assert_eq!(tc_param_pair.as_rule(), Rule::terminal_type);
            let tc_param_type = parse_type(tc_param_pair, &mut tva)?;
            params.push(tc_param_type);
        }
        if tc_names.contains(tc_name) {
            return Err(Error::new(
                ErrorCause::Redefinition(tc_name.to_owned()),
                tc_pos,
            ));
        } else {
            if tc_map.contains_key(tc_name) {
                return Err(Error::new(
                    ErrorCause::Redefinition(tc_name.to_owned()),
                    tc_pos,
                ));
            }
            tc_names.insert(tc_name.to_owned());
            let tc = TypeConstructor::new(
                tc_name.to_owned(),
                index,
                params,
                TypeExpression::clone(&new_type),
                tva.get_type_vars(),
                tc_pos,
            );
            tc_map.insert(tc_name.to_owned(), TypeConstructor::clone(&tc));
            type_constructors.push(tc);
        }
    }
    Ok(SumType::new(
        name.to_string(),
        tva.get_arity(),
        type_constructors,
        name_pos,
    ))
}

#[cfg(test)]
mod tests {
    use super::super::type_info::{CompositeExpression, TypeExpression};
    use super::*;

    #[test]
    fn test_fn_type1() {
        let code = "a -> b";
        let root = CuncParser::parse(Rule::arrow_type, &code)
            .unwrap()
            .next()
            .unwrap();
        let mut tva = TypeVarAllocator::new();
        let t = parse_type(root, &mut tva).unwrap();
        use CompositeExpression::*;
        let expected = TypeExpression::new_function(Var(0), Var(1));
        assert_eq!(t, expected);
    }

    #[test]
    fn test_fn_type2() {
        let code = "a -> b -> c -> d";
        let root = CuncParser::parse(Rule::arrow_type, &code)
            .unwrap()
            .next()
            .unwrap();
        let mut tva = TypeVarAllocator::new();
        let t = parse_type(root, &mut tva).unwrap();
        use CompositeExpression::*;
        let expected = TypeExpression::new_function(
            Var(0),
            TypeExpression::new_function(Var(1), TypeExpression::new_function(Var(2), Var(3))),
        );
        assert_eq!(t, expected);
    }

    #[test]
    fn test_fn_type3() {
        let code = "a -> (b -> c) -> d";
        let root = CuncParser::parse(Rule::arrow_type, &code)
            .unwrap()
            .next()
            .unwrap();
        let mut tva = TypeVarAllocator::new();
        let t = parse_type(root, &mut tva).unwrap();
        use CompositeExpression::*;
        let expected = TypeExpression::new_function(
            Var(0),
            TypeExpression::new_function(TypeExpression::new_function(Var(1), Var(2)), Var(3)),
        );
        assert_eq!(t, expected);
    }

    #[test]
    fn test_fn_type_def() {
        use CompositeExpression::*;
        let code = "data Toto a b = Mo (b a).";
        let root = CuncParser::parse(Rule::type_def, &code)
            .unwrap()
            .next()
            .unwrap();
        let mut tc_map: TcMap = HashMap::new();
        let t = parse_type_definition(root.into_inner(), &mut tc_map).unwrap();
        assert!(tc_map.contains_key("Mo"));
        assert_eq!(t.arity, 2);
        assert_eq!(t.name, "Toto");
        assert_eq!(t.constructors.len(), 1);
        let tc = t.constructors.last().unwrap();
        assert_eq!(tc.name, "Mo");
        assert_eq!(tc.enum_index, 0);
        let parent_type = &tc.parent_type;
        let parent_type_expected: TypeExpression = TypeExpression::new_composite(
            TypeExpression::new_composite(Atomic(AtomicType::User("Toto".to_string())), Var(0)),
            Var(1),
        );
        assert_eq!(parent_type, &parent_type_expected);
        assert_eq!(tc.params.len(), 1);
        assert_eq!(
            tc.params.last().unwrap(),
            &TypeExpression::new_composite(Var(1), Var(0))
        );
    }

    #[test]
    fn test_op_expr() {
        let code = "a + b * c - d";
        let root = CuncParser::parse(Rule::op_expression, &code)
            .unwrap() // Pairs
            .next()
            .unwrap(); // Pair
        let mut tva = TypeVarAllocator::new();
        tva.disallow_new_vars();
        let tc_map: TcMap = HashMap::new();
        let expr = parse_expression(root, &mut tva, &tc_map).unwrap();
        let mut lvl1 = expr.into_application_vec();
        assert_eq!(lvl1.len(), 3);
        assert_eq!(
            lvl1[0].e,
            ExpressionVariant::<OptionalType>::Variable("__sub__".to_string())
        );
        assert_eq!(
            lvl1[2].e,
            ExpressionVariant::<OptionalType>::Variable("d".to_string())
        );
        let mut lvl2 = lvl1.drain(1..2).next().unwrap().into_application_vec();
        assert_eq!(lvl2.len(), 3);
        assert_eq!(
            lvl2[0].e,
            ExpressionVariant::<OptionalType>::Variable("__add__".to_string())
        );
        assert_eq!(
            lvl2[1].e,
            ExpressionVariant::<OptionalType>::Variable("a".to_string())
        );
        let lvl3 = lvl2.drain(2..).next().unwrap().into_application_vec();
        assert_eq!(lvl3.len(), 3);
        assert_eq!(
            lvl3[0].e,
            ExpressionVariant::<OptionalType>::Variable("__mul__".to_string())
        );
        assert_eq!(
            lvl3[1].e,
            ExpressionVariant::<OptionalType>::Variable("b".to_string())
        );
        assert_eq!(
            lvl3[2].e,
            ExpressionVariant::<OptionalType>::Variable("c".to_string())
        );
    }
}
