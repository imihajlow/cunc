use crate::ast::MaybeTypedExpression;
use crate::ast::Module;
use crate::error::ErrorCause;
use crate::graph::Graph;
use crate::position::Position;
use crate::type_context::TypeContext;
use std::collections::HashMap;
use std::collections::HashSet;
use std::fmt;
use std::cmp;


use crate::ast::TypedExpression;

use crate::type_info::TypeExpression;

use crate::util::var_from_number;
use crate::{ast::{UntypedExpression}};


struct Solver {
    rules: Vec<Vec<TypeExpression>>
}

#[derive(Debug)]
struct SolveError(usize, ErrorCause);

impl Solver {
    fn new() -> Self {
        Self {
            rules: Vec::new()
        }
    }

    fn add_rule(&mut self, var_index: usize, t: TypeExpression) {
        if self.rules.len() <= var_index {
            self.rules.resize(var_index + 1, Vec::new());
        }
        self.rules[var_index].push(t);
    }

    fn solve(mut self) -> Result<Solution, SolveError> {
        assert!(self.rules.len() > 0);
        let mut to_process: Vec<usize> = (0..self.rules.len()).collect();
        while !to_process.is_empty() {
            println!("{}\n", &self);
            let current_var = to_process.pop().unwrap();
            if !self.rules[current_var].is_empty() {
                let current_rules = &mut self.rules[current_var];
                let rest = current_rules.split_off(1);
                let pivot_rule = TypeExpression::clone(current_rules.first().unwrap());
                let mut new_rules: Vec<(usize, TypeExpression)> = Vec::new();
                for rule in rest.into_iter() {
                    new_rules.extend(match_rules(&pivot_rule, &rule).map_err(|e| SolveError(current_var, e))?);
                }
                for rules in self.rules.iter_mut() {
                    for rule in rules.iter_mut() {
                        substitute(current_var, &pivot_rule, rule)
                    }
                }
                let mut affected_vars: HashSet<usize> = HashSet::new();
                for (var, t) in new_rules.into_iter() {
                    affected_vars.insert(var);
                    self.add_rule(var, t)
                }
                for var in affected_vars {
                    to_process.push(var);
                }
            }
        }
        let max_var_index = {
            let mut max_var_index: Option<usize> = Some(self.rules.len() - 1);
            for rules in self.rules.iter() {
                for rule in rules.iter() {
                    max_var_index = max_options(max_var_index, get_max_var_index(rule))
                }
            }
            max_var_index.unwrap()
        };
        let mut free_vars: HashSet<usize> = HashSet::new();
        for i in 0..=max_var_index {
            if i >= self.rules.len() || self.rules[i].is_empty() {
                free_vars.insert(i);
            }
        }

        println!("Finally:\n===========\n{}", &self);
        println!("max_var_index = {}", max_var_index);
        println!("free vars: {:?}", &free_vars);
        let mut free_var_mapping: HashMap<usize, usize> = HashMap::new();
        for (i, n) in free_vars.into_iter().enumerate() {
            free_var_mapping.insert(n, i);
        }

        let mut solution_rules: Vec<TypeExpression> = Vec::new();
        for i in 0..=max_var_index {
            use TypeExpression::*;
            if i >= self.rules.len() || self.rules[i].is_empty() {
                solution_rules.push(Var(free_var_mapping[&i]));
            } else {
                assert!(self.rules[i].len() == 1);
                let rule = self.rules[i].pop().unwrap();
                solution_rules.push(rename_vars(&free_var_mapping, rule));
            }
        }

        Ok(Solution::new(solution_rules, free_var_mapping.len()))
    }
}

impl fmt::Display for Solver {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (v, rules) in self.rules.iter().enumerate() {
            for t in rules.iter() {
                writeln!(f, "{} = {}", var_from_number(v), t)?;
            }
        }
        Ok(())
    }
}

fn max_options<T>(a: Option<T>, b: Option<T>) -> Option<T>
    where T: Ord + Copy {
    match (a, b) {
        (Some(x), Some(y)) => Some(cmp::max(x, y)),
        (Some(x), None) => Some(x),
        (None, Some(y)) => Some(y),
        _ => None
    }       
}

/// Find maximum variable index in a type expression. Returns None if expression contains no variables.
fn get_max_var_index(e: &TypeExpression) -> Option<usize> {
    use TypeExpression::*;
    match e {
        Var(n) => Some(*n),
        AtomicType(_) => None,
        Function(v) =>
            v.iter()
                .map(get_max_var_index)
                .fold(None, max_options)
    }
}

/// Match two type expressions and produce new type rules resulting from their equality.
fn match_rules(pivot: &TypeExpression, other: &TypeExpression) -> Result<Vec<(usize, TypeExpression)>, ErrorCause> {
    use TypeExpression::*;
    match (pivot, other) {
        (Var(n), t) => {
            Ok(vec![(*n, TypeExpression::clone(t))])
        }
        (t, Var(n)) => {
            Ok(vec![(*n, TypeExpression::clone(t))])
        }
        (AtomicType(a), AtomicType(b)) => {
            if a == b {
                Ok(Vec::new())
            } else {
                Err(ErrorCause::TypesMismatch(TypeExpression::clone(pivot), TypeExpression::clone(other)))
            }
        }
        (AtomicType(_), Function(_)) => {
            Err(ErrorCause::TypesMismatch(TypeExpression::clone(pivot), TypeExpression::clone(other)))
        }
        (Function(_), AtomicType(_)) => {
            Err(ErrorCause::TypesMismatch(TypeExpression::clone(pivot), TypeExpression::clone(other)))
        }
        (Function(a), Function(b)) => {
            let common = if a.len() == b.len() {
                a.len()
            } else {
                std::cmp::min(a.len(), b.len()) - 1
            };
            let mut result: Vec<(usize, TypeExpression)> = Vec::new();
            for i in 0..common {
                result.extend(match_rules(&a[i], &b[i])?);
            }
            if common != a.len() {
                let (one, many) = if a.len() < b.len() {
                    (a.last().unwrap(), Function(b.split_at(common).1.to_vec()))
                } else {
                    (b.last().unwrap(), Function(a.split_at(common).1.to_vec()))
                };
                result.extend(match_rules(one, &many)?);
            }
            Ok(result)
        }
    }
}

/// Substitute variable with its value in a target type expression.
fn substitute(var_index: usize, value: &TypeExpression, target: &mut TypeExpression) {
    use TypeExpression::*;
    match target {
        AtomicType(_) => (),
        Var(n) if *n == var_index => *target = TypeExpression::clone(value),
        Var(_) => (),
        Function(v) => 
            v.iter_mut().for_each(|t| substitute(var_index, value, t))
    }
}

/// Rename free variables in a type expression using a mapping (old number -> new number).
fn rename_vars(mapping: &HashMap<usize, usize>, value: TypeExpression) -> TypeExpression {
    use TypeExpression::*;
    match value {
        AtomicType(_) => value,
        Var(n) => Var(mapping[&n]),
        Function(v) => 
            Function(v.into_iter().map(|p| rename_vars(mapping, p)).collect())
    }
}

struct Solution {
    rules: Vec<TypeExpression>,
    free_vars_count: usize,
}

impl Solution {
    fn new(rules: Vec<TypeExpression>, free_vars_count: usize) -> Self {
        Self {
            rules,
            free_vars_count
        }
    }

    fn translate_type(&self, t: TypeExpression) -> TypeExpression {
        use TypeExpression::*;
        match t {
            AtomicType(_) => t,
            Var(n) => TypeExpression::clone(&self.rules[n]),
            Function(v) => Function(v.into_iter().map(|x| self.translate_type(x)).collect())
        }
    }

    fn get_free_vars_count(&self) -> usize {
        self.free_vars_count
    }
}

pub fn deduce_types(m: Module<MaybeTypedExpression>, context: &TypeContext) -> Module<TypedExpression> {
    // 1. Build dependency graph

    todo!();
}

#[cfg(test)]
mod tests {
    use crate::type_info::{AtomicType, IntType, IntBits};

    use super::*;

    #[test]
    fn test_match_rules() {
        // atomic vs atomic
        {
            let a = TypeExpression::AtomicType(AtomicType::Void);
            let b = TypeExpression::AtomicType(AtomicType::Void);
            assert!(match_rules(&a, &b).is_ok());
        }
        {
            let a = TypeExpression::AtomicType(AtomicType::Void);
            let b = TypeExpression::AtomicType(AtomicType::Int(IntType::new(false, IntBits::B8)));
            assert!(match_rules(&a, &b).is_err());
        }
    }

    #[test]
    fn test_solve_free_vars() {
        let mut solver = Solver::new();
        /*
        sum :: x -> x -> x

        f[a] a[b] b[c] c[d] =
            let x[e] = sum[f] a[b] b[c]
            sum[f] x[e] c[d] -> g
        */
        
        use TypeExpression::*;
        solver.add_rule(0, Function(vec![Var(1), Var(2), Var(3), Var(7)]));
        solver.add_rule(5, Function(vec![Var(1), Var(2), Var(4)]));
        solver.add_rule(5, Function(vec![Var(8), Var(8), Var(8)]));
        solver.add_rule(6, Function(vec![Var(4), Var(3), Var(7)]));
        solver.add_rule(6, Function(vec![Var(9), Var(9), Var(9)]));
        let solution = solver.solve();
        assert!(solution.is_ok());
        assert!(solution.unwrap().get_free_vars_count() == 1);
    }

    #[test]
    fn test_solve_no_free_vars() {
        let mut solver = Solver::new();
        /*
        sum :: U8 -> U8 -> U8

        f[a] a[b] b[c] c[d] =
            let x[e] = sum[f] a[b] b[c]
            sum[f] x[e] c[d] -> g
        */
        use crate::type_info;
        use TypeExpression::*;
        solver.add_rule(0, Function(vec![Var(1), Var(2), Var(3), Var(7)]));
        solver.add_rule(5, Function(vec![Var(1), Var(2), Var(4)]));
        solver.add_rule(5, Function(vec![
            AtomicType(type_info::AtomicType::Int(IntType::new(false, IntBits::B8))),
            AtomicType(type_info::AtomicType::Int(IntType::new(false, IntBits::B8))),
            AtomicType(type_info::AtomicType::Int(IntType::new(false, IntBits::B8)))
            ]));
        solver.add_rule(6, Function(vec![Var(4), Var(3), Var(7)]));
        solver.add_rule(6, Function(vec![
            AtomicType(type_info::AtomicType::Int(IntType::new(false, IntBits::B8))),
            AtomicType(type_info::AtomicType::Int(IntType::new(false, IntBits::B8))),
            AtomicType(type_info::AtomicType::Int(IntType::new(false, IntBits::B8)))
            ]));
        let solution = solver.solve();
        assert!(solution.is_ok());
        assert!(solution.unwrap().get_free_vars_count() == 0);
    }
}
