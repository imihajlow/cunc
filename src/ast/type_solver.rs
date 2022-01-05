use crate::error::Error;
use crate::error::ErrorCause;
use crate::error::Mismatchable;
use crate::position::Position;
use super::type_info::{CompositeExpression, TypeExpression};
use super::type_var_allocator::TypeVarAllocator;
use crate::util::max_options;
use crate::util::var_from_number;
use std::collections::HashMap;
use std::collections::HashSet;
use std::fmt;

pub(super) struct Solver<AT> {
    rules: Vec<Vec<CompositeExpression<AT>>>,
    verbose: bool,
}

#[derive(Debug)]
pub(super) enum SolveError {
    RuleError(usize, ErrorCause),
}

impl SolveError {
    pub(super) fn as_error(self, allocator: &TypeVarAllocator) -> Error {
        match self {
            Self::RuleError(n, c) => Error::new(c, Position::clone(allocator.get_position(n))),
        }
    }
}

impl<AT: Clone + PartialEq> Solver<AT>
where
    CompositeExpression<AT>: Mismatchable,
    AT: fmt::Display,
    CompositeExpression<AT>: fmt::Display,
{
    pub fn new() -> Self {
        Self {
            rules: Vec::new(),
            verbose: false,
        }
    }

    pub fn new_verbose() -> Self {
        Self {
            rules: Vec::new(),
            verbose: true,
        }
    }

    pub fn add_rule(&mut self, var_index: usize, t: CompositeExpression<AT>) {
        if self.rules.len() <= var_index {
            self.rules.resize(var_index + 1, Vec::new());
        }
        self.rules[var_index].push(t);
    }

    pub fn solve(mut self) -> Result<Solution<AT>, SolveError> {
        assert!(self.rules.len() > 0);
        let mut to_process: Vec<usize> = (0..self.rules.len()).collect();
        if self.verbose {
            println!("Type solver\n========");
        }
        while !to_process.is_empty() {
            if self.verbose {
                println!("{}\n", &self);
            }
            let current_var = to_process.pop().unwrap();
            let current_rules = &mut self.rules[current_var];
            // Delete rules like "x = x"
            current_rules.retain(|rule| rule != &CompositeExpression::Var(current_var));
            if !current_rules.is_empty() {
                // If there are multiple rules for once variable,
                // match them together to produce new rules,
                // removing all original rules but one.
                let rest = current_rules.split_off(1);
                let pivot_rule = CompositeExpression::clone(current_rules.first().unwrap());
                let mut new_rules: Vec<(usize, CompositeExpression<AT>)> = Vec::new();
                for rule in rest.into_iter() {
                    let matched_rules = match_rules(&pivot_rule, &rule)
                        .map_err(|e| SolveError::RuleError(current_var, e))?;
                    new_rules.extend(matched_rules);
                }

                // Substitute all occurences of the variable with its only rule
                for rules in self.rules.iter_mut() {
                    for rule in rules.iter_mut() {
                        rule.substitute(current_var, &pivot_rule)
                    }
                }

                // If there were new rules, mark corresponding variables for processing
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
                    max_var_index = max_options(max_var_index, rule.get_max_var_index())
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

        if self.verbose {
            println!("Finally:\n===========\n{}", &self);
            println!("max_var_index = {}", max_var_index);
            println!("free vars: {:?}", &free_vars);
        }
        let mut free_var_mapping: HashMap<usize, usize> = HashMap::new();
        for (i, n) in free_vars.into_iter().enumerate() {
            free_var_mapping.insert(n, i);
        }

        let mut solution_rules: Vec<CompositeExpression<AT>> = Vec::new();
        for i in 0..=max_var_index {
            use CompositeExpression::*;
            if i >= self.rules.len() || self.rules[i].is_empty() {
                solution_rules.push(Var(free_var_mapping[&i]));
            } else {
                assert!(self.rules[i].len() == 1);
                let rule = self.rules[i].pop().unwrap();
                solution_rules.push(rule.rename_vars(&free_var_mapping));
            }
        }

        Ok(Solution::new(solution_rules, free_var_mapping.len()))
    }
}

impl<AT: fmt::Display> fmt::Display for Solver<AT>
where
    CompositeExpression<AT>: std::fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (v, rules) in self.rules.iter().enumerate() {
            for t in rules.iter() {
                writeln!(f, "{} = {}", var_from_number(v), t)?;
            }
        }

        Ok(())
    }
}

/// Match two type expressions and produce new type rules resulting from their equality.
fn match_rules<AT: PartialEq + Clone>(
    pivot: &CompositeExpression<AT>,
    other: &CompositeExpression<AT>,
) -> Result<Vec<(usize, CompositeExpression<AT>)>, ErrorCause>
where
    CompositeExpression<AT>: Mismatchable,
{
    use CompositeExpression::*;
    match (pivot, other) {
        (Var(n), Var(m)) if n == m => Ok(Vec::new()),
        (Var(n), t) => Ok(vec![(*n, CompositeExpression::clone(&t))]),
        (t, Var(n)) => Ok(vec![(*n, CompositeExpression::clone(&t))]),
        (Atomic(a), Atomic(b)) => {
            if a == b {
                Ok(Vec::new())
            } else {
                Err(pivot.new_types_mismatch_error(other))
            }
        }
        (Atomic(_), Composite(_, _)) => Err(pivot.new_types_mismatch_error(other)),
        (Composite(_, _), Atomic(_)) => Err(pivot.new_types_mismatch_error(other)),
        (Composite(h1, t1), Composite(h2, t2)) => {
            let mut result = match_rules(h1, h2)?;
            result.extend(match_rules(t1, t2)?);
            Ok(result)
        }
    }
}

pub(super) struct Solution<AT> {
    rules: Vec<CompositeExpression<AT>>,
    free_vars_count: usize,
}

impl<AT: Clone> Solution<AT> {
    fn new(rules: Vec<CompositeExpression<AT>>, free_vars_count: usize) -> Self {
        Self {
            rules,
            free_vars_count,
        }
    }

    pub fn translate_type(&self, t: CompositeExpression<AT>) -> CompositeExpression<AT> {
        use CompositeExpression::*;
        match t {
            Atomic(_) => t,
            Var(n) => CompositeExpression::clone(&self.rules[n]),
            Composite(h, t) => Composite(
                Box::new(self.translate_type(*h)),
                Box::new(self.translate_type(*t)),
            ),
        }
    }

    pub fn translate_var_index(&self, index: usize) -> CompositeExpression<AT> {
        CompositeExpression::clone(&self.rules[index])
    }

    pub fn get_free_vars_count(&self) -> usize {
        self.free_vars_count
    }
}

impl<AT: fmt::Display> fmt::Display for Solution<AT>
where
    CompositeExpression<AT>: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (v, rule) in self.rules.iter().enumerate() {
            writeln!(f, "{} = {}", var_from_number(v), rule)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::super::type_info::{AtomicType, IntBits, IntType};

    use super::*;

    #[test]
    fn test_match_rules() {
        // atomic vs atomic
        {
            let a = CompositeExpression::Atomic(AtomicType::Int(IntType::new(false, IntBits::B8)));
            let b = CompositeExpression::Atomic(AtomicType::Int(IntType::new(false, IntBits::B8)));
            assert!(match_rules(&a, &b).is_ok());
        }
        {
            let a = CompositeExpression::Atomic(AtomicType::Int(IntType::new(false, IntBits::B16)));
            let b = CompositeExpression::Atomic(AtomicType::Int(IntType::new(false, IntBits::B8)));
            assert!(match_rules(&a, &b).is_err());
        }
    }

    #[test]
    fn test_solve_free_vars() {
        let mut solver: Solver<AtomicType> = Solver::new();
        /*
        sum :: x -> x -> x

        f[a] a[b] b[c] c[d] =
            let x[e] = sum[f] a[b] b[c]
            sum[f] x[e] c[d] -> g
        */

        use CompositeExpression::*;
        // 0 = 1 -> 2 -> 3 -> 7
        solver.add_rule(
            0,
            TypeExpression::new_function(
                Var(1),
                TypeExpression::new_function(Var(2), TypeExpression::new_function(Var(3), Var(7))),
            ),
        );
        // 5 = 1 -> 2 -> 4
        solver.add_rule(
            5,
            TypeExpression::new_function(Var(1), TypeExpression::new_function(Var(2), Var(4))),
        );
        // 5 = 8 -> 8 -> 8
        solver.add_rule(
            5,
            TypeExpression::new_function(Var(8), TypeExpression::new_function(Var(8), Var(8))),
        );
        // 6 = 4 -> 3 -> 7
        solver.add_rule(
            6,
            TypeExpression::new_function(Var(4), TypeExpression::new_function(Var(3), Var(7))),
        );
        // 6 = 9 -> 9 -> 9
        solver.add_rule(
            6,
            TypeExpression::new_function(Var(9), TypeExpression::new_function(Var(9), Var(9))),
        );
        let solution = solver.solve();
        assert!(solution.is_ok());
        assert!(solution.unwrap().get_free_vars_count() == 1);
    }

    #[test]
    fn test_solve_no_free_vars() {
        let mut solver: Solver<AtomicType> = Solver::new();
        /*
        sum :: U8 -> U8 -> U8

        f[a] a[b] b[c] c[d] =
            let x[e] = sum[f] a[b] b[c]
            sum[f] x[e] c[d] -> g
        */
        use super::super::type_info;
        use CompositeExpression::*;
        // 0 = 1 -> 2 -> 3 -> 7
        solver.add_rule(
            0,
            TypeExpression::new_function(
                Var(1),
                TypeExpression::new_function(Var(2), TypeExpression::new_function(Var(3), Var(7))),
            ),
        );
        // 5 = 1 -> 2 -> 4
        solver.add_rule(
            5,
            TypeExpression::new_function(Var(1), TypeExpression::new_function(Var(2), Var(4))),
        );
        // 5 = U8 -> U8 -> U8
        solver.add_rule(
            5,
            TypeExpression::new_function(
                Atomic(type_info::AtomicType::Int(IntType::new(false, IntBits::B8))),
                TypeExpression::new_function(
                    Atomic(type_info::AtomicType::Int(IntType::new(false, IntBits::B8))),
                    Atomic(type_info::AtomicType::Int(IntType::new(false, IntBits::B8))),
                ),
            ),
        );
        // 6 = 4 -> 3 -> 7
        solver.add_rule(
            6,
            TypeExpression::new_function(Var(4), TypeExpression::new_function(Var(3), Var(7))),
        );
        // 6 = U8 -> U8 -> U8
        solver.add_rule(
            6,
            TypeExpression::new_function(
                Atomic(type_info::AtomicType::Int(IntType::new(false, IntBits::B8))),
                TypeExpression::new_function(
                    Atomic(type_info::AtomicType::Int(IntType::new(false, IntBits::B8))),
                    Atomic(type_info::AtomicType::Int(IntType::new(false, IntBits::B8))),
                ),
            ),
        );
        let solution = solver.solve();
        assert!(solution.is_ok());
        assert!(solution.unwrap().get_free_vars_count() == 0);
    }
}
