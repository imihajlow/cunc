use crate::util::max_options;
use crate::position::Position;
use crate::error::Error;
use crate::error::ErrorCause;
use crate::type_constraint::TypeConstraint;
use crate::type_var_allocator::TypeVarAllocator;
use std::collections::HashMap;
use std::collections::HashSet;
use std::fmt;
use crate::type_info::TypeExpression;
use crate::util::var_from_number;
use itertools::Itertools;

pub struct Solver {
    rules: Vec<Vec<TypeExpression>>,
    constraints: Vec<TypeConstraint>
}

#[derive(Debug)]
pub enum SolveError {
    RuleError(usize, ErrorCause),
    ConstraintError(Error),
}

impl SolveError {
    pub fn as_error(self, allocator: &TypeVarAllocator) -> Error {
        match self {
            Self::RuleError(n, c) =>
                Error::new(c, Position::clone(allocator.get_position(n))),
            Self::ConstraintError(e) =>
                e
        }
    }
}

impl Solver {
    pub fn new() -> Self {
        Self {
            rules: Vec::new(),
            constraints: Vec::new(),
        }
    }

    pub fn add_rule(&mut self, var_index: usize, t: TypeExpression) {
        if self.rules.len() <= var_index {
            self.rules.resize(var_index + 1, Vec::new());
        }
        self.rules[var_index].push(t);
    }

    pub fn add_constraint(&mut self, c: TypeConstraint) {
        self.constraints.push(c);
    }

    pub fn solve(mut self) -> Result<Solution, SolveError> {
        assert!(self.rules.len() > 0);
        let mut to_process: Vec<usize> = (0..self.rules.len()).collect();
        // println!("Type solver\n========");
        while !to_process.is_empty() {
            // println!("{}\n", &self);
            let current_var = to_process.pop().unwrap();
            if !self.rules[current_var].is_empty() {
                // If there are multiple rules for once variable,
                // match them together to produce new rules,
                // removing all original rules but one.
                let current_rules = &mut self.rules[current_var];
                let rest = current_rules.split_off(1);
                let pivot_rule = TypeExpression::clone(current_rules.first().unwrap());
                let mut new_rules: Vec<(usize, TypeExpression)> = Vec::new();
                for rule in rest.into_iter() {
                    new_rules.extend(match_rules(&pivot_rule, &rule).map_err(|e| SolveError::RuleError(current_var, e))?);
                }

                // Substitute all occurences of the variable with its only rule
                for rules in self.rules.iter_mut() {
                    for rule in rules.iter_mut() {
                        rule.substitute(current_var, &pivot_rule)
                    }
                }
                for c in self.constraints.iter_mut() {
                    c.substitute(current_var, &pivot_rule);
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
            for constraint in self.constraints.iter() {
                max_var_index = max_options(max_var_index, constraint.get_max_var_index());
            }
            max_var_index.unwrap()
        };
        let mut free_vars: HashSet<usize> = HashSet::new();
        for i in 0..=max_var_index {
            if i >= self.rules.len() || self.rules[i].is_empty() {
                free_vars.insert(i);
            }
        }

        // println!("Finally:\n===========\n{}", &self);
        // println!("max_var_index = {}", max_var_index);
        // println!("free vars: {:?}", &free_vars);
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
                solution_rules.push(rule.rename_vars(&free_var_mapping));
            }
        }
        let mut checked_constraints: Vec<TypeConstraint> = Vec::new();
        for c in self.constraints.into_iter() {
            if let Some(c) = c.check().map_err(|e| SolveError::ConstraintError(e))? {
                checked_constraints.push(c);
            }
        }
        let merged_constraints =
            TypeConstraint::merge(checked_constraints).map_err(|e| SolveError::ConstraintError(e))?;
        let renamed_constraints =
            merged_constraints.into_iter().map(|c| c.rename_vars(&free_var_mapping)).collect();


        Ok(Solution::new(solution_rules, renamed_constraints, free_var_mapping.len()))
    }
}

impl fmt::Display for Solver {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if !self.constraints.is_empty() {
            for c in self.constraints.iter() {
                writeln!(f, "{}", c)?;
            }
            writeln!(f, "=>")?;
        }
        for (v, rules) in self.rules.iter().enumerate() {
            for t in rules.iter() {
                writeln!(f, "{} = {}", var_from_number(v), t)?;
            }
        }

        Ok(())
    }
}

/// Match two type expressions and produce new type rules resulting from their equality.
fn match_rules(pivot: &TypeExpression, other: &TypeExpression) -> Result<Vec<(usize, TypeExpression)>, ErrorCause> {
    use TypeExpression::*;
    match (pivot, other) {
        (Var(n), Var(m)) if n == m => {
            Ok(Vec::new())
        }
        (Var(n), t) => {
            Ok(vec![(*n, TypeExpression::clone(t))])
        }
        (t, Var(n)) => {
            Ok(vec![(*n, TypeExpression::clone(t))])
        }
        (Atomic(a), Atomic(b)) => {
            if a == b {
                Ok(Vec::new())
            } else {
                Err(ErrorCause::TypesMismatch(TypeExpression::clone(pivot), TypeExpression::clone(other)))
            }
        }
        (Atomic(_), Composite(_, _)) => {
            Err(ErrorCause::TypesMismatch(TypeExpression::clone(pivot), TypeExpression::clone(other)))
        }
        (Composite(_, _), Atomic(_)) => {
            Err(ErrorCause::TypesMismatch(TypeExpression::clone(pivot), TypeExpression::clone(other)))
        }
        (Composite(h1, t1), Composite(h2, t2)) => {
            let mut result = match_rules(h1, h2)?;
            result.extend(match_rules(t1, t2)?);
            Ok(result)
        }
    }
}

pub struct Solution {
    rules: Vec<TypeExpression>,
    constraints: Vec<TypeConstraint>,
    free_vars_count: usize,
}

impl Solution {
    fn new(rules: Vec<TypeExpression>, constraints: Vec<TypeConstraint>, free_vars_count: usize) -> Self {
        Self {
            rules,
            constraints,
            free_vars_count
        }
    }

    pub fn translate_type(&self, t: TypeExpression) -> TypeExpression {
        use TypeExpression::*;
        match t {
            Atomic(_) => t,
            Var(n) => TypeExpression::clone(&self.rules[n]),
            Composite(h, t) =>
                Composite(
                    Box::new(self.translate_type(*h)),
                    Box::new(self.translate_type(*t)))
        }
    }

    pub fn translate_var_index(&self, index: usize) -> TypeExpression {
        TypeExpression::clone(&self.rules[index])
    }

    pub fn get_free_vars_count(&self) -> usize {
        self.free_vars_count
    }

    pub fn clone_type_constraints(&self) -> Vec<TypeConstraint> {
        self.constraints.to_owned()
    }
}

impl fmt::Display for Solution {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if !self.constraints.is_empty() {
            for s in self.constraints.iter().map(|c| format!("{}", c)).intersperse(", ".to_string()) {
                f.write_str(&s)?;
            }
            f.write_str(" =>\n")?;
        }
        for (v, rule) in self.rules.iter().enumerate() {
            writeln!(f, "{} = {}", var_from_number(v), rule)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::type_info::{AtomicType, IntType, IntBits};

    use super::*;

    #[test]
    fn test_match_rules() {
        // atomic vs atomic
        {
            let a = TypeExpression::Atomic(AtomicType::Int(IntType::new(false, IntBits::B8)));
            let b = TypeExpression::Atomic(AtomicType::Int(IntType::new(false, IntBits::B8)));
            assert!(match_rules(&a, &b).is_ok());
        }
        {
            let a = TypeExpression::Atomic(AtomicType::Int(IntType::new(false, IntBits::B16)));
            let b = TypeExpression::Atomic(AtomicType::Int(IntType::new(false, IntBits::B8)));
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
        // 0 = 1 -> 2 -> 3 -> 7
        solver.add_rule(0, TypeExpression::new_function(
            Var(1),
            TypeExpression::new_function(
                Var(2),
                TypeExpression::new_function(
                    Var(3),
                    Var(7)))));
        // 5 = 1 -> 2 -> 4
        solver.add_rule(5, TypeExpression::new_function(
            Var(1),
            TypeExpression::new_function(
                Var(2),
                Var(4))));
        // 5 = 8 -> 8 -> 8
        solver.add_rule(5, TypeExpression::new_function(
            Var(8),
            TypeExpression::new_function(
                Var(8),
                Var(8))));
        // 6 = 4 -> 3 -> 7
        solver.add_rule(6, TypeExpression::new_function(
            Var(4),
            TypeExpression::new_function(
                Var(3),
                Var(7))));
        // 6 = 9 -> 9 -> 9
        solver.add_rule(6, TypeExpression::new_function(
            Var(9),
            TypeExpression::new_function(
                Var(9),
                Var(9))));
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
        // 0 = 1 -> 2 -> 3 -> 7
        solver.add_rule(0, TypeExpression::new_function(
            Var(1),
            TypeExpression::new_function(
                Var(2),
                TypeExpression::new_function(
                    Var(3),
                    Var(7)))));
        // 5 = 1 -> 2 -> 4
        solver.add_rule(5, TypeExpression::new_function(
            Var(1),
            TypeExpression::new_function(
                Var(2),
                Var(4))));
        // 5 = U8 -> U8 -> U8
        solver.add_rule(5, TypeExpression::new_function(
            Atomic(type_info::AtomicType::Int(IntType::new(false, IntBits::B8))),
            TypeExpression::new_function(
                Atomic(type_info::AtomicType::Int(IntType::new(false, IntBits::B8))),
                Atomic(type_info::AtomicType::Int(IntType::new(false, IntBits::B8))))));
        // 6 = 4 -> 3 -> 7
        solver.add_rule(6, TypeExpression::new_function(
            Var(4),
            TypeExpression::new_function(
                Var(3),
                Var(7))));
        // 6 = U8 -> U8 -> U8
        solver.add_rule(6, TypeExpression::new_function(
            Atomic(type_info::AtomicType::Int(IntType::new(false, IntBits::B8))),
            TypeExpression::new_function(
                Atomic(type_info::AtomicType::Int(IntType::new(false, IntBits::B8))),
                Atomic(type_info::AtomicType::Int(IntType::new(false, IntBits::B8))))));
        let solution = solver.solve();
        assert!(solution.is_ok());
        assert!(solution.unwrap().get_free_vars_count() == 0);
    }
}
