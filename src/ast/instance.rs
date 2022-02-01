use std::fmt::Formatter;
use super::{concrete_type::ConcreteType, ast::Function, function_header::FunctionHeader};
use std::fmt::{self, Write};

#[derive(Debug, Clone, PartialEq)]
pub enum MangledId {
    Local(String),
    Global(String, Vec<ConcreteType>),
    Builtin(String, Vec<ConcreteType>),
    Auto(u64),
}

pub struct Instance {
    functions: Vec<Function<ConcreteType, MangledId>>,
    builtins: Vec<FunctionHeader<ConcreteType, MangledId>>,
}

impl MangledId {
    pub fn new_auto() -> Self {
        Self::Auto(rand::random())
    }
}

impl Instance {
    pub(super) fn new() -> Self {
        Self {
            functions: Vec::new(),
            builtins: Vec::new(),
        }
    }

    pub(super) fn push_function(&mut self, fun: Function<ConcreteType, MangledId>) {
        self.functions.push(fun);
    }

    pub(super) fn push_builtin(&mut self, fun: FunctionHeader<ConcreteType, MangledId>) {
        self.builtins.push(fun);
    }
}

impl fmt::Display for MangledId {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        use MangledId::*;
        match self {
            Local(s) => f.write_str(s),
            Global(s, ts) => {
                f.write_str(s)?;
                for t in ts.iter() {
                    f.write_char('_')?;
                    f.write_str(&t.as_short_string())?;
                }
                Ok(())
            }
            Builtin(s, ts) => {
                f.write_str(s)?;
                for t in ts.iter() {
                    f.write_char('_')?;
                    f.write_str(&t.as_short_string())?;
                }
                Ok(())
            }
            Auto(n) => write!(f, "auto_{n:016X}"),
        }
    }
}

impl fmt::Display for Instance {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "instance:")?;
        for bi in self.builtins.iter() {
            write!(f, "\t{}", bi.name)?;
        }
        for fun in self.functions.iter() {
            write!(f, "\t{}", fun)?;
        }
        Ok(())
    }
}
