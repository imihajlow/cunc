use std::fmt::Formatter;
use super::concrete_type::ConcreteType;
use std::fmt::{self, Write};

#[derive(Debug, Clone, PartialEq)]
pub(super) enum MangledId {
    Local(String),
    Global(String, Vec<ConcreteType>),
    Auto(u64),
}

impl MangledId {
    pub(super) fn new_auto() -> Self {
        Self::Auto(rand::random())
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
            Auto(n) => write!(f, "auto_{n:016X}"),
        }
    }
}
