use std::collections::HashMap;

use crate::error::{ErrorCause};
use crate::type_info::CuncType;

pub struct TypeContext<'a> {
    parent: Option<&'a Self>,
    bindings: HashMap<String, CuncType>
}

impl<'a> TypeContext<'a> {
    pub fn new() -> Self {
        Self {
            parent: None,
            bindings: HashMap::new()
        }
    }

    pub fn push(&'a self) -> Self {
        Self {
            parent: Some(self),
            bindings: HashMap::new(),
        }
    }

    pub fn get_type(&self, name: &str) -> Option<&CuncType> {
        self.bindings
            .get(name)
            .or_else(||
                self.parent
                    .and_then(|p| p.get_type(name))
            )
    }

    pub fn set_type(&mut self, name: &str, typ: &CuncType) -> Result<(), ErrorCause> {
        if self.bindings.contains_key(name) {
            return Err(ErrorCause::Redefinition(name.to_string()));
        }
        self.bindings.insert(name.to_string(), CuncType::clone(typ));
        Ok(())
    }
}
