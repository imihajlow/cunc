use std::collections::HashMap;

use crate::error::{ErrorCause};
use crate::type_info::TypeInfo;

pub struct GenericContext<> {
    bindings: HashMap<String, TypeInfo>
}

impl GenericContext {
    pub fn new() -> Self {
        Self {
            bindings: HashMap::new()
        }
    }

    pub fn get_type(&self, name: &str) -> Option<&TypeInfo> {
        self.bindings
            .get(name)
    }

    pub fn set_type(&mut self, name: &str, typ: &TypeInfo) -> Result<(), ErrorCause> {
        if self.bindings.contains_key(name) {
            return Err(ErrorCause::Redefinition(name.to_string()));
        }
        self.bindings.insert(name.to_string(), TypeInfo::clone(typ));
        Ok(())
    }
}
