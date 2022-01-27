use std::collections::HashMap;

use crate::error::ErrorCause;

/// Keeps track of arbitrary properties of variables.
pub(super) struct TypeScope<'a, T>
where
    T: Clone,
{
    parent: Option<&'a Self>,
    bindings: HashMap<String, T>,
}

impl<'a, T: Clone> TypeScope<'a, T> {
    pub fn new() -> Self {
        Self {
            parent: None,
            bindings: HashMap::new(),
        }
    }

    pub fn push(&'a self) -> Self {
        Self {
            parent: Some(self),
            bindings: HashMap::new(),
        }
    }

    pub fn get(&self, name: &str) -> Option<&T> {
        self.bindings
            .get(name)
            .or_else(|| self.parent.and_then(|p| p.get(name)))
    }

    pub fn set(&mut self, name: &str, val: &T) -> Result<(), ErrorCause> {
        if self.bindings.contains_key(name) {
            return Err(ErrorCause::Redefinition(name.to_string()));
        }
        self.bindings.insert(name.to_string(), T::clone(val));
        Ok(())
    }

    pub fn convert<NewT: From<T> + Clone>(&self) -> TypeScope<'a, NewT> {
        match self.parent {
            None => TypeScope {
                parent: None,
                bindings: self
                    .bindings
                    .iter()
                    .map(|(name, val)| (name.to_owned(), NewT::from(val.to_owned())))
                    .collect(),
            },
            Some(p) => {
                let mut result = p.convert::<NewT>();
                for (name, val) in self.bindings.iter() {
                    result
                        .bindings
                        .insert(name.to_owned(), NewT::from(val.to_owned()));
                }
                result
            }
        }
    }
}
