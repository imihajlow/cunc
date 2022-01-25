use std::collections::HashMap;
use std::collections::HashSet;

use crate::error::ErrorCause;

/// Class to check if certain name is a toplevel function (participating in dependency graph) or not.
/// This does not check for anything besides that.
pub(super) struct NameScope {
    toplevel: HashSet<String>,
}

impl NameScope {
    pub fn new() -> Self {
        Self {
            toplevel: HashSet::new(),
        }
    }

    pub fn add_toplevel(&mut self, name: &str) {
        self.toplevel.insert(name.to_string());
    }

    pub fn is_toplevel(&self, name: &str) -> bool {
        self.toplevel.contains(name)
    }
}

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
}
