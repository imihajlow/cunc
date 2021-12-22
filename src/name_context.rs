use std::collections::HashSet;

/// Class to check if certain name is a toplevel function (participating in dependency graph) or not.
/// This does not check for anything besides that.
pub struct NameContext {
    names: Vec<HashSet<String>>
}

impl NameContext {
    pub fn new() -> Self {
        Self {
            names: vec![HashSet::new()],
        }
    }

    pub fn push(&mut self) {
        self.names.push(HashSet::new())
    }

    pub fn pop(&mut self) {
        self.names.pop();
    }

    pub fn add_name(&mut self, name: &str) {
        self.names.last_mut().unwrap().insert(name.to_string());
    } 

    pub fn is_toplevel(&self, name: &str) -> bool {
        self.names.first().unwrap().contains(name)
    }
}
