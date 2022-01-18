use super::type_vars::TypeVarsMapping;

// Instantiated AST

enum Id {
    Local(String),
    Global(String, TypeVarsMapping)
}
