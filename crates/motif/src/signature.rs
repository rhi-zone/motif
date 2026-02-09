use std::fmt;

/// An operation in a signature: a name and its arity.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Op {
    pub name: String,
    pub arity: usize,
}

/// Errors that can occur when building a signature.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SignatureError {
    DuplicateOp(String),
}

impl fmt::Display for SignatureError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SignatureError::DuplicateOp(name) => write!(f, "duplicate operation: {name}"),
        }
    }
}

impl std::error::Error for SignatureError {}

/// A many-sorted algebraic signature: a set of operations with arities.
#[derive(Debug, Clone)]
pub struct Signature {
    ops: Vec<Op>,
}

impl Signature {
    /// Create an empty signature.
    pub fn new() -> Self {
        Self { ops: Vec::new() }
    }

    /// Add an operation with the given name and arity. Rejects duplicates.
    pub fn add_op(&mut self, name: &str, arity: usize) -> Result<(), SignatureError> {
        if self.ops.iter().any(|op| op.name == name) {
            return Err(SignatureError::DuplicateOp(name.to_string()));
        }
        self.ops.push(Op {
            name: name.to_string(),
            arity,
        });
        Ok(())
    }

    /// Look up an operation by name.
    pub fn get_op(&self, name: &str) -> Option<&Op> {
        self.ops.iter().find(|op| op.name == name)
    }

    /// All operations in insertion order.
    pub fn ops(&self) -> &[Op] {
        &self.ops
    }

    /// Compile this signature to an egglog program fragment:
    /// a `(datatype Expr ...)` declaration plus a `(relation universe (Expr))`
    /// with tracking rules that populate the universe for each constructor.
    ///
    /// The universe relation is needed so that axioms with bare-variable sides
    /// (e.g., identity laws like `mul(a, e) = a`) can be expressed as guarded
    /// rules in egglog, which requires all rewrite LHS variables to be grounded.
    pub fn to_egglog(&self) -> String {
        let mut constructors = vec!["  (Var String)".to_string()];
        for op in &self.ops {
            if op.arity == 0 {
                constructors.push(format!("  ({})", op.name));
            } else {
                let args = std::iter::repeat_n("Expr", op.arity)
                    .collect::<Vec<_>>()
                    .join(" ");
                constructors.push(format!("  ({} {})", op.name, args));
            }
        }
        let datatype = format!("(datatype Expr\n{})", constructors.join("\n"));

        // Ruleset + universe relation + tracking rules for grounding bare variables
        let mut universe_rules = vec![
            "(ruleset axioms)".to_string(),
            "(relation universe (Expr))".to_string(),
            "(rule ((= x (Var s))) ((universe x)) :ruleset axioms)".to_string(),
        ];
        for op in &self.ops {
            if op.arity == 0 {
                universe_rules.push(format!(
                    "(rule ((= x ({}))) ((universe x)) :ruleset axioms)",
                    op.name
                ));
            } else {
                let vars: Vec<String> = (0..op.arity).map(|i| format!("a{i}")).collect();
                let pattern = format!("({} {})", op.name, vars.join(" "));
                let mut actions: Vec<String> = vec![format!("(universe x)")];
                for v in &vars {
                    actions.push(format!("(universe {v})"));
                }
                universe_rules.push(format!(
                    "(rule ((= x {pattern})) ({}) :ruleset axioms)",
                    actions.join(" ")
                ));
            }
        }

        format!("{datatype}\n{}", universe_rules.join("\n"))
    }
}

impl Default for Signature {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_signature() {
        let sig = Signature::new();
        assert!(sig.ops().is_empty());
    }

    #[test]
    fn add_and_lookup() {
        let mut sig = Signature::new();
        sig.add_op("e", 0).unwrap();
        sig.add_op("inv", 1).unwrap();
        sig.add_op("mul", 2).unwrap();

        assert_eq!(sig.get_op("e").unwrap().arity, 0);
        assert_eq!(sig.get_op("inv").unwrap().arity, 1);
        assert_eq!(sig.get_op("mul").unwrap().arity, 2);
        assert!(sig.get_op("nonexistent").is_none());
    }

    #[test]
    fn duplicate_rejection() {
        let mut sig = Signature::new();
        sig.add_op("e", 0).unwrap();
        assert_eq!(
            sig.add_op("e", 0),
            Err(SignatureError::DuplicateOp("e".to_string()))
        );
    }

    #[test]
    fn ops_preserves_order() {
        let mut sig = Signature::new();
        sig.add_op("e", 0).unwrap();
        sig.add_op("inv", 1).unwrap();
        sig.add_op("mul", 2).unwrap();
        let names: Vec<&str> = sig.ops().iter().map(|op| op.name.as_str()).collect();
        assert_eq!(names, vec!["e", "inv", "mul"]);
    }

    #[test]
    fn to_egglog_nullary() {
        let mut sig = Signature::new();
        sig.add_op("e", 0).unwrap();
        let egglog = sig.to_egglog();
        assert!(egglog.contains("(e)"));
        assert!(egglog.contains("(Var String)"));
    }

    #[test]
    fn to_egglog_unary() {
        let mut sig = Signature::new();
        sig.add_op("inv", 1).unwrap();
        let egglog = sig.to_egglog();
        assert!(egglog.contains("(inv Expr)"));
    }

    #[test]
    fn to_egglog_binary() {
        let mut sig = Signature::new();
        sig.add_op("mul", 2).unwrap();
        let egglog = sig.to_egglog();
        assert!(egglog.contains("(mul Expr Expr)"));
    }

    #[test]
    fn to_egglog_group_signature() {
        let mut sig = Signature::new();
        sig.add_op("e", 0).unwrap();
        sig.add_op("inv", 1).unwrap();
        sig.add_op("mul", 2).unwrap();
        let egglog = sig.to_egglog();
        // Datatype declaration
        assert!(egglog
            .contains("(datatype Expr\n  (Var String)\n  (e)\n  (inv Expr)\n  (mul Expr Expr))"));
        // Ruleset, universe relation, and tracking rules
        assert!(egglog.contains("(ruleset axioms)"));
        assert!(egglog.contains("(relation universe (Expr))"));
        assert!(egglog.contains("(rule ((= x (Var s))) ((universe x)) :ruleset axioms)"));
        assert!(egglog.contains("(rule ((= x (e))) ((universe x)) :ruleset axioms)"));
        assert!(
            egglog.contains("(rule ((= x (inv a0))) ((universe x) (universe a0)) :ruleset axioms)")
        );
        assert!(egglog.contains(
            "(rule ((= x (mul a0 a1))) ((universe x) (universe a0) (universe a1)) :ruleset axioms)"
        ));
    }
}
