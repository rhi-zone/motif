use std::collections::HashMap;

use crate::theory::{SaturationConfig, Theory};
use crate::translate::pattern_to_expr;

/// A mapping for a single operation in a morphism.
#[derive(Debug, Clone)]
pub enum OpMapping {
    /// Simple rename: the operation maps to another operation of the same arity.
    Rename(String),
    /// Template: the operation maps to an expression template.
    /// Uses `$1`, `$2`, ... for positional arguments (already translated).
    Template(String),
}

/// A theory morphism: maps operations to expressions in a target theory.
///
/// Generalizes `Translation` (which only supports renaming) to allow
/// compound mappings where an operation maps to an arbitrary expression
/// over the target signature.
///
/// Simple rename (like Translation):
///   `add → mul`
///
/// Compound template:
///   `sub($1, $2) → (mul $1 (inv $2))`
#[derive(Debug, Clone)]
pub struct Morphism {
    pub name: String,
    mappings: HashMap<String, OpMapping>,
}

impl Morphism {
    pub fn new(name: &str) -> Self {
        Self {
            name: name.to_string(),
            mappings: HashMap::new(),
        }
    }

    /// Add a simple rename: source_op → target_op.
    pub fn add_rename(&mut self, source: &str, target: &str) {
        self.mappings
            .insert(source.to_string(), OpMapping::Rename(target.to_string()));
    }

    /// Add a compound mapping: source_op($1, ...) → template expression.
    ///
    /// The template uses `$1`, `$2`, etc. for the (already-translated) arguments.
    pub fn add_template(&mut self, source: &str, template: &str) {
        self.mappings.insert(
            source.to_string(),
            OpMapping::Template(template.to_string()),
        );
    }

    /// Apply this morphism to an s-expression, recursively translating operations.
    pub fn apply(&self, expr: &str) -> String {
        let trimmed = expr.trim();
        if !trimmed.starts_with('(') {
            return trimmed.to_string();
        }
        let inner = &trimmed[1..trimmed.len() - 1];
        let parts = split_top_level(inner.trim());
        if parts.is_empty() {
            return trimmed.to_string();
        }
        let op = &parts[0];
        let args: Vec<String> = parts[1..].iter().map(|a| self.apply(a)).collect();

        match self.mappings.get(op.as_str()) {
            Some(OpMapping::Rename(target)) => {
                if args.is_empty() {
                    format!("({})", target)
                } else {
                    format!("({} {})", target, args.join(" "))
                }
            }
            Some(OpMapping::Template(template)) => {
                let mut result = template.clone();
                for (i, arg) in args.iter().enumerate() {
                    result = result.replace(&format!("${}", i + 1), arg);
                }
                result
            }
            None => {
                if args.is_empty() {
                    format!("({})", op)
                } else {
                    format!("({} {})", op, args.join(" "))
                }
            }
        }
    }

    /// Compose two morphisms: `self` (A→B) then `other` (B→C), producing A→C.
    ///
    /// For rename mappings, chains through `other`'s mappings directly.
    /// For template mappings, applies `other` to the template expression,
    /// translating intermediate-theory operations while preserving `$N`
    /// argument placeholders.
    pub fn compose(&self, other: &Morphism) -> Morphism {
        let mut result = Morphism::new(&format!("{};{}", self.name, other.name));
        for (op, mapping) in &self.mappings {
            let composed = match mapping {
                OpMapping::Rename(target) => match other.mappings.get(target.as_str()) {
                    Some(m) => m.clone(),
                    None => OpMapping::Rename(target.clone()),
                },
                OpMapping::Template(template) => OpMapping::Template(other.apply(template)),
            };
            result.mappings.insert(op.clone(), composed);
        }
        result
    }

    /// Check which axioms of the source theory are preserved in the target theory.
    ///
    /// For each axiom, translates both sides through the morphism, converts
    /// pattern variables to `(Var "name")` expressions, and checks equivalence
    /// in the target theory. Returns a list of `(axiom_name, preserved)`.
    pub fn preserves_axioms(
        &self,
        source: &Theory,
        target: &Theory,
        config: &SaturationConfig,
    ) -> Result<Vec<(String, bool)>, egglog::Error> {
        let constructors: Vec<&str> = target
            .signature
            .ops()
            .iter()
            .map(|op| op.name.as_str())
            .collect();

        let mut results = Vec::new();
        for axiom in &source.axioms {
            let translated_lhs = self.apply(&axiom.lhs);
            let translated_rhs = self.apply(&axiom.rhs);
            let expr_lhs = pattern_to_expr(&translated_lhs, &constructors);
            let expr_rhs = pattern_to_expr(&translated_rhs, &constructors);
            let preserved = match target.equiv(&expr_lhs, &expr_rhs, config) {
                Ok(p) => p,
                Err(e) => {
                    let msg = e.to_string();
                    if msg.contains("UnboundFunction") || msg.contains("Unbound") {
                        false
                    } else {
                        return Err(e);
                    }
                }
            };
            results.push((axiom.name.clone(), preserved));
        }
        Ok(results)
    }
}

/// Split a string at top-level whitespace, respecting parentheses and string literals.
fn split_top_level(s: &str) -> Vec<String> {
    let mut tokens = Vec::new();
    let mut current = String::new();
    let mut depth = 0i32;
    let mut in_string = false;
    let bytes = s.as_bytes();
    let mut i = 0;

    while i < bytes.len() {
        let c = bytes[i];
        if in_string {
            current.push(c as char);
            if c == b'"' {
                in_string = false;
            } else if c == b'\\' && i + 1 < bytes.len() {
                i += 1;
                current.push(bytes[i] as char);
            }
            i += 1;
            continue;
        }
        match c {
            b'"' => {
                in_string = true;
                current.push('"');
                i += 1;
            }
            b'(' => {
                depth += 1;
                current.push('(');
                i += 1;
            }
            b')' => {
                depth -= 1;
                current.push(')');
                i += 1;
            }
            b' ' | b'\t' | b'\n' | b'\r' if depth == 0 => {
                if !current.is_empty() {
                    tokens.push(std::mem::take(&mut current));
                }
                i += 1;
            }
            _ => {
                current.push(c as char);
                i += 1;
            }
        }
    }
    if !current.is_empty() {
        tokens.push(current);
    }
    tokens
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::theories::{
        boolean_algebra::boolean_algebra_theory, group::group_theory, ring::ring_theory,
        semiring::semiring_theory,
    };

    fn config() -> SaturationConfig {
        SaturationConfig { iter_limit: 10 }
    }

    #[test]
    fn rename_works_like_translation() {
        let mut m = Morphism::new("ring_to_group");
        m.add_rename("add", "mul");
        m.add_rename("zero", "e");
        m.add_rename("negate", "inv");
        assert_eq!(
            m.apply("(add (add a b) (negate a))"),
            "(mul (mul a b) (inv a))"
        );
    }

    #[test]
    fn template_substitution() {
        let mut m = Morphism::new("define_sub");
        m.add_template("sub", "(add $1 (negate $2))");
        assert_eq!(m.apply("(sub a b)"), "(add a (negate b))");
    }

    #[test]
    fn template_with_nested_args() {
        let mut m = Morphism::new("define_sub");
        m.add_template("sub", "(add $1 (negate $2))");
        assert_eq!(m.apply("(sub (add a b) c)"), "(add (add a b) (negate c))");
    }

    #[test]
    fn unmapped_ops_preserved() {
        let mut m = Morphism::new("partial");
        m.add_rename("f", "g");
        assert_eq!(m.apply("(h (f a))"), "(h (g a))");
    }

    #[test]
    fn de_morgan_template() {
        let mut m = Morphism::new("de_morgan");
        m.add_template(
            "meet",
            "(complement (join (complement $1) (complement $2)))",
        );
        assert_eq!(
            m.apply("(meet a b)"),
            "(complement (join (complement a) (complement b)))"
        );
    }

    #[test]
    fn compose_rename_chain() {
        let mut ab = Morphism::new("a_to_b");
        ab.add_rename("f", "g");
        let mut bc = Morphism::new("b_to_c");
        bc.add_rename("g", "h");
        let ac = ab.compose(&bc);
        assert_eq!(ac.apply("(f x)"), "(h x)");
    }

    #[test]
    fn compose_template_through_rename() {
        // First: sub → (mul $1 (inv $2))
        // Second: mul → add, inv → negate
        // Composed: sub → (add $1 (negate $2))
        let mut first = Morphism::new("define_sub");
        first.add_template("sub", "(mul $1 (inv $2))");
        let mut second = Morphism::new("rename");
        second.add_rename("mul", "add");
        second.add_rename("inv", "negate");
        let composed = first.compose(&second);
        assert_eq!(composed.apply("(sub a b)"), "(add a (negate b))");
    }

    #[test]
    fn compound_subtraction_simplifies_in_group() {
        // sub(a, b) defined as mul(a, inv(b)) in a group
        let mut m = Morphism::new("sub_to_group");
        m.add_template("sub", "(mul $1 (inv $2))");

        let group = group_theory();
        let result = m.apply("(sub a a)");
        assert_eq!(result, "(mul a (inv a))");

        // Verify it simplifies to identity
        let constructors: Vec<&str> = group
            .signature
            .ops()
            .iter()
            .map(|op| op.name.as_str())
            .collect();
        let expr = pattern_to_expr(&result, &constructors);
        assert!(group.equiv(&expr, "(e)", &config()).unwrap());
    }

    #[test]
    fn boolean_algebra_to_semiring_preserves_some_axioms() {
        // Boolean algebra → semiring: meet→mul, join→add, zero→zero, one→one
        let mut m = Morphism::new("ba_to_semiring");
        m.add_rename("meet", "mul");
        m.add_rename("join", "add");
        m.add_rename("zero", "zero");
        m.add_rename("one", "one");

        let ba = boolean_algebra_theory();
        let sr = semiring_theory();
        let results = m.preserves_axioms(&ba, &sr, &config()).unwrap();

        let preserved: Vec<&str> = results
            .iter()
            .filter(|(_, p)| *p)
            .map(|(n, _)| n.as_str())
            .collect();
        let not_preserved: Vec<&str> = results
            .iter()
            .filter(|(_, p)| !*p)
            .map(|(n, _)| n.as_str())
            .collect();

        // Associativity, identities, commutativity of add, distributivity preserved
        assert!(preserved.contains(&"meet_associativity"));
        assert!(preserved.contains(&"join_associativity"));
        assert!(preserved.contains(&"join_commutativity"));
        assert!(preserved.contains(&"meet_identity"));
        assert!(preserved.contains(&"join_identity"));
        assert!(preserved.contains(&"meet_distributivity"));
        // mul is not commutative in a semiring
        assert!(not_preserved.contains(&"meet_commutativity"));
        // Complement axioms can't be stated in semiring
        assert!(not_preserved.contains(&"meet_complement"));
        assert!(not_preserved.contains(&"join_complement"));
        // Absorption and idempotence are not semiring properties
        assert!(not_preserved.contains(&"meet_absorption"));
        assert!(not_preserved.contains(&"join_absorption"));
    }

    #[test]
    fn ring_additive_morphism_preserves_group_axioms() {
        let mut m = Morphism::new("additive");
        m.add_rename("add", "mul");
        m.add_rename("zero", "e");
        m.add_rename("negate", "inv");

        let ring = ring_theory();
        let group = group_theory();
        let results = m.preserves_axioms(&ring, &group, &config()).unwrap();

        let preserved: Vec<&str> = results
            .iter()
            .filter(|(_, p)| *p)
            .map(|(n, _)| n.as_str())
            .collect();

        assert!(preserved.contains(&"add_right_identity"));
        assert!(preserved.contains(&"add_left_identity"));
        assert!(preserved.contains(&"add_right_inverse"));
        assert!(preserved.contains(&"add_left_inverse"));
        assert!(preserved.contains(&"add_associativity"));
    }
}
