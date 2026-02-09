use crate::theory::{SaturationConfig, Theory};

/// A translation between theories: maps operation names from source to target.
///
/// Works at the s-expression string level — renames symbols in expressions
/// before feeding them to a different theory's egglog program.
#[derive(Debug, Clone)]
pub struct Translation {
    pub name: String,
    pub source: String,
    pub target: String,
    map: Vec<(String, String)>,
}

impl Translation {
    /// Create an empty translation between named theories.
    pub fn new(name: &str, source: &str, target: &str) -> Self {
        Self {
            name: name.to_string(),
            source: source.to_string(),
            target: target.to_string(),
            map: Vec::new(),
        }
    }

    /// Add an operation mapping: rename `from` to `to`.
    pub fn map_op(&mut self, from: &str, to: &str) {
        self.map.push((from.to_string(), to.to_string()));
    }

    /// Apply this translation to an s-expression string.
    ///
    /// Renames operation symbols at the start of parenthesized sub-expressions.
    /// This is a structural rewrite: only symbols in operator position (immediately
    /// after an opening paren) are renamed.
    pub fn apply(&self, expr: &str) -> String {
        let tokens = tokenize(expr);
        let mut result = Vec::with_capacity(tokens.len());
        let mut prev_open = false;

        for token in &tokens {
            if *token == "(" {
                prev_open = true;
                result.push(token.to_string());
            } else if prev_open {
                // This token is in operator position
                prev_open = false;
                if let Some((_, to)) = self.map.iter().find(|(from, _)| from == token) {
                    result.push(to.clone());
                } else {
                    result.push(token.to_string());
                }
            } else {
                prev_open = false;
                result.push(token.to_string());
            }
        }

        // Reconstruct with spacing: space between tokens except after ( and before )
        let mut out = String::new();
        for (i, token) in result.iter().enumerate() {
            if i > 0 && token != ")" && result[i - 1] != "(" {
                out.push(' ');
            }
            out.push_str(token);
        }
        out
    }

    /// Compose two translations: `self` (A→B) then `other` (B→C), producing A→C.
    ///
    /// For each mapping `a→b` in self: if other maps `b→c`, emit `a→c`.
    /// Otherwise, carry `a→b` through unchanged.
    pub fn compose(&self, other: &Translation) -> Translation {
        let mut result = Translation::new(
            &format!("{};{}", self.name, other.name),
            &self.source,
            &other.target,
        );
        for (from, to) in &self.map {
            if let Some((_, final_to)) = other.map.iter().find(|(k, _)| k == to) {
                result.map_op(from, final_to);
            } else {
                result.map_op(from, to);
            }
        }
        result
    }

    /// Check whether translating the source theory's axioms produces
    /// valid equalities in the target theory.
    ///
    /// For each axiom, translates both sides, converts pattern variables
    /// to `(Var "name")` expressions, and checks equivalence in the target
    /// theory. Returns a list of `(axiom_name, preserved)`.
    pub fn preserves_axioms(
        &self,
        source: &Theory,
        target: &Theory,
        config: &SaturationConfig,
    ) -> Result<Vec<(String, bool)>, egglog::Error> {
        // Collect all constructor names from the target theory
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
            // Convert pattern variables to (Var "name") expressions
            let expr_lhs = pattern_to_expr(&translated_lhs, &constructors);
            let expr_rhs = pattern_to_expr(&translated_rhs, &constructors);
            let preserved = match target.equiv(&expr_lhs, &expr_rhs, config) {
                Ok(p) => p,
                Err(e) => {
                    let msg = e.to_string();
                    // Axioms referencing constructors not in the target theory
                    // can't be stated, so they're not preserved.
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

/// Tokenize an s-expression into parens, strings, and symbols.
fn tokenize(s: &str) -> Vec<&str> {
    let mut tokens = Vec::new();
    let bytes = s.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        match bytes[i] {
            b'(' => {
                tokens.push("(");
                i += 1;
            }
            b')' => {
                tokens.push(")");
                i += 1;
            }
            b'"' => {
                // String literal: scan to closing quote
                let start = i;
                i += 1;
                while i < bytes.len() && bytes[i] != b'"' {
                    if bytes[i] == b'\\' {
                        i += 1; // skip escaped char
                    }
                    i += 1;
                }
                if i < bytes.len() {
                    i += 1; // closing quote
                }
                tokens.push(&s[start..i]);
            }
            b' ' | b'\t' | b'\n' | b'\r' => {
                i += 1;
            }
            _ => {
                let start = i;
                while i < bytes.len()
                    && !matches!(bytes[i], b'(' | b')' | b' ' | b'\t' | b'\n' | b'\r' | b'"')
                {
                    i += 1;
                }
                tokens.push(&s[start..i]);
            }
        }
    }
    tokens
}

/// Convert axiom pattern variables to `(Var "name")` expressions.
///
/// In axiom patterns, bare lowercase identifiers that aren't constructor names
/// are pattern variables. This converts them to concrete Var expressions so
/// they can be fed to `Theory::equiv()`.
fn pattern_to_expr(pattern: &str, constructors: &[&str]) -> String {
    let tokens = tokenize(pattern);
    let mut result = Vec::with_capacity(tokens.len());
    let mut prev_open = false;

    for token in &tokens {
        if *token == "(" {
            prev_open = true;
            result.push(token.to_string());
        } else if *token == ")" {
            prev_open = false;
            result.push(token.to_string());
        } else if prev_open {
            // Operator position — keep as-is
            prev_open = false;
            result.push(token.to_string());
        } else if token.starts_with('"') {
            // String literal — keep as-is
            result.push(token.to_string());
        } else if token.chars().next().is_some_and(|c| c.is_ascii_lowercase())
            && !constructors.contains(token)
            && *token != "Var"
        {
            // Bare variable — wrap in (Var "name")
            result.push(format!("(Var \"{token}\")"));
        } else {
            result.push(token.to_string());
        }
    }

    // Reconstruct with spacing
    let mut out = String::new();
    for (i, token) in result.iter().enumerate() {
        if i > 0 && token != ")" && !result[i - 1].ends_with('(') {
            out.push(' ');
        }
        out.push_str(token);
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn identity_translation() {
        let t = Translation::new("id", "A", "A");
        assert_eq!(t.apply("(f (g x))"), "(f (g x))");
    }

    #[test]
    fn single_op_rename() {
        let mut t = Translation::new("rename_f", "A", "B");
        t.map_op("f", "h");
        assert_eq!(t.apply("(f x)"), "(h x)");
    }

    #[test]
    fn nested_expression() {
        let mut t = Translation::new("nested", "A", "B");
        t.map_op("f", "h");
        t.map_op("g", "k");
        assert_eq!(t.apply("(f (g x) (g y))"), "(h (k x) (k y))");
    }

    #[test]
    fn does_not_rename_arguments() {
        let mut t = Translation::new("args", "A", "B");
        t.map_op("f", "h");
        // "f" in argument position should NOT be renamed
        assert_eq!(t.apply("(g f)"), "(g f)");
    }

    #[test]
    fn preserves_string_literals() {
        let t = Translation::new("strings", "A", "B");
        assert_eq!(t.apply("(Var \"hello\")"), "(Var \"hello\")");
    }

    #[test]
    fn forgetful_functor_ring_to_group() {
        let mut t = Translation::new("ring_to_additive_group", "Ring", "Group");
        t.map_op("add", "mul");
        t.map_op("zero", "e");
        t.map_op("negate", "inv");

        assert_eq!(
            t.apply("(add (add a b) (negate a))"),
            "(mul (mul a b) (inv a))"
        );
    }

    #[test]
    fn compose_identity() {
        let mut t = Translation::new("f_to_g", "A", "B");
        t.map_op("f", "g");
        let id = Translation::new("id", "B", "B");
        let composed = t.compose(&id);
        assert_eq!(composed.apply("(f x)"), "(g x)");
        assert_eq!(composed.source, "A");
        assert_eq!(composed.target, "B");
    }

    #[test]
    fn compose_chain() {
        let mut ab = Translation::new("a_to_b", "A", "B");
        ab.map_op("f", "g");
        let mut bc = Translation::new("b_to_c", "B", "C");
        bc.map_op("g", "h");
        let ac = ab.compose(&bc);
        assert_eq!(ac.apply("(f x)"), "(h x)");
        assert_eq!(ac.source, "A");
        assert_eq!(ac.target, "C");
    }

    #[test]
    fn compose_unmapped_passes_through() {
        let mut ab = Translation::new("a_to_b", "A", "B");
        ab.map_op("f", "g");
        ab.map_op("h", "k");
        // bc only maps g, not k
        let mut bc = Translation::new("b_to_c", "B", "C");
        bc.map_op("g", "z");
        let ac = ab.compose(&bc);
        // f→g→z, h→k (unchanged, bc doesn't touch k)
        assert_eq!(ac.apply("(f (h x))"), "(z (k x))");
    }
}
