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
}
