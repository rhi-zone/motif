use std::collections::HashMap;

/// How to display an operation.
#[derive(Debug, Clone)]
pub enum OpNotation {
    /// Nullary constant: displayed as the given symbol.
    Constant(String),
    /// Unary prefix: symbol before the argument (e.g., `-a`).
    Prefix(String),
    /// Unary postfix: symbol after the argument (e.g., `a⁻¹`).
    Postfix(String),
    /// Binary infix: symbol between arguments with a precedence level.
    /// Higher precedence binds tighter. Used for parenthesization.
    Infix(String, u8),
}

/// A notation map for pretty-printing s-expressions.
#[derive(Debug, Clone)]
pub struct Notation {
    ops: HashMap<String, OpNotation>,
}

impl Notation {
    pub fn new() -> Self {
        Self {
            ops: HashMap::new(),
        }
    }

    pub fn add(&mut self, op: &str, notation: OpNotation) {
        self.ops.insert(op.to_string(), notation);
    }

    pub fn get(&self, op: &str) -> Option<&OpNotation> {
        self.ops.get(op)
    }
}

impl Default for Notation {
    fn default() -> Self {
        Self::new()
    }
}

/// Default notation for common algebraic operations.
pub fn default_notation() -> Notation {
    let mut n = Notation::new();
    // Group-like
    n.add("e", OpNotation::Constant("e".to_string()));
    n.add("inv", OpNotation::Postfix("\u{207b}\u{00b9}".to_string())); // ⁻¹
    n.add("mul", OpNotation::Infix("\u{00b7}".to_string(), 6)); // ·
                                                                // Ring-like
    n.add("zero", OpNotation::Constant("0".to_string()));
    n.add("one", OpNotation::Constant("1".to_string()));
    n.add("negate", OpNotation::Prefix("-".to_string()));
    n.add("add", OpNotation::Infix("+".to_string(), 4));
    n.add(
        "reciprocal",
        OpNotation::Postfix("\u{207b}\u{00b9}".to_string()),
    );
    // Lattice-like
    n.add("meet", OpNotation::Infix("\u{2227}".to_string(), 6)); // ∧
    n.add("join", OpNotation::Infix("\u{2228}".to_string(), 4)); // ∨
    n.add("complement", OpNotation::Prefix("\u{00ac}".to_string())); // ¬
    n
}

/// Pretty-print an s-expression using the given notation.
pub fn pretty(expr: &str, notation: &Notation) -> String {
    pretty_inner(expr, notation, 0)
}

/// Inner recursive pretty-printer. `parent_prec` is the precedence of the
/// enclosing infix operator (0 = top level, no parens needed).
fn pretty_inner(expr: &str, notation: &Notation, parent_prec: u8) -> String {
    let trimmed = expr.trim();

    // Bare variable
    if !trimmed.starts_with('(') {
        return trimmed.to_string();
    }

    let inner = &trimmed[1..trimmed.len() - 1];
    let parts = split_top_level(inner.trim());
    if parts.is_empty() {
        return trimmed.to_string();
    }

    let op = &parts[0];

    // (Var "name") → name
    if op == "Var" && parts.len() == 2 {
        return parts[1].trim_matches('"').to_string();
    }

    let args: Vec<&str> = parts[1..].iter().map(|s| s.as_str()).collect();

    match notation.get(op) {
        Some(OpNotation::Constant(sym)) => sym.clone(),
        Some(OpNotation::Prefix(sym)) => {
            let arg_expr = args.first().unwrap_or(&"?");
            let arg = pretty_inner(arg_expr, notation, 0);
            if is_compound(arg_expr, notation) {
                format!("{sym}({arg})")
            } else {
                format!("{sym}{arg}")
            }
        }
        Some(OpNotation::Postfix(sym)) => {
            let arg_expr = args.first().unwrap_or(&"?");
            let arg = pretty_inner(arg_expr, notation, 0);
            if is_compound(arg_expr, notation) {
                format!("({arg}){sym}")
            } else {
                format!("{arg}{sym}")
            }
        }
        Some(OpNotation::Infix(sym, prec)) => {
            let lhs = pretty_inner(args.first().unwrap_or(&"?"), notation, *prec);
            let rhs = pretty_inner(args.get(1).unwrap_or(&"?"), notation, *prec);
            let result = format!("{lhs} {sym} {rhs}");
            if *prec < parent_prec {
                format!("({result})")
            } else {
                result
            }
        }
        None => {
            // Unknown op — use function-call notation
            if args.is_empty() {
                op.to_string()
            } else {
                let arg_strs: Vec<String> =
                    args.iter().map(|a| pretty_inner(a, notation, 0)).collect();
                format!("{}({})", op, arg_strs.join(", "))
            }
        }
    }
}

/// Check if an s-expression is a compound (non-atomic) expression that
/// needs parentheses when used as an argument to prefix/postfix operators.
fn is_compound(expr: &str, notation: &Notation) -> bool {
    let trimmed = expr.trim();
    if !trimmed.starts_with('(') {
        return false; // bare atom
    }
    let inner = &trimmed[1..trimmed.len() - 1];
    let parts = split_top_level(inner.trim());
    if parts.is_empty() {
        return false;
    }
    let op = &parts[0];
    if op == "Var" {
        return false;
    }
    match notation.get(op) {
        Some(OpNotation::Constant(_)) => false,
        _ => parts.len() > 1, // has arguments → compound
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

    fn n() -> Notation {
        default_notation()
    }

    #[test]
    fn variable() {
        assert_eq!(pretty("(Var \"a\")", &n()), "a");
    }

    #[test]
    fn constant() {
        assert_eq!(pretty("(e)", &n()), "e");
        assert_eq!(pretty("(zero)", &n()), "0");
        assert_eq!(pretty("(one)", &n()), "1");
    }

    #[test]
    fn binary_infix() {
        assert_eq!(
            pretty("(mul (Var \"a\") (Var \"b\"))", &n()),
            "a \u{00b7} b"
        );
        assert_eq!(pretty("(add (Var \"a\") (Var \"b\"))", &n()), "a + b");
    }

    #[test]
    fn unary_postfix() {
        assert_eq!(pretty("(inv (Var \"a\"))", &n()), "a\u{207b}\u{00b9}");
    }

    #[test]
    fn unary_prefix() {
        assert_eq!(pretty("(negate (Var \"a\"))", &n()), "-a");
        assert_eq!(pretty("(complement (Var \"a\"))", &n()), "\u{00ac}a");
    }

    #[test]
    fn nested_same_precedence() {
        // mul(mul(a, b), c) should not need extra parens (left-associative feel)
        assert_eq!(
            pretty("(mul (mul (Var \"a\") (Var \"b\")) (Var \"c\"))", &n()),
            "a \u{00b7} b \u{00b7} c"
        );
    }

    #[test]
    fn mixed_precedence_no_parens_needed() {
        // add(a, mul(b, c)) — mul has higher precedence, no parens needed
        assert_eq!(
            pretty("(add (Var \"a\") (mul (Var \"b\") (Var \"c\")))", &n()),
            "a + b \u{00b7} c"
        );
    }

    #[test]
    fn mixed_precedence_parens_needed() {
        // mul(add(a, b), c) — add has lower precedence, needs parens
        assert_eq!(
            pretty("(mul (add (Var \"a\") (Var \"b\")) (Var \"c\"))", &n()),
            "(a + b) \u{00b7} c"
        );
    }

    #[test]
    fn postfix_on_compound() {
        // inv(mul(a, b)) → (a · b)⁻¹
        assert_eq!(
            pretty("(inv (mul (Var \"a\") (Var \"b\")))", &n()),
            "(a \u{00b7} b)\u{207b}\u{00b9}"
        );
    }

    #[test]
    fn prefix_on_compound() {
        // negate(add(a, b)) → -(a + b)
        assert_eq!(
            pretty("(negate (add (Var \"a\") (Var \"b\")))", &n()),
            "-(a + b)"
        );
    }

    #[test]
    fn identity_law() {
        // mul(a, e) → a · e
        assert_eq!(pretty("(mul (Var \"a\") (e))", &n()), "a \u{00b7} e");
    }

    #[test]
    fn inverse_cancellation() {
        // mul(a, inv(a)) → a · a⁻¹
        assert_eq!(
            pretty("(mul (Var \"a\") (inv (Var \"a\")))", &n()),
            "a \u{00b7} a\u{207b}\u{00b9}"
        );
    }

    #[test]
    fn lattice_absorption() {
        // meet(a, join(a, b)) → a ∧ (a ∨ b)
        assert_eq!(
            pretty("(meet (Var \"a\") (join (Var \"a\") (Var \"b\")))", &n()),
            "a \u{2227} (a \u{2228} b)"
        );
    }

    #[test]
    fn unknown_op_falls_back() {
        assert_eq!(pretty("(foo (Var \"a\") (Var \"b\"))", &n()), "foo(a, b)");
    }
}
