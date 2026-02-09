use std::collections::HashMap;

use crate::sexpr::split_top_level;

/// Output format for pretty-printing.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Format {
    /// Unicode math symbols: a · b, a⁻¹, ¬a, a ∧ b
    Unicode,
    /// LaTeX math mode: a \cdot b, a^{-1}, \lnot a, a \land b
    Latex,
    /// Plain ASCII: a * b, a^(-1), ~a, a /\ b
    Ascii,
}

/// How to display an operation.
#[derive(Debug, Clone)]
pub enum OpNotation {
    /// Nullary constant: displayed as the given symbol.
    Constant(String),
    /// Unary prefix: symbol before the argument (e.g., `-a`).
    Prefix(String),
    /// Unary postfix: symbol after the argument.
    /// For Unicode: appended directly (e.g., `⁻¹`).
    /// For LaTeX: placed in superscript (e.g., `-1` → `^{-1}`).
    /// For ASCII: placed in caret parens (e.g., `-1` → `^(-1)`).
    Postfix(String),
    /// Binary infix: symbol between arguments with a precedence level.
    /// Higher precedence binds tighter. Used for parenthesization.
    Infix(String, u8),
}

/// A notation map for pretty-printing s-expressions.
#[derive(Debug, Clone)]
pub struct Notation {
    ops: HashMap<String, OpNotation>,
    pub format: Format,
}

impl Notation {
    pub fn new(format: Format) -> Self {
        Self {
            ops: HashMap::new(),
            format,
        }
    }

    pub fn add(&mut self, op: &str, notation: OpNotation) {
        self.ops.insert(op.to_string(), notation);
    }

    pub fn get(&self, op: &str) -> Option<&OpNotation> {
        self.ops.get(op)
    }
}

/// Default Unicode notation for common algebraic operations.
pub fn default_notation() -> Notation {
    unicode_notation()
}

/// Unicode notation: a · b, a⁻¹, ¬a, a ∧ b
pub fn unicode_notation() -> Notation {
    let mut n = Notation::new(Format::Unicode);
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

/// LaTeX notation: a \cdot b, a^{-1}, \lnot a, a \land b
pub fn latex_notation() -> Notation {
    let mut n = Notation::new(Format::Latex);
    // Group-like
    n.add("e", OpNotation::Constant("e".to_string()));
    n.add("inv", OpNotation::Postfix("-1".to_string()));
    n.add("mul", OpNotation::Infix("\\cdot".to_string(), 6));
    // Ring-like
    n.add("zero", OpNotation::Constant("0".to_string()));
    n.add("one", OpNotation::Constant("1".to_string()));
    n.add("negate", OpNotation::Prefix("-".to_string()));
    n.add("add", OpNotation::Infix("+".to_string(), 4));
    n.add("reciprocal", OpNotation::Postfix("-1".to_string()));
    // Lattice-like
    n.add("meet", OpNotation::Infix("\\land".to_string(), 6));
    n.add("join", OpNotation::Infix("\\lor".to_string(), 4));
    n.add("complement", OpNotation::Prefix("\\lnot ".to_string()));
    n
}

/// ASCII notation: a * b, a^(-1), ~a, a /\ b
pub fn ascii_notation() -> Notation {
    let mut n = Notation::new(Format::Ascii);
    // Group-like
    n.add("e", OpNotation::Constant("e".to_string()));
    n.add("inv", OpNotation::Postfix("-1".to_string()));
    n.add("mul", OpNotation::Infix("*".to_string(), 6));
    // Ring-like
    n.add("zero", OpNotation::Constant("0".to_string()));
    n.add("one", OpNotation::Constant("1".to_string()));
    n.add("negate", OpNotation::Prefix("-".to_string()));
    n.add("add", OpNotation::Infix("+".to_string(), 4));
    n.add("reciprocal", OpNotation::Postfix("-1".to_string()));
    // Lattice-like
    n.add("meet", OpNotation::Infix("/\\".to_string(), 6));
    n.add("join", OpNotation::Infix("\\/".to_string(), 4));
    n.add("complement", OpNotation::Prefix("~".to_string()));
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
            let compound = is_compound(arg_expr, notation);
            if compound {
                match notation.format {
                    Format::Latex => format!("{sym}\\left({arg}\\right)"),
                    _ => format!("{sym}({arg})"),
                }
            } else {
                format!("{sym}{arg}")
            }
        }
        Some(OpNotation::Postfix(sym)) => {
            let arg_expr = args.first().unwrap_or(&"?");
            let arg = pretty_inner(arg_expr, notation, 0);
            let compound = is_compound(arg_expr, notation);
            match notation.format {
                Format::Unicode => {
                    if compound {
                        format!("({arg}){sym}")
                    } else {
                        format!("{arg}{sym}")
                    }
                }
                Format::Latex => {
                    if compound {
                        format!("\\left({arg}\\right)^{{{sym}}}")
                    } else {
                        format!("{arg}^{{{sym}}}")
                    }
                }
                Format::Ascii => {
                    if compound {
                        format!("({arg})^({sym})")
                    } else {
                        format!("{arg}^({sym})")
                    }
                }
            }
        }
        Some(OpNotation::Infix(sym, prec)) => {
            let lhs = pretty_inner(args.first().unwrap_or(&"?"), notation, *prec);
            let rhs = pretty_inner(args.get(1).unwrap_or(&"?"), notation, *prec);
            let result = format!("{lhs} {sym} {rhs}");
            if *prec < parent_prec {
                match notation.format {
                    Format::Latex => format!("\\left({result}\\right)"),
                    _ => format!("({result})"),
                }
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

#[cfg(test)]
mod tests {
    use super::*;

    fn uni() -> Notation {
        unicode_notation()
    }

    // --- Unicode format ---

    #[test]
    fn unicode_variable() {
        assert_eq!(pretty("(Var \"a\")", &uni()), "a");
    }

    #[test]
    fn unicode_constant() {
        assert_eq!(pretty("(e)", &uni()), "e");
        assert_eq!(pretty("(zero)", &uni()), "0");
    }

    #[test]
    fn unicode_infix() {
        assert_eq!(
            pretty("(mul (Var \"a\") (Var \"b\"))", &uni()),
            "a \u{00b7} b"
        );
    }

    #[test]
    fn unicode_postfix() {
        assert_eq!(pretty("(inv (Var \"a\"))", &uni()), "a\u{207b}\u{00b9}");
    }

    #[test]
    fn unicode_prefix() {
        assert_eq!(pretty("(negate (Var \"a\"))", &uni()), "-a");
    }

    #[test]
    fn unicode_precedence() {
        // add(a, mul(b, c)) — mul binds tighter, no parens
        assert_eq!(
            pretty("(add (Var \"a\") (mul (Var \"b\") (Var \"c\")))", &uni()),
            "a + b \u{00b7} c"
        );
        // mul(add(a, b), c) — add is lower, needs parens
        assert_eq!(
            pretty("(mul (add (Var \"a\") (Var \"b\")) (Var \"c\"))", &uni()),
            "(a + b) \u{00b7} c"
        );
    }

    #[test]
    fn unicode_postfix_compound() {
        assert_eq!(
            pretty("(inv (mul (Var \"a\") (Var \"b\")))", &uni()),
            "(a \u{00b7} b)\u{207b}\u{00b9}"
        );
    }

    #[test]
    fn unicode_prefix_compound() {
        assert_eq!(
            pretty("(negate (add (Var \"a\") (Var \"b\")))", &uni()),
            "-(a + b)"
        );
    }

    #[test]
    fn unicode_lattice() {
        assert_eq!(
            pretty("(meet (Var \"a\") (join (Var \"a\") (Var \"b\")))", &uni()),
            "a \u{2227} (a \u{2228} b)"
        );
    }

    // --- LaTeX format ---

    #[test]
    fn latex_infix() {
        let n = latex_notation();
        assert_eq!(pretty("(mul (Var \"a\") (Var \"b\"))", &n), "a \\cdot b");
    }

    #[test]
    fn latex_postfix() {
        let n = latex_notation();
        assert_eq!(pretty("(inv (Var \"a\"))", &n), "a^{-1}");
    }

    #[test]
    fn latex_postfix_compound() {
        let n = latex_notation();
        assert_eq!(
            pretty("(inv (mul (Var \"a\") (Var \"b\")))", &n),
            "\\left(a \\cdot b\\right)^{-1}"
        );
    }

    #[test]
    fn latex_prefix() {
        let n = latex_notation();
        assert_eq!(pretty("(complement (Var \"a\"))", &n), "\\lnot a");
    }

    #[test]
    fn latex_prefix_compound() {
        let n = latex_notation();
        assert_eq!(
            pretty("(complement (join (Var \"a\") (Var \"b\")))", &n),
            "\\lnot \\left(a \\lor b\\right)"
        );
    }

    #[test]
    fn latex_precedence_parens() {
        let n = latex_notation();
        assert_eq!(
            pretty("(mul (add (Var \"a\") (Var \"b\")) (Var \"c\"))", &n),
            "\\left(a + b\\right) \\cdot c"
        );
    }

    #[test]
    fn latex_lattice() {
        let n = latex_notation();
        assert_eq!(
            pretty("(meet (Var \"a\") (join (Var \"a\") (Var \"b\")))", &n),
            "a \\land \\left(a \\lor b\\right)"
        );
    }

    // --- ASCII format ---

    #[test]
    fn ascii_infix() {
        let n = ascii_notation();
        assert_eq!(pretty("(mul (Var \"a\") (Var \"b\"))", &n), "a * b");
    }

    #[test]
    fn ascii_postfix() {
        let n = ascii_notation();
        assert_eq!(pretty("(inv (Var \"a\"))", &n), "a^(-1)");
    }

    #[test]
    fn ascii_postfix_compound() {
        let n = ascii_notation();
        assert_eq!(
            pretty("(inv (mul (Var \"a\") (Var \"b\")))", &n),
            "(a * b)^(-1)"
        );
    }

    #[test]
    fn ascii_lattice() {
        let n = ascii_notation();
        assert_eq!(
            pretty("(meet (Var \"a\") (join (Var \"a\") (Var \"b\")))", &n),
            "a /\\ (a \\/ b)"
        );
    }

    #[test]
    fn unknown_op_falls_back() {
        assert_eq!(pretty("(foo (Var \"a\") (Var \"b\"))", &uni()), "foo(a, b)");
    }
}
