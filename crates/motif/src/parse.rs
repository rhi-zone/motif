use crate::signature::Signature;
use crate::theory::{Axiom, Theory};
use std::fmt;

/// Error from parsing a theory definition.
#[derive(Debug, Clone)]
pub struct ParseError {
    pub line: usize,
    pub message: String,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "line {}: {}", self.line, self.message)
    }
}

impl std::error::Error for ParseError {}

/// Parse a theory definition from a text format.
///
/// Format:
/// ```text
/// theory Group {
///   ops: e/0, inv/1, mul/2
///   axiom right_identity: (mul a (e)) = a
///   axiom left_identity: (mul (e) a) = a
///   axiom right_inverse: (mul a (inv a)) = (e)
///   axiom left_inverse: (mul (inv a) a) = (e)
///   axiom associativity: (mul (mul a b) c) = (mul a (mul b c))
/// }
/// ```
pub fn parse_theory(input: &str) -> Result<Theory, ParseError> {
    let mut lines = input.lines().enumerate().peekable();

    // Find "theory Name {"
    let (name, open_line) = loop {
        let Some((line_num, line)) = lines.next() else {
            return Err(ParseError {
                line: 0,
                message: "expected 'theory Name {'".to_string(),
            });
        };
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with('#') {
            continue;
        }
        let Some(rest) = trimmed.strip_prefix("theory ") else {
            return Err(ParseError {
                line: line_num + 1,
                message: format!("expected 'theory Name {{', got: {trimmed}"),
            });
        };
        let rest = rest.trim();
        let Some(name) = rest.strip_suffix('{') else {
            return Err(ParseError {
                line: line_num + 1,
                message: "expected '{{' after theory name".to_string(),
            });
        };
        break (name.trim().to_string(), line_num + 1);
    };

    if name.is_empty() {
        return Err(ParseError {
            line: open_line,
            message: "theory name cannot be empty".to_string(),
        });
    }

    let mut sig = Signature::new();
    let mut axioms = Vec::new();
    let mut found_close = false;

    for (line_num, line) in lines {
        let line_num = line_num + 1; // 1-indexed
        let trimmed = line.trim();

        if trimmed.is_empty() || trimmed.starts_with('#') {
            continue;
        }
        if trimmed == "}" {
            found_close = true;
            break;
        }

        if let Some(ops_str) = trimmed.strip_prefix("ops:") {
            // Parse "ops: e/0, inv/1, mul/2"
            for part in ops_str.split(',') {
                let part = part.trim();
                if part.is_empty() {
                    continue;
                }
                let Some((name, arity_str)) = part.split_once('/') else {
                    return Err(ParseError {
                        line: line_num,
                        message: format!("expected 'name/arity', got: {part}"),
                    });
                };
                let arity: usize = arity_str.trim().parse().map_err(|_| ParseError {
                    line: line_num,
                    message: format!("invalid arity: {}", arity_str.trim()),
                })?;
                sig.add_op(name.trim(), arity).map_err(|e| ParseError {
                    line: line_num,
                    message: e.to_string(),
                })?;
            }
        } else if let Some(rest) = trimmed.strip_prefix("axiom ") {
            // Parse "axiom name: lhs = rhs"
            let Some((name, equation)) = rest.split_once(':') else {
                return Err(ParseError {
                    line: line_num,
                    message: "expected 'axiom name: lhs = rhs'".to_string(),
                });
            };
            let name = name.trim();
            let equation = equation.trim();

            let Some((lhs, rhs)) = split_equation(equation) else {
                return Err(ParseError {
                    line: line_num,
                    message: format!("expected 'lhs = rhs', got: {equation}"),
                });
            };

            axioms.push(Axiom {
                name: name.to_string(),
                lhs: lhs.to_string(),
                rhs: rhs.to_string(),
            });
        } else {
            return Err(ParseError {
                line: line_num,
                message: format!("unexpected line: {trimmed}"),
            });
        }
    }

    if !found_close {
        return Err(ParseError {
            line: 0,
            message: "expected closing '}'".to_string(),
        });
    }

    Ok(Theory {
        name,
        signature: sig,
        axioms,
    })
}

/// Split an equation at the top-level `=` sign, respecting parentheses.
fn split_equation(s: &str) -> Option<(&str, &str)> {
    let mut depth = 0;
    for (i, ch) in s.char_indices() {
        match ch {
            '(' => depth += 1,
            ')' => depth -= 1,
            '=' if depth == 0 => {
                return Some((s[..i].trim(), s[i + 1..].trim()));
            }
            _ => {}
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::theory::SaturationConfig;

    #[test]
    fn parse_group_theory() {
        let input = r#"
theory Group {
  ops: e/0, inv/1, mul/2
  axiom right_identity: (mul a (e)) = a
  axiom left_identity: (mul (e) a) = a
  axiom right_inverse: (mul a (inv a)) = (e)
  axiom left_inverse: (mul (inv a) a) = (e)
  axiom associativity: (mul (mul a b) c) = (mul a (mul b c))
}
"#;
        let theory = parse_theory(input).unwrap();
        assert_eq!(theory.name, "Group");
        assert_eq!(theory.signature.ops().len(), 3);
        assert_eq!(theory.axioms.len(), 5);
        assert_eq!(theory.axioms[0].name, "right_identity");
        assert_eq!(theory.axioms[0].lhs, "(mul a (e))");
        assert_eq!(theory.axioms[0].rhs, "a");
    }

    #[test]
    fn parsed_theory_works_with_egglog() {
        let input = r#"
theory Group {
  ops: e/0, inv/1, mul/2
  axiom right_identity: (mul a (e)) = a
  axiom left_identity: (mul (e) a) = a
  axiom right_inverse: (mul a (inv a)) = (e)
  axiom left_inverse: (mul (inv a) a) = (e)
  axiom associativity: (mul (mul a b) c) = (mul a (mul b c))
}
"#;
        let theory = parse_theory(input).unwrap();
        let config = SaturationConfig { iter_limit: 5 };
        assert!(theory
            .equiv("(mul (Var \"a\") (e))", "(Var \"a\")", &config)
            .unwrap());
        assert!(theory
            .equiv(
                "(mul (inv (Var \"a\")) (mul (Var \"a\") (Var \"b\")))",
                "(Var \"b\")",
                &config,
            )
            .unwrap());
    }

    #[test]
    fn parse_with_comments() {
        let input = r#"
# A simple monoid
theory Monoid {
  ops: e/0, mul/2
  # Identity axioms
  axiom right_identity: (mul a (e)) = a
  axiom left_identity: (mul (e) a) = a
  axiom associativity: (mul (mul a b) c) = (mul a (mul b c))
}
"#;
        let theory = parse_theory(input).unwrap();
        assert_eq!(theory.name, "Monoid");
        assert_eq!(theory.axioms.len(), 3);
    }

    #[test]
    fn parse_error_missing_brace() {
        let input = "theory Oops {\n  ops: e/0\n";
        let err = parse_theory(input).unwrap_err();
        assert!(err.message.contains("closing '}'"));
    }

    #[test]
    fn parse_error_bad_arity() {
        let input = "theory Bad {\n  ops: e/abc\n}\n";
        let err = parse_theory(input).unwrap_err();
        assert!(err.message.contains("invalid arity"));
    }

    #[test]
    fn parse_error_missing_equals() {
        let input = "theory Bad {\n  ops: e/0\n  axiom x: (e) (e)\n}\n";
        let err = parse_theory(input).unwrap_err();
        assert!(err.message.contains("lhs = rhs"));
    }
}
