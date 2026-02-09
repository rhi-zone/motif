//! Utilities for working with s-expressions.

/// Split a string at top-level whitespace, respecting parentheses and string literals.
pub fn split_top_level(s: &str) -> Vec<String> {
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
