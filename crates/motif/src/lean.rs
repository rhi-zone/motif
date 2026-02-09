use crate::explore::EquivClass;
use crate::sexpr::split_top_level;
use crate::theory::Theory;

/// Export a theory as a Lean 4 class definition.
///
/// Generates an opaque sort, operation declarations, and axioms as
/// class fields. The output is a self-contained Lean 4 snippet.
pub fn theory_to_lean(theory: &Theory) -> String {
    let name = &theory.name;
    let mut lines = Vec::new();

    lines.push(format!("class {name} (α : Type) where"));

    // Operations
    for op in theory.signature.ops() {
        let typ = match op.arity {
            0 => "α".to_string(),
            1 => "α → α".to_string(),
            2 => "α → α → α".to_string(),
            n => {
                let args: Vec<&str> = (0..n).map(|_| "α").collect();
                format!("{} → α", args.join(" → "))
            }
        };
        lines.push(format!("  {} : {}", op.name, typ));
    }

    // Axioms
    for axiom in &theory.axioms {
        let vars = collect_axiom_vars(&axiom.lhs, &axiom.rhs, theory);
        let var_binders = if vars.is_empty() {
            String::new()
        } else {
            let binder_list: Vec<String> = vars.iter().map(|v| format!("{v} : α")).collect();
            format!("∀ ({}), ", binder_list.join(") ("))
        };
        let lhs = sexpr_to_lean(&axiom.lhs, theory);
        let rhs = sexpr_to_lean(&axiom.rhs, theory);
        lines.push(format!(
            "  {} : {}{} = {}",
            axiom.name, var_binders, lhs, rhs
        ));
    }

    lines.join("\n")
}

/// Export equivalence classes as Lean 4 theorem statements.
///
/// Each equivalence pair becomes a `theorem` with a `sorry` proof.
/// The theorems reference the theory class for their operations.
pub fn equiv_classes_to_lean(theory: &Theory, classes: &[EquivClass], prefix: &str) -> String {
    let name = &theory.name;
    let mut lines = Vec::new();

    for (i, class) in classes.iter().enumerate() {
        for j in 1..class.members.len() {
            let a = &class.members[0];
            let b = &class.members[j];
            let vars = collect_expr_vars_pair(a, b, theory);
            let var_binders = if vars.is_empty() {
                String::new()
            } else {
                let binder_list: Vec<String> = vars.iter().map(|v| format!("{v} : α")).collect();
                format!(" ({})", binder_list.join(") ("))
            };

            let lhs = sexpr_to_lean(a, theory);
            let rhs = sexpr_to_lean(b, theory);
            lines.push(format!(
                "theorem {prefix}_{}_{}  [{name} α]{var_binders} : {lhs} = {rhs} := by sorry",
                i + 1,
                j
            ));
        }
    }

    lines.join("\n")
}

/// Convert an s-expression to Lean 4 syntax.
///
/// - `(Var "x")` → `x`
/// - `(op)` → `@ClassName.op α _`  (nullary)
/// - `(op a)` → `ClassName.op a`
/// - `(op a b)` → `ClassName.op a b`
/// - bare variable `x` → `x`
fn sexpr_to_lean(expr: &str, theory: &Theory) -> String {
    let trimmed = expr.trim();

    // Bare variable (no parens)
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
        let name = parts[1].trim_matches('"');
        return name.to_string();
    }

    let args: Vec<String> = parts[1..]
        .iter()
        .map(|a| sexpr_to_lean(a, theory))
        .collect();

    let class_name = &theory.name;

    // Check if this is a theory operation
    let is_theory_op = theory.signature.ops().iter().any(|o| o.name == *op);

    if is_theory_op {
        if args.is_empty() {
            // Nullary: need explicit type annotation
            format!("{class_name}.{op} (α := α)")
        } else {
            // Prefix application
            let args_str = args
                .iter()
                .map(|a| {
                    if a.contains(' ') {
                        format!("({a})")
                    } else {
                        a.to_string()
                    }
                })
                .collect::<Vec<_>>()
                .join(" ");
            format!("{class_name}.{op} {args_str}")
        }
    } else {
        // Unknown op — emit as-is
        if args.is_empty() {
            format!("({op})")
        } else {
            format!("({op} {})", args.join(" "))
        }
    }
}

/// Collect variable names from an axiom's LHS and RHS.
fn collect_axiom_vars(lhs: &str, rhs: &str, theory: &Theory) -> Vec<String> {
    let mut vars = Vec::new();
    collect_vars_from(lhs, theory, &mut vars);
    collect_vars_from(rhs, theory, &mut vars);
    vars
}

/// Collect variable names from two expressions.
fn collect_expr_vars_pair(a: &str, b: &str, theory: &Theory) -> Vec<String> {
    let mut vars = Vec::new();
    collect_vars_from(a, theory, &mut vars);
    collect_vars_from(b, theory, &mut vars);
    vars
}

/// Collect bare variable names from an s-expression.
fn collect_vars_from(expr: &str, theory: &Theory, vars: &mut Vec<String>) {
    let ops: Vec<&str> = theory
        .signature
        .ops()
        .iter()
        .map(|o| o.name.as_str())
        .collect();
    let bytes = expr.as_bytes();
    let mut i = 0;
    let mut after_open = false;

    while i < bytes.len() {
        match bytes[i] {
            b'(' => {
                after_open = true;
                i += 1;
            }
            b')' | b' ' | b'\t' | b'\n' | b'\r' => {
                after_open = false;
                i += 1;
            }
            b'"' => {
                // String literal — extract the name for (Var "x") patterns
                after_open = false;
                i += 1;
                let start = i;
                while i < bytes.len() && bytes[i] != b'"' {
                    if bytes[i] == b'\\' {
                        i += 1;
                    }
                    i += 1;
                }
                let name = &expr[start..i];
                if !vars.contains(&name.to_string()) {
                    vars.push(name.to_string());
                }
                if i < bytes.len() {
                    i += 1;
                }
            }
            _ => {
                let start = i;
                while i < bytes.len()
                    && !matches!(bytes[i], b'(' | b')' | b' ' | b'\t' | b'\n' | b'\r' | b'"')
                {
                    i += 1;
                }
                let token = &expr[start..i];
                if after_open {
                    after_open = false;
                } else if token.chars().next().is_some_and(|c| c.is_ascii_lowercase())
                    && !ops.contains(&token)
                    && token != "Var"
                    && !vars.contains(&token.to_string())
                {
                    vars.push(token.to_string());
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::theories::{group::group_theory, monoid::monoid_theory};

    #[test]
    fn monoid_class_definition() {
        let m = monoid_theory();
        let lean = theory_to_lean(&m);
        assert!(lean.contains("class Monoid (α : Type) where"));
        assert!(lean.contains("e : α"));
        assert!(lean.contains("mul : α → α → α"));
        assert!(lean.contains("right_identity : ∀ (a : α), Monoid.mul a (Monoid.e (α := α)) = a"));
    }

    #[test]
    fn group_class_definition() {
        let g = group_theory();
        let lean = theory_to_lean(&g);
        assert!(lean.contains("class Group (α : Type) where"));
        assert!(lean.contains("inv : α → α"));
        assert!(lean.contains("associativity"));
    }

    #[test]
    fn sexpr_var_to_lean() {
        let m = monoid_theory();
        assert_eq!(sexpr_to_lean("(Var \"a\")", &m), "a");
    }

    #[test]
    fn sexpr_nullary_to_lean() {
        let m = monoid_theory();
        assert_eq!(sexpr_to_lean("(e)", &m), "Monoid.e (α := α)");
    }

    #[test]
    fn sexpr_binary_to_lean() {
        let m = monoid_theory();
        assert_eq!(
            sexpr_to_lean("(mul (Var \"a\") (Var \"b\"))", &m),
            "Monoid.mul a b"
        );
    }

    #[test]
    fn sexpr_nested_to_lean() {
        let m = monoid_theory();
        assert_eq!(
            sexpr_to_lean("(mul (mul (Var \"a\") (Var \"b\")) (Var \"c\"))", &m),
            "Monoid.mul (Monoid.mul a b) c"
        );
    }

    #[test]
    fn equiv_class_to_theorem() {
        let m = monoid_theory();
        let classes = vec![EquivClass {
            members: vec![
                "(Var \"a\")".to_string(),
                "(mul (Var \"a\") (e))".to_string(),
                "(mul (e) (Var \"a\"))".to_string(),
            ],
        }];
        let lean = equiv_classes_to_lean(&m, &classes, "identity");
        assert!(lean.contains("theorem identity_1_1"));
        assert!(lean.contains("[Monoid α]"));
        assert!(lean.contains("a = Monoid.mul a (Monoid.e (α := α))"));
        assert!(lean.contains(":= by sorry"));
    }
}
