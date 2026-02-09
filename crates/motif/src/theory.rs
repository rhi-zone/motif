use egglog::EGraph;

use crate::signature::Signature;

/// An equational axiom: `lhs = rhs` as s-expression strings.
///
/// Variables in patterns use egglog's pattern variable syntax (bare identifiers
/// that don't correspond to constructors are treated as pattern variables).
#[derive(Debug, Clone)]
pub struct Axiom {
    pub name: String,
    pub lhs: String,
    pub rhs: String,
}

impl Axiom {
    /// Compile this axiom to egglog rewrite rules.
    ///
    /// Emits bidirectional rewrites only when both sides are constructor
    /// expressions with the same free variables (e.g., associativity).
    /// When one side is a bare variable or has different free variables
    /// (e.g., identity or inverse laws), only the forward direction
    /// (`lhs→rhs`) is emitted to avoid e-graph blowup.
    pub fn to_egglog(&self) -> String {
        let lhs_vars = free_vars(&self.lhs);
        let rhs_vars = free_vars(&self.rhs);

        let same_vars =
            lhs_vars.len() == rhs_vars.len() && lhs_vars.iter().all(|v| rhs_vars.contains(v));
        let both_constructors = !is_bare_variable(&self.lhs) && !is_bare_variable(&self.rhs);

        let fwd = rewrite_or_rule(&self.lhs, &self.rhs);
        if same_vars && both_constructors {
            let rev = rewrite_or_rule(&self.rhs, &self.lhs);
            format!("{fwd}\n{rev}")
        } else {
            fwd
        }
    }
}

/// Returns true if the expression is a bare variable (no parens).
fn is_bare_variable(expr: &str) -> bool {
    !expr.trim().starts_with('(')
}

/// Collect free variable names from an s-expression. Variables are bare
/// identifiers that are not in operator position (immediately after `(`).
fn free_vars(expr: &str) -> Vec<String> {
    let mut vars = Vec::new();
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
                after_open = false;
                i += 1;
                while i < bytes.len() && bytes[i] != b'"' {
                    if bytes[i] == b'\\' {
                        i += 1;
                    }
                    i += 1;
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
                    // This is an operator, skip it
                    after_open = false;
                } else {
                    // This is in argument position — a variable
                    // (Uppercase tokens like "String" are sort names in datatype decls,
                    // but in rewrite patterns lowercase tokens are variables)
                    if token.chars().next().is_some_and(|c| c.is_ascii_lowercase())
                        && !vars.contains(&token.to_string())
                    {
                        vars.push(token.to_string());
                    }
                }
            }
        }
    }
    vars
}

/// Emit a `(rewrite lhs rhs)` if all RHS variables are grounded by the LHS,
/// or a `(rule ...)` with universe guards otherwise.
///
/// egglog requires all variables in the RHS of a rewrite to be bound by the LHS.
/// When the LHS is a bare variable or a nullary constructor that doesn't bind
/// all RHS variables, we must use a universe-guarded rule instead.
fn rewrite_or_rule(lhs: &str, rhs: &str) -> String {
    let lhs_vars = free_vars(lhs);
    let rhs_vars = free_vars(rhs);
    let has_unbound = rhs_vars.iter().any(|v| !lhs_vars.contains(v));

    if is_bare_variable(lhs) || has_unbound {
        // Must use universe-guarded rule form
        let mut all_vars = lhs_vars;
        for v in &rhs_vars {
            if !all_vars.contains(v) {
                all_vars.push(v.clone());
            }
        }
        if is_bare_variable(lhs) {
            let lhs_var = lhs.trim();
            if !all_vars.contains(&lhs_var.to_string()) {
                all_vars.push(lhs_var.to_string());
            }
        }
        let guards: Vec<String> = all_vars.iter().map(|v| format!("(universe {v})")).collect();
        format!(
            "(rule ({}) ((union {lhs} {rhs})) :ruleset axioms)",
            guards.join(" ")
        )
    } else {
        format!("(rewrite {lhs} {rhs} :ruleset axioms)")
    }
}

/// Configuration for equality saturation.
pub struct SaturationConfig {
    pub iter_limit: usize,
}

/// An algebraic theory: a signature plus equational axioms.
#[derive(Debug, Clone)]
pub struct Theory {
    pub name: String,
    pub signature: Signature,
    pub axioms: Vec<Axiom>,
}

impl Theory {
    /// Compile this theory to a complete egglog program fragment:
    /// datatype declaration + ruleset + rewrite rules.
    pub fn to_egglog(&self) -> String {
        let mut parts = vec![self.signature.to_egglog()];
        for axiom in &self.axioms {
            parts.push(axiom.to_egglog());
        }
        parts.join("\n")
    }

    /// Saturate the given expressions under this theory's axioms.
    ///
    /// Each expression is bound as a `let` in the egglog program, then
    /// saturation runs for the configured number of iterations.
    /// Returns the resulting `EGraph`.
    pub fn saturate(
        &self,
        exprs: &[(&str, &str)],
        config: &SaturationConfig,
    ) -> Result<EGraph, egglog::Error> {
        let mut program = self.to_egglog();
        for (name, expr) in exprs {
            program.push_str(&format!("\n(let {name} {expr})"));
        }
        program.push_str(&format!(
            "\n(run-schedule (repeat {} (run axioms)))",
            config.iter_limit
        ));

        let mut egraph = EGraph::default();
        egraph.parse_and_run_program(None, &program)?;
        Ok(egraph)
    }

    /// Check whether two expressions are equivalent under this theory's axioms.
    pub fn equiv(
        &self,
        expr_a: &str,
        expr_b: &str,
        config: &SaturationConfig,
    ) -> Result<bool, egglog::Error> {
        let mut program = self.to_egglog();
        program.push_str(&format!("\n(let a__ {expr_a})"));
        program.push_str(&format!("\n(let b__ {expr_b})"));
        program.push_str(&format!(
            "\n(run-schedule (repeat {} (run axioms)))",
            config.iter_limit
        ));
        program.push_str("\n(check (= a__ b__))");

        let mut egraph = EGraph::default();
        match egraph.parse_and_run_program(None, &program) {
            Ok(_) => Ok(true),
            Err(e) => {
                let msg = e.to_string();
                if msg.contains("Check failed") || msg.contains("check failed") {
                    Ok(false)
                } else {
                    Err(e)
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn simple_theory() -> Theory {
        let mut sig = Signature::new();
        sig.add_op("f", 1).unwrap();
        sig.add_op("g", 1).unwrap();
        Theory {
            name: "simple".to_string(),
            signature: sig,
            axioms: vec![Axiom {
                name: "f_g_cancel".to_string(),
                lhs: "(f (g x))".to_string(),
                rhs: "x".to_string(),
            }],
        }
    }

    #[test]
    fn axiom_forward_only_when_rhs_is_bare_var() {
        let axiom = Axiom {
            name: "test".to_string(),
            lhs: "(f x)".to_string(),
            rhs: "x".to_string(),
        };
        let egglog = axiom.to_egglog();
        // Forward direction emitted
        assert!(egglog.contains("(rewrite (f x) x :ruleset axioms)"));
        // Reverse NOT emitted — RHS is a bare variable
        assert!(!egglog.contains("union"));
        assert!(!egglog.contains("(rewrite x"));
    }

    #[test]
    fn axiom_bidirectional_same_vars() {
        let axiom = Axiom {
            name: "assoc".to_string(),
            lhs: "(f (g x))".to_string(),
            rhs: "(g (f x))".to_string(),
        };
        let egglog = axiom.to_egglog();
        // Both sides have same variables, so both directions emitted
        assert!(egglog.contains("(rewrite (f (g x)) (g (f x)) :ruleset axioms)"));
        assert!(egglog.contains("(rewrite (g (f x)) (f (g x)) :ruleset axioms)"));
    }

    #[test]
    fn axiom_forward_only_when_rhs_has_no_vars() {
        let axiom = Axiom {
            name: "inverse".to_string(),
            lhs: "(mul a (inv a))".to_string(),
            rhs: "(e)".to_string(),
        };
        let egglog = axiom.to_egglog();
        // Forward: lhs→rhs
        assert!(egglog.contains("(rewrite (mul a (inv a)) (e) :ruleset axioms)"));
        // Reverse NOT emitted: rhs has no vars, lhs has `a`
        assert!(!egglog.contains("(rewrite (e) (mul a (inv a))"));
    }

    #[test]
    fn theory_to_egglog_contains_all_parts() {
        let theory = simple_theory();
        let egglog = theory.to_egglog();
        assert!(egglog.contains("(datatype Expr"));
        assert!(egglog.contains("(ruleset axioms)"));
        assert!(egglog.contains("(relation universe (Expr))"));
        assert!(egglog.contains("(rewrite (f (g x)) x :ruleset axioms)"));
    }

    #[test]
    fn saturate_runs_without_error() {
        let theory = simple_theory();
        let config = SaturationConfig { iter_limit: 5 };
        let result = theory.saturate(&[("expr1", "(f (g (Var \"a\")))")], &config);
        assert!(result.is_ok());
    }

    #[test]
    fn equiv_detects_equal() {
        let theory = simple_theory();
        let config = SaturationConfig { iter_limit: 5 };
        let result = theory.equiv("(f (g (Var \"a\")))", "(Var \"a\")", &config);
        assert!(result.unwrap());
    }

    #[test]
    fn equiv_detects_not_equal() {
        let theory = simple_theory();
        let config = SaturationConfig { iter_limit: 5 };
        let result = theory.equiv("(Var \"a\")", "(Var \"b\")", &config);
        assert!(!result.unwrap());
    }

    #[test]
    fn equiv_nested() {
        let theory = simple_theory();
        let config = SaturationConfig { iter_limit: 10 };
        // f(g(f(g(x)))) = f(g(x)) = x via repeated cancellation
        let result = theory.equiv("(f (g (f (g (Var \"a\")))))", "(Var \"a\")", &config);
        assert!(result.unwrap());
    }
}
