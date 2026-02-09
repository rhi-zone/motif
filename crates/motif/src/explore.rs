use crate::signature::Signature;
use crate::theory::{SaturationConfig, Theory};
use egglog::EGraph;

/// An equivalence class discovered by exploration.
#[derive(Debug, Clone)]
pub struct EquivClass {
    pub members: Vec<String>,
}

/// Enumerate all well-typed expressions over a signature up to a given depth.
///
/// - Depth 0: variables `(Var "name")` and nullary constructors `(op)`
/// - Depth d: ops applied to arguments from depth d-1
pub fn enumerate(sig: &Signature, vars: &[&str], max_depth: usize) -> Vec<String> {
    let mut current: Vec<String> = Vec::new();

    // Depth 0: atoms
    for v in vars {
        current.push(format!("(Var \"{v}\")"));
    }
    for op in sig.ops() {
        if op.arity == 0 {
            current.push(format!("({})", op.name));
        }
    }

    for _depth in 1..=max_depth {
        let prev = current.clone();
        for op in sig.ops() {
            match op.arity {
                0 => {} // already included
                1 => {
                    for arg in &prev {
                        let expr = format!("({} {})", op.name, arg);
                        if !current.contains(&expr) {
                            current.push(expr);
                        }
                    }
                }
                2 => {
                    for a in &prev {
                        for b in &prev {
                            let expr = format!("({} {} {})", op.name, a, b);
                            if !current.contains(&expr) {
                                current.push(expr);
                            }
                        }
                    }
                }
                _ => {} // higher arities not yet supported
            }
        }
    }

    current
}

/// Discover equivalence classes among a set of expressions under a theory.
///
/// Saturates once, then checks pairwise equivalence on the same e-graph.
/// Returns only non-trivial classes (more than one member).
pub fn discover_equiv_classes(
    theory: &Theory,
    exprs: &[String],
    config: &SaturationConfig,
) -> Result<Vec<EquivClass>, egglog::Error> {
    if exprs.is_empty() {
        return Ok(Vec::new());
    }

    // Build program: theory + all expressions + saturation
    let mut program = theory.to_egglog();
    theory.seed_constants(&mut program);
    for (i, expr) in exprs.iter().enumerate() {
        program.push_str(&format!("\n(let expr_{i}__ {expr})"));
    }
    program.push_str(&format!(
        "\n(run-schedule (repeat {} (run axioms)))",
        config.iter_limit
    ));

    let mut egraph = EGraph::default();
    egraph.parse_and_run_program(None, &program)?;

    // Check pairwise equivalence on the saturated e-graph
    let mut classified = vec![false; exprs.len()];
    let mut classes = Vec::new();

    for i in 0..exprs.len() {
        if classified[i] {
            continue;
        }
        let mut class = vec![i];
        classified[i] = true;

        for (j, is_classified) in classified.iter_mut().enumerate().skip(i + 1) {
            if *is_classified {
                continue;
            }
            let check = format!("(check (= expr_{i}__ expr_{j}__))");
            match egraph.parse_and_run_program(None, &check) {
                Ok(_) => {
                    class.push(j);
                    *is_classified = true;
                }
                Err(e) => {
                    let msg = e.to_string();
                    if !msg.contains("Check failed") && !msg.contains("check failed") {
                        return Err(e);
                    }
                }
            }
        }

        if class.len() > 1 {
            classes.push(EquivClass {
                members: class.iter().map(|&idx| exprs[idx].clone()).collect(),
            });
        }
    }

    Ok(classes)
}

/// Explore a theory: enumerate expressions and discover equivalence classes.
pub fn explore(
    theory: &Theory,
    vars: &[&str],
    depth: usize,
    config: &SaturationConfig,
) -> Result<Vec<EquivClass>, egglog::Error> {
    let exprs = enumerate(&theory.signature, vars, depth);
    discover_equiv_classes(theory, &exprs, config)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::theories::{group::group_theory, monoid::monoid_theory};

    fn config() -> SaturationConfig {
        SaturationConfig { iter_limit: 5 }
    }

    #[test]
    fn enumerate_monoid_depth0() {
        let m = monoid_theory();
        let exprs = enumerate(&m.signature, &["a"], 0);
        assert_eq!(exprs, vec!["(Var \"a\")", "(e)"]);
    }

    #[test]
    fn enumerate_monoid_depth1() {
        let m = monoid_theory();
        let exprs = enumerate(&m.signature, &["a"], 1);
        // depth 0: (Var "a"), (e)
        // depth 1: mul applied to pairs of depth-0
        assert!(exprs.contains(&"(mul (Var \"a\") (e))".to_string()));
        assert!(exprs.contains(&"(mul (e) (Var \"a\"))".to_string()));
        assert!(exprs.contains(&"(mul (Var \"a\") (Var \"a\"))".to_string()));
        assert!(exprs.contains(&"(mul (e) (e))".to_string()));
    }

    #[test]
    fn monoid_discovers_identity() {
        let m = monoid_theory();
        let classes = explore(&m, &["a", "b"], 1, &config()).unwrap();
        // Should discover: a = mul(a, e) = mul(e, a)
        let a_class = classes
            .iter()
            .find(|c| c.members.contains(&"(Var \"a\")".to_string()));
        assert!(a_class.is_some());
        let a_class = a_class.unwrap();
        assert!(a_class
            .members
            .contains(&"(mul (Var \"a\") (e))".to_string()));
        assert!(a_class
            .members
            .contains(&"(mul (e) (Var \"a\"))".to_string()));
    }

    #[test]
    fn group_discovers_inverse() {
        let g = group_theory();
        // mul(a, inv(a)) is depth 2 (inv(a) is depth 1)
        let classes = explore(&g, &["a"], 2, &config()).unwrap();
        // Should discover: e = mul(a, inv(a)) = mul(inv(a), a)
        let e_class = classes
            .iter()
            .find(|c| c.members.contains(&"(e)".to_string()));
        assert!(e_class.is_some());
        let e_class = e_class.unwrap();
        assert!(e_class
            .members
            .contains(&"(mul (Var \"a\") (inv (Var \"a\")))".to_string()));
    }

    #[test]
    fn group_depth2_discovers_identity_inverse() {
        let g = group_theory();
        // At depth 2, should discover inv(e) = e
        // (since mul(inv(e), e) rewrites to both inv(e) and e)
        let classes = explore(&g, &["a"], 2, &config()).unwrap();
        let e_class = classes
            .iter()
            .find(|c| c.members.contains(&"(e)".to_string()));
        assert!(e_class.is_some());
        let e_class = e_class.unwrap();
        assert!(e_class.members.contains(&"(inv (e))".to_string()));
    }
}
