use crate::explore::{discover_equiv_classes, enumerate, EquivClass};
use crate::theory::{SaturationConfig, Theory};

/// A conjecture: an equivalence that holds in one theory but not another.
#[derive(Debug, Clone)]
pub struct Conjecture {
    /// The equivalence class (all members are equivalent in the proving theory).
    pub equiv_class: EquivClass,
    /// Which pairs are novel (not provable in the base theory).
    /// Each pair is (member_a, member_b) from the equivalence class.
    pub novel_pairs: Vec<(String, String)>,
}

/// Discover conjectures: equivalences that hold in `theory` but not in `base`.
///
/// Enumerates expressions over `theory`'s signature, discovers equivalence
/// classes via saturation in both theories, then finds pairs equivalent in
/// `theory` but not in `base`. Uses enumeration-based checking for both
/// theories to avoid saturation incompleteness.
///
/// This answers: "what new theorems does `theory` prove that `base` can't?"
pub fn conjecture(
    base: &Theory,
    theory: &Theory,
    vars: &[&str],
    depth: usize,
    config: &SaturationConfig,
) -> Result<Vec<Conjecture>, egglog::Error> {
    // Enumerate over the theory's signature (richer than base)
    let exprs = enumerate(&theory.signature, vars, depth);
    let theory_classes = discover_equiv_classes(theory, &exprs, config)?;

    // Filter to expressions that are well-formed in base's signature
    let base_ops: Vec<&str> = base
        .signature
        .ops()
        .iter()
        .map(|op| op.name.as_str())
        .collect();
    let base_exprs: Vec<String> = exprs
        .iter()
        .filter(|e| expr_uses_only_ops(e, &base_ops))
        .cloned()
        .collect();

    // Discover classes in base theory using the same enumeration approach
    let base_classes = discover_equiv_classes(base, &base_exprs, config)?;

    // For each theory class, find pairs of base-expressible members that
    // are equivalent in the theory but NOT in the base
    let mut conjectures = Vec::new();
    for class in &theory_classes {
        let base_members: Vec<&String> = class
            .members
            .iter()
            .filter(|m| expr_uses_only_ops(m, &base_ops))
            .collect();

        if base_members.len() < 2 {
            continue;
        }

        let mut novel_pairs = Vec::new();
        for i in 0..base_members.len() {
            for j in (i + 1)..base_members.len() {
                let a = base_members[i];
                let b = base_members[j];
                if !in_same_class(a, b, &base_classes) {
                    novel_pairs.push((a.clone(), b.clone()));
                }
            }
        }

        if !novel_pairs.is_empty() {
            conjectures.push(Conjecture {
                equiv_class: class.clone(),
                novel_pairs,
            });
        }
    }

    Ok(conjectures)
}

/// Check whether two expressions are in the same equivalence class.
fn in_same_class(a: &str, b: &str, classes: &[EquivClass]) -> bool {
    classes
        .iter()
        .any(|c| c.members.iter().any(|m| m == a) && c.members.iter().any(|m| m == b))
}

/// Check whether an s-expression only uses operations from the given set.
/// `Var` is always allowed (it's the variable constructor).
fn expr_uses_only_ops(expr: &str, ops: &[&str]) -> bool {
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
                    // Operator position: must be in ops or be "Var"
                    if token != "Var" && !ops.contains(&token) {
                        return false;
                    }
                    after_open = false;
                }
            }
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::theories::{
        abelian_group::abelian_group_theory, group::group_theory, monoid::monoid_theory,
    };

    fn config() -> SaturationConfig {
        SaturationConfig { iter_limit: 10 }
    }

    #[test]
    fn expr_uses_only_ops_basic() {
        assert!(expr_uses_only_ops("(mul (Var \"a\") (e))", &["mul", "e"]));
        assert!(!expr_uses_only_ops("(inv (Var \"a\"))", &["mul", "e"]));
        assert!(expr_uses_only_ops("(Var \"a\")", &["mul"]));
    }

    #[test]
    fn identical_theories_produce_no_conjectures() {
        let monoid = monoid_theory();
        let conjectures = conjecture(&monoid, &monoid, &["a"], 1, &config()).unwrap();
        assert!(conjectures.is_empty());
    }

    #[test]
    fn group_vs_monoid_no_shared_signature_novelty() {
        // Group's novel power is via inv, which monoid can't express.
        // Within monoid's language {e, mul}, group proves the same things.
        let monoid = monoid_theory();
        let group = group_theory();
        let conjectures = conjecture(&monoid, &group, &["a"], 2, &config()).unwrap();
        assert!(conjectures.is_empty());
    }

    #[test]
    fn abelian_vs_group_discovers_commutativity() {
        // Abelian group adds commutativity. With same signature {e, inv, mul},
        // it should discover novel equivalences like mul(a, b) = mul(b, a).
        // Need 2 variables for commutativity to matter; depth 1 is sufficient.
        let group = group_theory();
        let abelian = abelian_group_theory();
        let conjectures = conjecture(&group, &abelian, &["a", "b"], 1, &config()).unwrap();

        // Should find novel pairs — commutativity-derived equivalences
        assert!(!conjectures.is_empty());

        // The classic: mul(a, b) = mul(b, a) should be novel
        let has_swap = conjectures.iter().any(|c| {
            c.novel_pairs.iter().any(|(a, b)| {
                (a.contains("(mul (Var \"a\") (Var \"b\"))")
                    && b.contains("(mul (Var \"b\") (Var \"a\"))"))
                    || (b.contains("(mul (Var \"a\") (Var \"b\"))")
                        && a.contains("(mul (Var \"b\") (Var \"a\"))"))
            })
        });
        assert!(has_swap, "should discover mul(a,b) = mul(b,a) as novel");
    }
}
