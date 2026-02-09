//! Automatic morphism discovery between theories.
//!
//! Given a source and target theory, enumerate arity-compatible operation
//! mappings and check which ones preserve axioms.

use crate::explore::enumerate;
use crate::morphism::Morphism;
use crate::theory::{SaturationConfig, Theory};

/// A discovered morphism with axiom preservation results.
#[derive(Debug, Clone)]
pub struct DiscoveredMorphism {
    /// The operation mapping: (source_op, target_op_or_template).
    pub mapping: Vec<(String, String)>,
    /// Per-axiom preservation results: (axiom_name, preserved).
    pub axioms: Vec<(String, bool)>,
    /// Number of preserved axioms.
    pub preserved_count: usize,
    /// Total number of axioms checked.
    pub total_count: usize,
}

/// A candidate mapping for a single source operation.
#[derive(Debug, Clone)]
enum Candidate {
    /// Simple rename to a target operation.
    Rename(String),
    /// Template expression, e.g. "(add $1 (negate $2))".
    Template(String),
}

/// Convert enumerated expression from `(Var "$1")` form to `$1` placeholder form.
fn var_to_placeholder(expr: &str) -> String {
    // Replace (Var "$N") with $N throughout
    let mut result = expr.to_string();
    let mut i = 1;
    loop {
        let var_form = format!("(Var \"${}\")", i);
        if !result.contains(&var_form) {
            break;
        }
        result = result.replace(&var_form, &format!("${}", i));
        i += 1;
    }
    result
}

/// Check that a template uses all positional args $1..$arity.
fn uses_all_args(template: &str, arity: usize) -> bool {
    (1..=arity).all(|i| template.contains(&format!("${i}")))
}

/// Check if a template is just a simple op application like `(op $1 $2)`,
/// which is already covered by rename candidates.
fn is_simple_rename(template: &str, arity: usize) -> bool {
    let trimmed = template.trim();
    if !trimmed.starts_with('(') || !trimmed.ends_with(')') {
        return false;
    }
    let inner = &trimmed[1..trimmed.len() - 1];
    let parts: Vec<&str> = inner.split_whitespace().collect();
    if parts.len() != arity + 1 {
        return false;
    }
    // Check args are exactly $1, $2, ... in order
    parts[1..]
        .iter()
        .enumerate()
        .all(|(i, p)| *p == format!("${}", i + 1))
}

/// Generate template candidates from the target signature for a given source op arity.
fn generate_template_candidates(target: &Theory, arity: usize, depth: usize) -> Vec<String> {
    if arity == 0 || depth == 0 {
        return Vec::new();
    }
    let vars: Vec<String> = (1..=arity).map(|i| format!("${i}")).collect();
    let var_refs: Vec<&str> = vars.iter().map(|s| s.as_str()).collect();
    let exprs = enumerate(&target.signature, &var_refs, depth);

    exprs
        .into_iter()
        .map(|e| var_to_placeholder(&e))
        .filter(|t| uses_all_args(t, arity) && !is_simple_rename(t, arity))
        .collect()
}

/// Discover morphisms from `source` to `target` that preserve at least one axiom.
///
/// Enumerates all arity-compatible rename mappings (each source operation maps
/// to a target operation with the same arity), plus template candidates at the
/// given depth. Returns results sorted by number of preserved axioms (descending).
///
/// `template_depth` controls template candidate generation:
/// - `0` = rename-only (current behavior)
/// - `>=1` = also try template expressions up to that depth
pub fn discover_morphisms(
    source: &Theory,
    target: &Theory,
    config: &SaturationConfig,
    template_depth: usize,
) -> Result<Vec<DiscoveredMorphism>, egglog::Error> {
    let source_ops = source.signature.ops();
    let target_ops = target.signature.ops();

    // For each source op, collect rename and template candidates
    let mut candidates_per_op: Vec<(&str, Vec<Candidate>)> = Vec::new();
    for src_op in source_ops {
        let mut candidates: Vec<Candidate> = Vec::new();

        // Rename candidates: target ops with matching arity
        for tgt_op in target_ops {
            if tgt_op.arity == src_op.arity {
                candidates.push(Candidate::Rename(tgt_op.name.clone()));
            }
        }

        // Template candidates (if depth > 0)
        if template_depth > 0 {
            let templates = generate_template_candidates(target, src_op.arity, template_depth);
            for t in templates {
                candidates.push(Candidate::Template(t));
            }
        }

        if candidates.is_empty() {
            return Ok(Vec::new());
        }
        candidates_per_op.push((src_op.name.as_str(), candidates));
    }

    // Enumerate all combinations (Cartesian product)
    let combinations = cartesian_product(&candidates_per_op);

    let mut results = Vec::new();
    for combo in &combinations {
        let mut morphism = Morphism::new("discovered");
        for (src, candidate) in combo {
            match candidate {
                Candidate::Rename(tgt) => morphism.add_rename(src, tgt),
                Candidate::Template(tmpl) => morphism.add_template(src, tmpl),
            }
        }

        let axioms = morphism.preserves_axioms(source, target, config)?;
        let preserved_count = axioms.iter().filter(|(_, p)| *p).count();
        let total_count = axioms.len();

        if preserved_count > 0 {
            results.push(DiscoveredMorphism {
                mapping: combo
                    .iter()
                    .map(|(s, c)| {
                        let target_str = match c {
                            Candidate::Rename(t) => t.clone(),
                            Candidate::Template(t) => t.clone(),
                        };
                        (s.to_string(), target_str)
                    })
                    .collect(),
                axioms,
                preserved_count,
                total_count,
            });
        }
    }

    results.sort_by(|a, b| b.preserved_count.cmp(&a.preserved_count));
    Ok(results)
}

/// Compute the Cartesian product of candidate mappings.
fn cartesian_product<'a>(
    candidates: &'a [(&'a str, Vec<Candidate>)],
) -> Vec<Vec<(&'a str, &'a Candidate)>> {
    if candidates.is_empty() {
        return vec![vec![]];
    }

    let (src_op, targets) = &candidates[0];
    let rest = cartesian_product(&candidates[1..]);

    let mut result = Vec::new();
    for tgt in targets {
        for combo in &rest {
            let mut new_combo = vec![(*src_op, tgt)];
            new_combo.extend_from_slice(combo);
            result.push(new_combo);
        }
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::signature::Signature;
    use crate::theories::{group::group_theory, monoid::monoid_theory, ring::ring_theory};
    use crate::theory::Axiom;

    fn config() -> SaturationConfig {
        SaturationConfig { iter_limit: 5 }
    }

    #[test]
    fn group_to_ring_finds_additive_morphism() {
        let group = group_theory();
        let ring = ring_theory();
        let results = discover_morphisms(&group, &ring, &config(), 0).unwrap();

        assert!(!results.is_empty());

        let best = &results[0];
        assert_eq!(best.preserved_count, best.total_count);

        let has_mapping =
            |src: &str, tgt: &str| best.mapping.iter().any(|(s, t)| s == src && t == tgt);
        assert!(has_mapping("e", "zero"));
        assert!(has_mapping("inv", "negate"));
        assert!(has_mapping("mul", "add"));
    }

    #[test]
    fn monoid_to_ring_finds_both_monoids() {
        let monoid = monoid_theory();
        let ring = ring_theory();
        let results = discover_morphisms(&monoid, &ring, &config(), 0).unwrap();

        let full_morphisms: Vec<&DiscoveredMorphism> = results
            .iter()
            .filter(|r| r.preserved_count == r.total_count)
            .collect();

        assert!(
            full_morphisms.len() >= 2,
            "expected at least 2 full morphisms, got {}",
            full_morphisms.len()
        );
    }

    #[test]
    fn incompatible_signatures_yield_no_morphisms() {
        let group = group_theory();
        let monoid = monoid_theory();
        let results = discover_morphisms(&group, &monoid, &config(), 0).unwrap();
        assert!(results.is_empty());
    }

    #[test]
    fn identical_theory_finds_identity() {
        let group = group_theory();
        let results = discover_morphisms(&group, &group, &config(), 0).unwrap();

        let identity = results
            .iter()
            .find(|r| r.mapping.iter().all(|(s, t)| s == t));
        assert!(identity.is_some());
        let id = identity.unwrap();
        assert_eq!(id.preserved_count, id.total_count);
    }

    #[test]
    fn discovers_subtraction_template() {
        // Source: theory with sub/2 and zero/0, axiom sub(a,a) = zero
        // Depth 2 needed: (add $1 (negate $2)) requires negate($2) at depth 1,
        // then add($1, negate($2)) at depth 2.
        let mut sig = Signature::new();
        sig.add_op("zero", 0).unwrap();
        sig.add_op("sub", 2).unwrap();
        let source = Theory {
            name: "SubTheory".to_string(),
            signature: sig,
            axioms: vec![Axiom {
                name: "self_sub".to_string(),
                lhs: "(sub a a)".to_string(),
                rhs: "(zero)".to_string(),
            }],
        };

        // Use a minimal group-like target (fewer ops → fewer template candidates)
        let mut tgt_sig = Signature::new();
        tgt_sig.add_op("zero", 0).unwrap();
        tgt_sig.add_op("negate", 1).unwrap();
        tgt_sig.add_op("add", 2).unwrap();
        let target = Theory {
            name: "AdditiveGroup".to_string(),
            signature: tgt_sig,
            axioms: vec![
                Axiom {
                    name: "right_identity".into(),
                    lhs: "(add a (zero))".into(),
                    rhs: "a".into(),
                },
                Axiom {
                    name: "left_identity".into(),
                    lhs: "(add (zero) a)".into(),
                    rhs: "a".into(),
                },
                Axiom {
                    name: "right_inverse".into(),
                    lhs: "(add a (negate a))".into(),
                    rhs: "(zero)".into(),
                },
                Axiom {
                    name: "left_inverse".into(),
                    lhs: "(add (negate a) a)".into(),
                    rhs: "(zero)".into(),
                },
                Axiom {
                    name: "associativity".into(),
                    lhs: "(add (add a b) c)".into(),
                    rhs: "(add a (add b c))".into(),
                },
            ],
        };

        let results = discover_morphisms(&source, &target, &config(), 2).unwrap();

        // Should find sub → (add $1 (negate $2)) among the results
        let has_template = results.iter().any(|r| {
            r.mapping
                .iter()
                .any(|(s, t)| s == "sub" && t == "(add $1 (negate $2))")
                && r.preserved_count > 0
        });
        assert!(
            has_template,
            "expected to find sub → (add $1 (negate $2)), got: {:?}",
            results.iter().map(|r| &r.mapping).collect::<Vec<_>>()
        );
    }

    #[test]
    fn rename_still_works_at_depth_1() {
        let group = group_theory();
        let ring = ring_theory();
        let results = discover_morphisms(&group, &ring, &config(), 1).unwrap();

        // The rename morphism e→zero, inv→negate, mul→add should still appear
        let has_rename = results.iter().any(|r| {
            let has = |s: &str, t: &str| r.mapping.iter().any(|(a, b)| a == s && b == t);
            has("e", "zero") && has("inv", "negate") && has("mul", "add")
        });
        assert!(
            has_rename,
            "rename morphism should still be found at depth 1"
        );
    }

    #[test]
    fn depth_0_matches_rename_only() {
        let group = group_theory();
        let ring = ring_theory();
        let results_0 = discover_morphisms(&group, &ring, &config(), 0).unwrap();

        // All mappings at depth 0 should be simple op names (no parentheses)
        for r in &results_0 {
            for (_, t) in &r.mapping {
                assert!(
                    !t.contains('('),
                    "depth 0 should only produce renames, got template: {t}"
                );
            }
        }
    }

    #[test]
    fn var_to_placeholder_converts_correctly() {
        assert_eq!(var_to_placeholder("(Var \"$1\")"), "$1");
        assert_eq!(
            var_to_placeholder("(add (Var \"$1\") (negate (Var \"$2\")))"),
            "(add $1 (negate $2))"
        );
    }

    #[test]
    fn uses_all_args_checks_correctly() {
        assert!(uses_all_args("(add $1 $2)", 2));
        assert!(!uses_all_args("(add $1 $1)", 2));
        assert!(uses_all_args("(negate $1)", 1));
        assert!(!uses_all_args("(zero)", 1));
    }

    #[test]
    fn is_simple_rename_detects_renames() {
        assert!(is_simple_rename("(add $1 $2)", 2));
        assert!(is_simple_rename("(negate $1)", 1));
        assert!(!is_simple_rename("(add $1 (negate $2))", 2));
        assert!(!is_simple_rename("(add $2 $1)", 2)); // wrong order
    }
}
