//! Automatic morphism discovery between theories.
//!
//! Given a source and target theory, enumerate arity-compatible operation
//! mappings and check which ones preserve axioms.

use crate::morphism::Morphism;
use crate::theory::{SaturationConfig, Theory};

/// A discovered morphism with axiom preservation results.
#[derive(Debug, Clone)]
pub struct DiscoveredMorphism {
    /// The operation mapping: (source_op, target_op).
    pub mapping: Vec<(String, String)>,
    /// Per-axiom preservation results: (axiom_name, preserved).
    pub axioms: Vec<(String, bool)>,
    /// Number of preserved axioms.
    pub preserved_count: usize,
    /// Total number of axioms checked.
    pub total_count: usize,
}

/// Discover morphisms from `source` to `target` that preserve at least one axiom.
///
/// Enumerates all arity-compatible rename mappings (each source operation maps
/// to a target operation with the same arity), checks axiom preservation for
/// each, and returns results sorted by number of preserved axioms (descending).
pub fn discover_morphisms(
    source: &Theory,
    target: &Theory,
    config: &SaturationConfig,
) -> Result<Vec<DiscoveredMorphism>, egglog::Error> {
    let source_ops = source.signature.ops();
    let target_ops = target.signature.ops();

    // For each source op, find target ops with matching arity
    let mut candidates_per_op: Vec<(&str, Vec<&str>)> = Vec::new();
    for src_op in source_ops {
        let matches: Vec<&str> = target_ops
            .iter()
            .filter(|t| t.arity == src_op.arity)
            .map(|t| t.name.as_str())
            .collect();
        if matches.is_empty() {
            // No compatible target op — no valid morphisms exist
            return Ok(Vec::new());
        }
        candidates_per_op.push((src_op.name.as_str(), matches));
    }

    // Enumerate all combinations (Cartesian product)
    let combinations = cartesian_product(&candidates_per_op);

    let mut results = Vec::new();
    for combo in &combinations {
        // Build a morphism from this mapping
        let mut morphism = Morphism::new("discovered");
        for (src, tgt) in combo {
            morphism.add_rename(src, tgt);
        }

        // Check axiom preservation
        let axioms = morphism.preserves_axioms(source, target, config)?;
        let preserved_count = axioms.iter().filter(|(_, p)| *p).count();
        let total_count = axioms.len();

        if preserved_count > 0 {
            results.push(DiscoveredMorphism {
                mapping: combo
                    .iter()
                    .map(|(s, t)| (s.to_string(), t.to_string()))
                    .collect(),
                axioms,
                preserved_count,
                total_count,
            });
        }
    }

    // Sort by preserved count descending
    results.sort_by(|a, b| b.preserved_count.cmp(&a.preserved_count));
    Ok(results)
}

/// Compute the Cartesian product of candidate mappings.
///
/// Input: `[("e", ["zero", "one"]), ("mul", ["add", "mul"])]`
/// Output: `[[("e","zero"), ("mul","add")], [("e","zero"), ("mul","mul")], ...]`
fn cartesian_product<'a>(candidates: &[(&'a str, Vec<&'a str>)]) -> Vec<Vec<(&'a str, &'a str)>> {
    if candidates.is_empty() {
        return vec![vec![]];
    }

    let (src_op, targets) = &candidates[0];
    let rest = cartesian_product(&candidates[1..]);

    let mut result = Vec::new();
    for &tgt in targets {
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
    use crate::theories::{group::group_theory, monoid::monoid_theory, ring::ring_theory};

    fn config() -> SaturationConfig {
        SaturationConfig { iter_limit: 5 }
    }

    #[test]
    fn group_to_ring_finds_additive_morphism() {
        // Group {e/0, inv/1, mul/2} → Ring {zero/0, one/0, negate/1, add/2, mul/2}
        // Should find: e→zero, inv→negate, mul→add (preserves all group axioms)
        let group = group_theory();
        let ring = ring_theory();
        let results = discover_morphisms(&group, &ring, &config()).unwrap();

        assert!(!results.is_empty());

        // The best morphism should preserve all 5 group axioms
        let best = &results[0];
        assert_eq!(best.preserved_count, best.total_count);

        // Check the mapping is e→zero, inv→negate, mul→add
        let has_mapping =
            |src: &str, tgt: &str| best.mapping.iter().any(|(s, t)| s == src && t == tgt);
        assert!(has_mapping("e", "zero"));
        assert!(has_mapping("inv", "negate"));
        assert!(has_mapping("mul", "add"));
    }

    #[test]
    fn monoid_to_ring_finds_both_monoids() {
        // Monoid {e/0, mul/2} → Ring {zero/0, one/0, add/2, mul/2, ...}
        // Should find two full morphisms:
        //   e→zero, mul→add (additive monoid)
        //   e→one, mul→mul (multiplicative monoid)
        let monoid = monoid_theory();
        let ring = ring_theory();
        let results = discover_morphisms(&monoid, &ring, &config()).unwrap();

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
        // Group {e/0, inv/1, mul/2} to a theory with no unary ops → no morphisms
        let group = group_theory();
        let monoid = monoid_theory(); // no unary ops
        let results = discover_morphisms(&group, &monoid, &config()).unwrap();
        assert!(results.is_empty());
    }

    #[test]
    fn identical_theory_finds_identity() {
        let group = group_theory();
        let results = discover_morphisms(&group, &group, &config()).unwrap();

        // The identity morphism (e→e, inv→inv, mul→mul) should preserve all axioms
        let identity = results
            .iter()
            .find(|r| r.mapping.iter().all(|(s, t)| s == t));
        assert!(identity.is_some());
        let id = identity.unwrap();
        assert_eq!(id.preserved_count, id.total_count);
    }
}
