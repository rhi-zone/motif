use crate::theory::{SaturationConfig, Theory};
use crate::translate::Translation;

/// Result of checking theory inclusion.
#[derive(Debug, Clone)]
pub struct InclusionResult {
    /// Whether all axioms of the candidate are provable in the target.
    pub is_included: bool,
    /// Per-axiom results: (axiom_name, provable_in_target).
    pub axioms: Vec<(String, bool)>,
    /// Signature compatibility: whether all ops in the candidate exist in the target.
    pub signature_compatible: bool,
}

/// Check whether theory `sub` is included in theory `sup`: every axiom of
/// `sub` is provable under `sup`'s axioms, and every operation in `sub`'s
/// signature exists in `sup`'s signature with the same arity.
pub fn check_inclusion(
    sub: &Theory,
    sup: &Theory,
    config: &SaturationConfig,
) -> Result<InclusionResult, egglog::Error> {
    // Check signature compatibility
    let signature_compatible = sub.signature.ops().iter().all(|sub_op| {
        sup.signature
            .ops()
            .iter()
            .any(|sup_op| sup_op.name == sub_op.name && sup_op.arity == sub_op.arity)
    });

    if !signature_compatible {
        return Ok(InclusionResult {
            is_included: false,
            axioms: sub.axioms.iter().map(|a| (a.name.clone(), false)).collect(),
            signature_compatible,
        });
    }

    // Use identity translation (no renames) to check axiom preservation
    let identity = Translation::new("inclusion_check", &sub.name, &sup.name);
    let axioms = identity.preserves_axioms(sub, sup, config)?;
    let is_included = axioms.iter().all(|(_, preserved)| *preserved);

    Ok(InclusionResult {
        is_included,
        axioms,
        signature_compatible,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::theories::{
        abelian_group::abelian_group_theory, group::group_theory, monoid::monoid_theory,
        ring::ring_theory,
    };

    fn config() -> SaturationConfig {
        SaturationConfig { iter_limit: 5 }
    }

    #[test]
    fn monoid_included_in_group() {
        let result = check_inclusion(&monoid_theory(), &group_theory(), &config()).unwrap();
        assert!(result.signature_compatible);
        assert!(result.is_included);
    }

    #[test]
    fn group_included_in_abelian_group() {
        let result = check_inclusion(&group_theory(), &abelian_group_theory(), &config()).unwrap();
        assert!(result.signature_compatible);
        assert!(result.is_included);
    }

    #[test]
    fn monoid_included_in_abelian_group() {
        let result = check_inclusion(&monoid_theory(), &abelian_group_theory(), &config()).unwrap();
        assert!(result.signature_compatible);
        assert!(result.is_included);
    }

    #[test]
    fn group_not_included_in_monoid() {
        let result = check_inclusion(&group_theory(), &monoid_theory(), &config()).unwrap();
        // Group signature has inv which monoid doesn't
        assert!(!result.signature_compatible);
        assert!(!result.is_included);
    }

    #[test]
    fn abelian_group_not_included_in_group() {
        let result = check_inclusion(&abelian_group_theory(), &group_theory(), &config()).unwrap();
        assert!(result.signature_compatible);
        // Commutativity is not provable in plain group theory
        assert!(!result.is_included);
        let not_preserved: Vec<&str> = result
            .axioms
            .iter()
            .filter(|(_, p)| !*p)
            .map(|(n, _)| n.as_str())
            .collect();
        assert!(not_preserved.contains(&"commutativity"));
    }

    #[test]
    fn ring_not_included_in_group() {
        let result = check_inclusion(&ring_theory(), &group_theory(), &config()).unwrap();
        // Ring has ops (add, zero, negate, mul, one) not all in group (e, inv, mul)
        assert!(!result.signature_compatible);
    }
}
