use crate::theory::{SaturationConfig, Theory};

/// Equivalence comparison for a single candidate expression.
#[derive(Debug, Clone)]
pub struct CandidateResult {
    pub candidate: String,
    pub in_first: bool,
    pub in_second: bool,
}

/// Result of comparing equivalences between two theories.
#[derive(Debug, Clone)]
pub struct EquivDiff {
    pub expr: String,
    pub results: Vec<CandidateResult>,
}

impl EquivDiff {
    /// Candidates equivalent only in the first theory.
    pub fn only_first(&self) -> Vec<&str> {
        self.results
            .iter()
            .filter(|r| r.in_first && !r.in_second)
            .map(|r| r.candidate.as_str())
            .collect()
    }

    /// Candidates equivalent only in the second theory.
    pub fn only_second(&self) -> Vec<&str> {
        self.results
            .iter()
            .filter(|r| !r.in_first && r.in_second)
            .map(|r| r.candidate.as_str())
            .collect()
    }

    /// Candidates equivalent in both theories.
    pub fn in_both(&self) -> Vec<&str> {
        self.results
            .iter()
            .filter(|r| r.in_first && r.in_second)
            .map(|r| r.candidate.as_str())
            .collect()
    }
}

/// Compare equivalences of an expression with candidates across two theories.
///
/// For each candidate, checks whether `expr` is equivalent to that candidate
/// under each theory. Expressions that use operations not in a theory's
/// signature are treated as not equivalent (errors become `false`).
pub fn equiv_diff(
    expr: &str,
    candidates: &[&str],
    first: &Theory,
    second: &Theory,
    config: &SaturationConfig,
) -> EquivDiff {
    let results = candidates
        .iter()
        .map(|&candidate| {
            let in_first = first.equiv(expr, candidate, config).unwrap_or(false);
            let in_second = second.equiv(expr, candidate, config).unwrap_or(false);
            CandidateResult {
                candidate: candidate.to_string(),
                in_first,
                in_second,
            }
        })
        .collect();
    EquivDiff {
        expr: expr.to_string(),
        results,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::theories::{
        abelian_group::abelian_group_theory, group::group_theory, monoid::monoid_theory,
    };

    fn config() -> SaturationConfig {
        SaturationConfig { iter_limit: 5 }
    }

    #[test]
    fn group_vs_monoid_shared_equivalences() {
        let group = group_theory();
        let monoid = monoid_theory();

        // Both theories agree: (mul a (e)) = a
        let diff = equiv_diff(
            "(mul (Var \"a\") (e))",
            &["(Var \"a\")", "(mul (e) (Var \"a\"))"],
            &group,
            &monoid,
            &config(),
        );
        assert_eq!(diff.in_both(), vec!["(Var \"a\")", "(mul (e) (Var \"a\"))"]);
        assert!(diff.only_first().is_empty());
        assert!(diff.only_second().is_empty());
    }

    #[test]
    fn group_vs_monoid_inverse_only_in_group() {
        let group = group_theory();
        let monoid = monoid_theory();

        // Group can simplify inv(a) * (a * b) = b, monoid cannot (no inv)
        let diff = equiv_diff(
            "(mul (inv (Var \"a\")) (mul (Var \"a\") (Var \"b\")))",
            &["(Var \"b\")"],
            &group,
            &monoid,
            &config(),
        );
        assert_eq!(diff.only_first(), vec!["(Var \"b\")"]);
        assert!(diff.only_second().is_empty());
        assert!(diff.in_both().is_empty());
    }

    #[test]
    fn abelian_vs_group_commutativity() {
        let abelian = abelian_group_theory();
        let group = group_theory();

        // Abelian group proves mul(a, b) = mul(b, a), plain group does not
        let diff = equiv_diff(
            "(mul (Var \"a\") (Var \"b\"))",
            &["(mul (Var \"b\") (Var \"a\"))"],
            &abelian,
            &group,
            &config(),
        );
        assert_eq!(diff.only_first(), vec!["(mul (Var \"b\") (Var \"a\"))"]);
        assert!(diff.only_second().is_empty());
    }
}
