use crate::inclusion::check_inclusion;
use crate::theory::{SaturationConfig, Theory};

/// A directed edge in the theory lattice: `sub` is included in `sup`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Inclusion {
    pub sub: String,
    pub sup: String,
}

/// The theory lattice: a DAG of subtheory relationships.
#[derive(Debug, Clone)]
pub struct TheoryLattice {
    pub theories: Vec<String>,
    /// All discovered inclusion edges (including transitive).
    pub edges: Vec<Inclusion>,
}

impl TheoryLattice {
    /// Build the theory lattice from a set of named theories via pairwise
    /// inclusion checking.
    pub fn from_theories(
        theories: &[(&str, &Theory)],
        config: &SaturationConfig,
    ) -> Result<Self, egglog::Error> {
        let names: Vec<String> = theories.iter().map(|(n, _)| n.to_string()).collect();
        let mut edges = Vec::new();

        for (i, (name_a, theory_a)) in theories.iter().enumerate() {
            for (j, (name_b, theory_b)) in theories.iter().enumerate() {
                if i == j {
                    continue;
                }
                let result = check_inclusion(theory_a, theory_b, config)?;
                if result.is_included {
                    edges.push(Inclusion {
                        sub: name_a.to_string(),
                        sup: name_b.to_string(),
                    });
                }
            }
        }

        Ok(TheoryLattice {
            theories: names,
            edges,
        })
    }

    /// Theories that directly contain the given theory (supertheories).
    pub fn supertheories(&self, theory: &str) -> Vec<&str> {
        self.edges
            .iter()
            .filter(|e| e.sub == theory)
            .map(|e| e.sup.as_str())
            .collect()
    }

    /// Theories that are contained in the given theory (subtheories).
    pub fn subtheories(&self, theory: &str) -> Vec<&str> {
        self.edges
            .iter()
            .filter(|e| e.sup == theory)
            .map(|e| e.sub.as_str())
            .collect()
    }

    /// Compute the transitive reduction: remove edges that are implied
    /// by transitivity. For example, if A ⊂ B ⊂ C, remove A ⊂ C.
    pub fn reduce(&self) -> Vec<&Inclusion> {
        self.edges
            .iter()
            .filter(|edge| {
                // Check if there's an intermediate theory: sub ⊂ mid ⊂ sup
                !self.edges.iter().any(|mid_edge| {
                    mid_edge.sub == edge.sub
                        && mid_edge.sup != edge.sup
                        && self
                            .edges
                            .iter()
                            .any(|e2| e2.sub == mid_edge.sup && e2.sup == edge.sup)
                })
            })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::theories::{
        abelian_group::abelian_group_theory, boolean_algebra::boolean_algebra_theory,
        field::field_theory, group::group_theory, lattice::lattice_theory, monoid::monoid_theory,
        ring::ring_theory, semiring::semiring_theory,
    };

    fn config() -> SaturationConfig {
        SaturationConfig { iter_limit: 5 }
    }

    #[test]
    fn group_tower() {
        let monoid = monoid_theory();
        let group = group_theory();
        let abelian = abelian_group_theory();

        let lattice = TheoryLattice::from_theories(
            &[
                ("Monoid", &monoid),
                ("Group", &group),
                ("AbelianGroup", &abelian),
            ],
            &config(),
        )
        .unwrap();

        // Monoid ⊂ Group ⊂ AbelianGroup
        assert!(lattice.edges.contains(&Inclusion {
            sub: "Monoid".into(),
            sup: "Group".into()
        }));
        assert!(lattice.edges.contains(&Inclusion {
            sub: "Group".into(),
            sup: "AbelianGroup".into()
        }));
        assert!(lattice.edges.contains(&Inclusion {
            sub: "Monoid".into(),
            sup: "AbelianGroup".into()
        }));

        // Transitive reduction removes Monoid ⊂ AbelianGroup
        let reduced = lattice.reduce();
        assert!(reduced.contains(&&Inclusion {
            sub: "Monoid".into(),
            sup: "Group".into()
        }));
        assert!(reduced.contains(&&Inclusion {
            sub: "Group".into(),
            sup: "AbelianGroup".into()
        }));
        assert!(!reduced.contains(&&Inclusion {
            sub: "Monoid".into(),
            sup: "AbelianGroup".into()
        }));
    }

    #[test]
    fn ring_tower() {
        let semiring = semiring_theory();
        let ring = ring_theory();
        let field = field_theory();

        let lattice = TheoryLattice::from_theories(
            &[("Semiring", &semiring), ("Ring", &ring), ("Field", &field)],
            &config(),
        )
        .unwrap();

        assert!(lattice.edges.contains(&Inclusion {
            sub: "Semiring".into(),
            sup: "Ring".into()
        }));
        assert!(lattice.edges.contains(&Inclusion {
            sub: "Ring".into(),
            sup: "Field".into()
        }));

        let reduced = lattice.reduce();
        assert_eq!(reduced.len(), 2);
    }

    #[test]
    fn lattice_tower() {
        let lat = lattice_theory();
        let bool_alg = boolean_algebra_theory();

        let theory_lattice = TheoryLattice::from_theories(
            &[("Lattice", &lat), ("BooleanAlgebra", &bool_alg)],
            &config(),
        )
        .unwrap();

        assert!(theory_lattice.edges.contains(&Inclusion {
            sub: "Lattice".into(),
            sup: "BooleanAlgebra".into()
        }));
        // BooleanAlgebra is NOT a subtheory of Lattice
        assert!(!theory_lattice.edges.contains(&Inclusion {
            sub: "BooleanAlgebra".into(),
            sup: "Lattice".into()
        }));
    }

    #[test]
    fn cross_tower_incomparable() {
        let group = group_theory();
        let lat = lattice_theory();

        let theory_lattice =
            TheoryLattice::from_theories(&[("Group", &group), ("Lattice", &lat)], &config())
                .unwrap();

        // Different signatures — neither includes the other
        assert!(theory_lattice.edges.is_empty());
    }

    #[test]
    fn full_lattice() {
        let monoid = monoid_theory();
        let group = group_theory();
        let abelian = abelian_group_theory();
        let lat = lattice_theory();
        let bool_alg = boolean_algebra_theory();
        let semiring = semiring_theory();
        let ring = ring_theory();
        let field = field_theory();

        let theory_lattice = TheoryLattice::from_theories(
            &[
                ("Monoid", &monoid),
                ("Group", &group),
                ("AbelianGroup", &abelian),
                ("Lattice", &lat),
                ("BooleanAlgebra", &bool_alg),
                ("Semiring", &semiring),
                ("Ring", &ring),
                ("Field", &field),
            ],
            &config(),
        )
        .unwrap();

        let reduced = theory_lattice.reduce();

        // Should have exactly these direct edges:
        // Monoid → Group → AbelianGroup
        // Semiring → Ring → Field
        // Lattice → BooleanAlgebra
        assert_eq!(reduced.len(), 5);
    }
}
