use crate::signature::Signature;
use crate::theory::{Axiom, Theory};

/// Construct the theory of lattices: signature `{meet/2, join/2}` with
/// commutativity, associativity, absorption, and idempotence axioms.
///
/// A different flavor from group-like structures — no identity element,
/// no inverse, two interacting binary operations governed by absorption.
pub fn lattice_theory() -> Theory {
    let mut sig = Signature::new();
    sig.add_op("meet", 2).unwrap();
    sig.add_op("join", 2).unwrap();

    let axioms = vec![
        // Commutativity
        Axiom {
            name: "meet_commutativity".to_string(),
            lhs: "(meet a b)".to_string(),
            rhs: "(meet b a)".to_string(),
        },
        Axiom {
            name: "join_commutativity".to_string(),
            lhs: "(join a b)".to_string(),
            rhs: "(join b a)".to_string(),
        },
        // Associativity
        Axiom {
            name: "meet_associativity".to_string(),
            lhs: "(meet (meet a b) c)".to_string(),
            rhs: "(meet a (meet b c))".to_string(),
        },
        Axiom {
            name: "join_associativity".to_string(),
            lhs: "(join (join a b) c)".to_string(),
            rhs: "(join a (join b c))".to_string(),
        },
        // Absorption
        Axiom {
            name: "meet_absorption".to_string(),
            lhs: "(meet a (join a b))".to_string(),
            rhs: "a".to_string(),
        },
        Axiom {
            name: "join_absorption".to_string(),
            lhs: "(join a (meet a b))".to_string(),
            rhs: "a".to_string(),
        },
        // Idempotence
        Axiom {
            name: "meet_idempotence".to_string(),
            lhs: "(meet a a)".to_string(),
            rhs: "a".to_string(),
        },
        Axiom {
            name: "join_idempotence".to_string(),
            lhs: "(join a a)".to_string(),
            rhs: "a".to_string(),
        },
    ];

    Theory {
        name: "Lattice".to_string(),
        signature: sig,
        axioms,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::theory::SaturationConfig;

    fn config() -> SaturationConfig {
        SaturationConfig { iter_limit: 5 }
    }

    #[test]
    fn meet_idempotence() {
        let l = lattice_theory();
        assert!(l
            .equiv("(meet (Var \"a\") (Var \"a\"))", "(Var \"a\")", &config())
            .unwrap());
    }

    #[test]
    fn join_idempotence() {
        let l = lattice_theory();
        assert!(l
            .equiv("(join (Var \"a\") (Var \"a\"))", "(Var \"a\")", &config())
            .unwrap());
    }

    #[test]
    fn absorption() {
        let l = lattice_theory();
        // meet(a, join(a, b)) = a
        assert!(l
            .equiv(
                "(meet (Var \"a\") (join (Var \"a\") (Var \"b\")))",
                "(Var \"a\")",
                &config(),
            )
            .unwrap());
    }

    #[test]
    fn absorption_dual() {
        let l = lattice_theory();
        // join(a, meet(a, b)) = a
        assert!(l
            .equiv(
                "(join (Var \"a\") (meet (Var \"a\") (Var \"b\")))",
                "(Var \"a\")",
                &config(),
            )
            .unwrap());
    }

    #[test]
    fn commutativity() {
        let l = lattice_theory();
        assert!(l
            .equiv(
                "(meet (Var \"a\") (Var \"b\"))",
                "(meet (Var \"b\") (Var \"a\"))",
                &config(),
            )
            .unwrap());
    }
}
