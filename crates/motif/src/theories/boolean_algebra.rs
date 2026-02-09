use crate::signature::Signature;
use crate::theory::{Axiom, Theory};

/// Construct the theory of boolean algebras: signature
/// `{zero/0, one/0, complement/1, meet/2, join/2}`.
///
/// A boolean algebra is a complemented distributive lattice: (S, meet, join)
/// is a lattice with bounds zero and one, complement satisfies the
/// complementation laws, and meet distributes over join.
pub fn boolean_algebra_theory() -> Theory {
    let mut sig = Signature::new();
    sig.add_op("zero", 0).unwrap();
    sig.add_op("one", 0).unwrap();
    sig.add_op("complement", 1).unwrap();
    sig.add_op("meet", 2).unwrap();
    sig.add_op("join", 2).unwrap();

    let axioms = vec![
        // Lattice axioms
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
        // Bounded lattice: identity elements
        Axiom {
            name: "meet_identity".to_string(),
            lhs: "(meet a (one))".to_string(),
            rhs: "a".to_string(),
        },
        Axiom {
            name: "join_identity".to_string(),
            lhs: "(join a (zero))".to_string(),
            rhs: "a".to_string(),
        },
        // Complement laws
        Axiom {
            name: "meet_complement".to_string(),
            lhs: "(meet a (complement a))".to_string(),
            rhs: "(zero)".to_string(),
        },
        Axiom {
            name: "join_complement".to_string(),
            lhs: "(join a (complement a))".to_string(),
            rhs: "(one)".to_string(),
        },
        // Distributivity of meet over join
        Axiom {
            name: "meet_distributivity".to_string(),
            lhs: "(meet a (join b c))".to_string(),
            rhs: "(join (meet a b) (meet a c))".to_string(),
        },
        // Involution: complement is self-inverse.
        // Derivable from the other axioms, but the proof requires reverse
        // identity rules (a → meet(a, one)) that cause e-graph blowup,
        // so we state it explicitly.
        Axiom {
            name: "complement_involution".to_string(),
            lhs: "(complement (complement a))".to_string(),
            rhs: "a".to_string(),
        },
    ];

    Theory {
        name: "BooleanAlgebra".to_string(),
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
    fn complement_laws() {
        let b = boolean_algebra_theory();
        assert!(b
            .equiv(
                "(meet (Var \"a\") (complement (Var \"a\")))",
                "(zero)",
                &config(),
            )
            .unwrap());
        assert!(b
            .equiv(
                "(join (Var \"a\") (complement (Var \"a\")))",
                "(one)",
                &config(),
            )
            .unwrap());
    }

    #[test]
    fn absorption() {
        let b = boolean_algebra_theory();
        assert!(b
            .equiv(
                "(meet (Var \"a\") (join (Var \"a\") (Var \"b\")))",
                "(Var \"a\")",
                &config(),
            )
            .unwrap());
    }

    #[test]
    fn double_complement() {
        let b = boolean_algebra_theory();
        // complement(complement(a)) = a is derivable via complement uniqueness
        // Requires constants (one, zero) to be seeded in the e-graph
        assert!(b
            .equiv(
                "(complement (complement (Var \"a\")))",
                "(Var \"a\")",
                &config(),
            )
            .unwrap());
    }
}
