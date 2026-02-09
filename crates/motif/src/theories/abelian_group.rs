use crate::signature::Signature;
use crate::theory::{Axiom, Theory};

/// Construct the theory of abelian groups: signature `{e/0, inv/1, mul/2}`
/// with identity, inverse, associativity, and commutativity axioms.
///
/// Commutativity + associativity (AC) can cause e-graph blowup with high
/// iteration limits. Keep limits low (5-10) for tests.
pub fn abelian_group_theory() -> Theory {
    let mut sig = Signature::new();
    sig.add_op("e", 0).unwrap();
    sig.add_op("inv", 1).unwrap();
    sig.add_op("mul", 2).unwrap();

    let axioms = vec![
        Axiom {
            name: "right_identity".to_string(),
            lhs: "(mul a (e))".to_string(),
            rhs: "a".to_string(),
        },
        Axiom {
            name: "left_identity".to_string(),
            lhs: "(mul (e) a)".to_string(),
            rhs: "a".to_string(),
        },
        Axiom {
            name: "right_inverse".to_string(),
            lhs: "(mul a (inv a))".to_string(),
            rhs: "(e)".to_string(),
        },
        Axiom {
            name: "left_inverse".to_string(),
            lhs: "(mul (inv a) a)".to_string(),
            rhs: "(e)".to_string(),
        },
        Axiom {
            name: "associativity".to_string(),
            lhs: "(mul (mul a b) c)".to_string(),
            rhs: "(mul a (mul b c))".to_string(),
        },
        Axiom {
            name: "commutativity".to_string(),
            lhs: "(mul a b)".to_string(),
            rhs: "(mul b a)".to_string(),
        },
    ];

    Theory {
        name: "AbelianGroup".to_string(),
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
    fn commutativity() {
        let g = abelian_group_theory();
        assert!(g
            .equiv(
                "(mul (Var \"a\") (Var \"b\"))",
                "(mul (Var \"b\") (Var \"a\"))",
                &config(),
            )
            .unwrap());
    }

    #[test]
    fn inverse_cancellation_via_commutativity() {
        let g = abelian_group_theory();
        // a * b * inv(a) = b (requires commutativity — doesn't hold in non-abelian groups)
        assert!(g
            .equiv(
                "(mul (mul (Var \"a\") (Var \"b\")) (inv (Var \"a\")))",
                "(Var \"b\")",
                &config(),
            )
            .unwrap());
    }

    #[test]
    fn inverse_of_product() {
        let g = abelian_group_theory();
        // inv(a) * inv(b) = inv(b * a) in any group, = inv(a * b) in abelian group
        // Test: inv(a) * inv(b) * (a * b) = e
        assert!(g
            .equiv(
                "(mul (mul (inv (Var \"a\")) (inv (Var \"b\"))) (mul (Var \"a\") (Var \"b\")))",
                "(e)",
                &config(),
            )
            .unwrap());
    }
}
