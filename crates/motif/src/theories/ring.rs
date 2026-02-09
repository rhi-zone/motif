use crate::signature::Signature;
use crate::theory::{Axiom, Theory};

/// Construct the theory of (non-commutative) rings: signature
/// `{zero/0, one/0, negate/1, add/2, mul/2}` with additive group axioms,
/// multiplicative identity, and distributivity.
///
/// Commutativity of addition and multiplication are deliberately omitted
/// to avoid associative-commutative blowup during saturation.
pub fn ring_theory() -> Theory {
    let mut sig = Signature::new();
    sig.add_op("zero", 0).unwrap();
    sig.add_op("one", 0).unwrap();
    sig.add_op("negate", 1).unwrap();
    sig.add_op("add", 2).unwrap();
    sig.add_op("mul", 2).unwrap();

    let axioms = vec![
        // Additive group axioms
        Axiom {
            name: "add_right_identity".to_string(),
            lhs: "(add a (zero))".to_string(),
            rhs: "a".to_string(),
        },
        Axiom {
            name: "add_left_identity".to_string(),
            lhs: "(add (zero) a)".to_string(),
            rhs: "a".to_string(),
        },
        Axiom {
            name: "add_right_inverse".to_string(),
            lhs: "(add a (negate a))".to_string(),
            rhs: "(zero)".to_string(),
        },
        Axiom {
            name: "add_left_inverse".to_string(),
            lhs: "(add (negate a) a)".to_string(),
            rhs: "(zero)".to_string(),
        },
        Axiom {
            name: "add_associativity".to_string(),
            lhs: "(add (add a b) c)".to_string(),
            rhs: "(add a (add b c))".to_string(),
        },
        // Multiplicative identity
        Axiom {
            name: "mul_left_identity".to_string(),
            lhs: "(mul (one) a)".to_string(),
            rhs: "a".to_string(),
        },
        Axiom {
            name: "mul_right_identity".to_string(),
            lhs: "(mul a (one))".to_string(),
            rhs: "a".to_string(),
        },
        // Distributivity
        Axiom {
            name: "left_distributivity".to_string(),
            lhs: "(mul a (add b c))".to_string(),
            rhs: "(add (mul a b) (mul a c))".to_string(),
        },
        Axiom {
            name: "right_distributivity".to_string(),
            lhs: "(mul (add a b) c)".to_string(),
            rhs: "(add (mul a c) (mul b c))".to_string(),
        },
    ];

    Theory {
        name: "Ring".to_string(),
        signature: sig,
        axioms,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::theory::SaturationConfig;

    fn config() -> SaturationConfig {
        SaturationConfig { iter_limit: 10 }
    }

    #[test]
    fn additive_identity() {
        let r = ring_theory();
        let result = r.equiv("(add (Var \"a\") (zero))", "(Var \"a\")", &config());
        assert!(result.unwrap());
    }

    #[test]
    fn additive_inverse() {
        let r = ring_theory();
        let result = r.equiv(
            "(add (Var \"a\") (negate (Var \"a\")))",
            "(zero)",
            &config(),
        );
        assert!(result.unwrap());
    }

    #[test]
    fn multiplicative_identity() {
        let r = ring_theory();
        let result = r.equiv("(mul (one) (Var \"a\"))", "(Var \"a\")", &config());
        assert!(result.unwrap());
    }

    #[test]
    fn left_distributivity() {
        let r = ring_theory();
        let result = r.equiv(
            "(mul (Var \"a\") (add (Var \"b\") (Var \"c\")))",
            "(add (mul (Var \"a\") (Var \"b\")) (mul (Var \"a\") (Var \"c\")))",
            &config(),
        );
        assert!(result.unwrap());
    }

    #[test]
    fn right_distributivity() {
        let r = ring_theory();
        let result = r.equiv(
            "(mul (add (Var \"a\") (Var \"b\")) (Var \"c\"))",
            "(add (mul (Var \"a\") (Var \"c\")) (mul (Var \"b\") (Var \"c\")))",
            &config(),
        );
        assert!(result.unwrap());
    }
}
