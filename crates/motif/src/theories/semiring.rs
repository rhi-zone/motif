use crate::signature::Signature;
use crate::theory::{Axiom, Theory};

/// Construct the theory of commutative semirings: signature
/// `{zero/0, one/0, add/2, mul/2}`.
///
/// A semiring is a ring without additive inverse: (S, +, 0) is a commutative
/// monoid, (S, *, 1) is a monoid, multiplication distributes over addition,
/// and zero annihilates.
pub fn semiring_theory() -> Theory {
    let mut sig = Signature::new();
    sig.add_op("zero", 0).unwrap();
    sig.add_op("one", 0).unwrap();
    sig.add_op("add", 2).unwrap();
    sig.add_op("mul", 2).unwrap();

    let axioms = vec![
        // Additive commutative monoid
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
            name: "add_associativity".to_string(),
            lhs: "(add (add a b) c)".to_string(),
            rhs: "(add a (add b c))".to_string(),
        },
        Axiom {
            name: "add_commutativity".to_string(),
            lhs: "(add a b)".to_string(),
            rhs: "(add b a)".to_string(),
        },
        // Multiplicative monoid
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
        Axiom {
            name: "mul_associativity".to_string(),
            lhs: "(mul (mul a b) c)".to_string(),
            rhs: "(mul a (mul b c))".to_string(),
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
        // Zero annihilation
        Axiom {
            name: "zero_right_annihilation".to_string(),
            lhs: "(mul a (zero))".to_string(),
            rhs: "(zero)".to_string(),
        },
        Axiom {
            name: "zero_left_annihilation".to_string(),
            lhs: "(mul (zero) a)".to_string(),
            rhs: "(zero)".to_string(),
        },
    ];

    Theory {
        name: "Semiring".to_string(),
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
    fn additive_identity() {
        let s = semiring_theory();
        assert!(s
            .equiv("(add (Var \"a\") (zero))", "(Var \"a\")", &config())
            .unwrap());
    }

    #[test]
    fn zero_annihilation() {
        let s = semiring_theory();
        assert!(s
            .equiv("(mul (Var \"a\") (zero))", "(zero)", &config())
            .unwrap());
    }

    #[test]
    fn distributivity() {
        let s = semiring_theory();
        assert!(s
            .equiv(
                "(mul (Var \"a\") (add (Var \"b\") (Var \"c\")))",
                "(add (mul (Var \"a\") (Var \"b\")) (mul (Var \"a\") (Var \"c\")))",
                &config(),
            )
            .unwrap());
    }
}
