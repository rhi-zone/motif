use crate::signature::Signature;
use crate::theory::{Axiom, Theory};

/// Construct the theory of fields (equational approximation): signature
/// `{zero/0, one/0, negate/1, mulinv/1, add/2, mul/2}`.
///
/// A field is a commutative ring where every nonzero element has a
/// multiplicative inverse. Since equational logic cannot express "nonzero",
/// we use a total inverse function `mulinv` with `mul(a, mulinv(a)) = one`
/// for all elements (the "meadow" convention: `mulinv(zero) = zero`).
pub fn field_theory() -> Theory {
    let mut sig = Signature::new();
    sig.add_op("zero", 0).unwrap();
    sig.add_op("one", 0).unwrap();
    sig.add_op("negate", 1).unwrap();
    sig.add_op("mulinv", 1).unwrap();
    sig.add_op("add", 2).unwrap();
    sig.add_op("mul", 2).unwrap();

    let axioms = vec![
        // Additive abelian group
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
        Axiom {
            name: "add_commutativity".to_string(),
            lhs: "(add a b)".to_string(),
            rhs: "(add b a)".to_string(),
        },
        // Multiplicative abelian group (total inverse via meadow convention)
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
            name: "mul_right_inverse".to_string(),
            lhs: "(mul a (mulinv a))".to_string(),
            rhs: "(one)".to_string(),
        },
        Axiom {
            name: "mul_left_inverse".to_string(),
            lhs: "(mul (mulinv a) a)".to_string(),
            rhs: "(one)".to_string(),
        },
        Axiom {
            name: "mul_associativity".to_string(),
            lhs: "(mul (mul a b) c)".to_string(),
            rhs: "(mul a (mul b c))".to_string(),
        },
        Axiom {
            name: "mul_commutativity".to_string(),
            lhs: "(mul a b)".to_string(),
            rhs: "(mul b a)".to_string(),
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
        name: "Field".to_string(),
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
    fn multiplicative_inverse() {
        let f = field_theory();
        assert!(f
            .equiv("(mul (Var \"a\") (mulinv (Var \"a\")))", "(one)", &config(),)
            .unwrap());
    }

    #[test]
    fn additive_simplification() {
        let f = field_theory();
        assert!(f
            .equiv(
                "(add (negate (Var \"a\")) (add (Var \"a\") (Var \"b\")))",
                "(Var \"b\")",
                &config(),
            )
            .unwrap());
    }

    #[test]
    fn commutativity() {
        let f = field_theory();
        assert!(f
            .equiv(
                "(mul (Var \"a\") (Var \"b\"))",
                "(mul (Var \"b\") (Var \"a\"))",
                &config(),
            )
            .unwrap());
    }
}
