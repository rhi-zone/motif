use crate::signature::Signature;
use crate::theory::{Axiom, Theory};

/// Construct the theory of groups: signature `{e/0, inv/1, mul/2}` with
/// identity, inverse, and associativity axioms.
pub fn group_theory() -> Theory {
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
    ];

    Theory {
        name: "Group".to_string(),
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
    fn right_identity_simplification() {
        let g = group_theory();
        let result = g.equiv("(mul (Var \"a\") (e))", "(Var \"a\")", &config());
        assert!(result.unwrap());
    }

    #[test]
    fn left_identity_simplification() {
        let g = group_theory();
        let result = g.equiv("(mul (e) (Var \"a\"))", "(Var \"a\")", &config());
        assert!(result.unwrap());
    }

    #[test]
    fn right_inverse_cancellation() {
        let g = group_theory();
        let result = g.equiv("(mul (Var \"a\") (inv (Var \"a\")))", "(e)", &config());
        assert!(result.unwrap());
    }

    #[test]
    fn left_inverse_cancellation() {
        let g = group_theory();
        let result = g.equiv("(mul (inv (Var \"a\")) (Var \"a\"))", "(e)", &config());
        assert!(result.unwrap());
    }

    #[test]
    fn associativity() {
        let g = group_theory();
        let result = g.equiv(
            "(mul (mul (Var \"a\") (Var \"b\")) (Var \"c\"))",
            "(mul (Var \"a\") (mul (Var \"b\") (Var \"c\")))",
            &config(),
        );
        assert!(result.unwrap());
    }
}
