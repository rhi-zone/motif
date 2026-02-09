use crate::signature::Signature;
use crate::theory::{Axiom, Theory};

/// Construct the theory of monoids: signature `{e/0, mul/2}` with
/// identity and associativity axioms. No inverse.
pub fn monoid_theory() -> Theory {
    let mut sig = Signature::new();
    sig.add_op("e", 0).unwrap();
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
            name: "associativity".to_string(),
            lhs: "(mul (mul a b) c)".to_string(),
            rhs: "(mul a (mul b c))".to_string(),
        },
    ];

    Theory {
        name: "Monoid".to_string(),
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
    fn right_identity() {
        let m = monoid_theory();
        assert!(m
            .equiv("(mul (Var \"a\") (e))", "(Var \"a\")", &config())
            .unwrap());
    }

    #[test]
    fn left_identity() {
        let m = monoid_theory();
        assert!(m
            .equiv("(mul (e) (Var \"a\"))", "(Var \"a\")", &config())
            .unwrap());
    }

    #[test]
    fn associativity() {
        let m = monoid_theory();
        assert!(m
            .equiv(
                "(mul (mul (Var \"a\") (Var \"b\")) (Var \"c\"))",
                "(mul (Var \"a\") (mul (Var \"b\") (Var \"c\")))",
                &config(),
            )
            .unwrap());
    }

    #[test]
    fn identity_chain() {
        let m = monoid_theory();
        // e * (e * a) = a
        assert!(m
            .equiv("(mul (e) (mul (e) (Var \"a\")))", "(Var \"a\")", &config())
            .unwrap());
    }
}
