use crate::theory::Theory;

/// Structural properties detectable from axiom patterns.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Property {
    /// `(op a (id)) = a` or `(op (id) a) = a`
    HasIdentity { op: String, identity: String },
    /// `(op a (inv a)) = id` or `(op (inv a) a) = id`
    HasInverse { op: String, inverse: String },
    /// `(op (op a b) c) = (op a (op b c))`
    Associative { op: String },
    /// `(op a b) = (op b a)`
    Commutative { op: String },
    /// `(op a a) = a`
    Idempotent { op: String },
    /// `(op1 a (op2 a b)) = a` (absorption)
    Absorbs { op1: String, op2: String },
    /// `(op1 a (op2 b c)) = (op2 (op1 a b) (op1 a c))`
    DistributesOver { op1: String, op2: String },
}

/// Algebraic structure classifications derived from properties.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Classification {
    Monoid { op: String },
    Group { op: String },
    AbelianGroup { op: String },
    Lattice { meet: String, join: String },
    Ring { add: String, mul: String },
}

/// Analyze a theory's axioms and return detected structural properties.
pub fn detect_properties(theory: &Theory) -> Vec<Property> {
    let mut props = Vec::new();

    for axiom in &theory.axioms {
        let lhs = axiom.lhs.trim();
        let rhs = axiom.rhs.trim();

        // Try both orientations: (lhs = rhs) and (rhs = lhs)
        detect_from_equation(lhs, rhs, &mut props);
        detect_from_equation(rhs, lhs, &mut props);
    }

    props.sort_by(|a, b| format!("{a:?}").cmp(&format!("{b:?}")));
    props.dedup();
    props
}

/// Derive algebraic classifications from detected properties.
pub fn classify(theory: &Theory) -> Vec<Classification> {
    let props = detect_properties(theory);
    let mut classes = Vec::new();

    // Collect all ops that have each property
    let identities: Vec<(&str, &str)> = props
        .iter()
        .filter_map(|p| match p {
            Property::HasIdentity { op, identity } => Some((op.as_str(), identity.as_str())),
            _ => None,
        })
        .collect();
    let inverses: Vec<&str> = props
        .iter()
        .filter_map(|p| match p {
            Property::HasInverse { op, .. } => Some(op.as_str()),
            _ => None,
        })
        .collect();
    let assoc: Vec<&str> = props
        .iter()
        .filter_map(|p| match p {
            Property::Associative { op } => Some(op.as_str()),
            _ => None,
        })
        .collect();
    let commut: Vec<&str> = props
        .iter()
        .filter_map(|p| match p {
            Property::Commutative { op } => Some(op.as_str()),
            _ => None,
        })
        .collect();
    let absorbs: Vec<(&str, &str)> = props
        .iter()
        .filter_map(|p| match p {
            Property::Absorbs { op1, op2 } => Some((op1.as_str(), op2.as_str())),
            _ => None,
        })
        .collect();
    let distributes: Vec<(&str, &str)> = props
        .iter()
        .filter_map(|p| match p {
            Property::DistributesOver { op1, op2 } => Some((op1.as_str(), op2.as_str())),
            _ => None,
        })
        .collect();

    // Monoid: identity + associativity
    for (op, _id) in &identities {
        if assoc.contains(op) {
            classes.push(Classification::Monoid { op: op.to_string() });
        }
    }

    // Group: monoid + inverse
    for (op, _id) in &identities {
        if assoc.contains(op) && inverses.contains(op) {
            classes.push(Classification::Group { op: op.to_string() });
        }
    }

    // Abelian group: group + commutativity
    for (op, _id) in &identities {
        if assoc.contains(op) && inverses.contains(op) && commut.contains(op) {
            classes.push(Classification::AbelianGroup { op: op.to_string() });
        }
    }

    // Lattice: two ops that absorb each other
    for (op1, op2) in &absorbs {
        if absorbs.contains(&(op2, op1)) {
            // Only emit once (alphabetical order)
            if op1 < op2 {
                classes.push(Classification::Lattice {
                    meet: op1.to_string(),
                    join: op2.to_string(),
                });
            }
        }
    }

    // Ring: two ops where one is an abelian group and the other distributes over it
    // and has identity + associativity
    for (add_op, _add_id) in &identities {
        if !assoc.contains(add_op) || !inverses.contains(add_op) {
            continue;
        }
        for (mul_op, _mul_id) in &identities {
            if mul_op == add_op || !assoc.contains(mul_op) {
                continue;
            }
            if distributes.contains(&(mul_op, add_op)) {
                classes.push(Classification::Ring {
                    add: add_op.to_string(),
                    mul: mul_op.to_string(),
                });
            }
        }
    }

    classes.sort_by(|a, b| format!("{a:?}").cmp(&format!("{b:?}")));
    classes.dedup();
    classes
}

/// Try to detect a structural property from a single equation (lhs = rhs).
fn detect_from_equation(lhs: &str, rhs: &str, props: &mut Vec<Property>) {
    detect_identity(lhs, rhs, props);
    detect_inverse(lhs, rhs, props);
    detect_associativity(lhs, rhs, props);
    detect_commutativity(lhs, rhs, props);
    detect_idempotence(lhs, rhs, props);
    detect_absorption(lhs, rhs, props);
    detect_distributivity(lhs, rhs, props);
}

/// Parse a simple s-expression into (operator, args).
/// Returns None for bare variables or malformed expressions.
fn parse_sexpr(s: &str) -> Option<(&str, Vec<&str>)> {
    let s = s.trim();
    if !s.starts_with('(') || !s.ends_with(')') {
        return None;
    }
    let inner = &s[1..s.len() - 1];

    // Find the operator (first token)
    let op_end = match inner.find(|c: char| c.is_whitespace()) {
        Some(i) => i,
        None => return Some((inner.trim(), vec![])), // Nullary like (e)
    };
    let op = inner[..op_end].trim();
    let rest = &inner[op_end..];

    // Parse args (handling nested parens)
    let mut args = Vec::new();
    let mut depth = 0;
    let mut start = None;
    for (i, ch) in rest.char_indices() {
        match ch {
            '(' => {
                if depth == 0 {
                    start = Some(i);
                }
                depth += 1;
            }
            ')' => {
                depth -= 1;
                if depth == 0 {
                    if let Some(s) = start {
                        args.push(rest[s..=i].trim());
                    }
                    start = None;
                }
            }
            c if !c.is_whitespace() && depth == 0 && start.is_none() => {
                // Start of a bare token
                start = Some(i);
            }
            c if (c.is_whitespace() || i == rest.len() - 1) && depth == 0 => {
                if let Some(s) = start {
                    let end = if c.is_whitespace() { i } else { i + 1 };
                    let token = rest[s..end].trim();
                    if !token.is_empty() {
                        args.push(token);
                    }
                    start = None;
                }
            }
            _ => {}
        }
    }
    // Catch trailing bare token
    if let Some(s) = start {
        let token = rest[s..].trim();
        if !token.is_empty() {
            args.push(token);
        }
    }

    Some((op, args))
}

/// Check if a string is a bare variable (lowercase, no parens).
fn is_var(s: &str) -> bool {
    let s = s.trim();
    !s.starts_with('(') && s.chars().next().is_some_and(|c| c.is_ascii_lowercase())
}

/// Detect: `(op a (id)) = a` or `(op (id) a) = a`
fn detect_identity(lhs: &str, rhs: &str, props: &mut Vec<Property>) {
    if !is_var(rhs) {
        return;
    }
    let Some((op, args)) = parse_sexpr(lhs) else {
        return;
    };
    if args.len() != 2 {
        return;
    }
    // (op VAR (CONST)) = VAR  where VAR matches rhs
    if args[0].trim() == rhs.trim() {
        if let Some((id, id_args)) = parse_sexpr(args[1]) {
            if id_args.is_empty() {
                props.push(Property::HasIdentity {
                    op: op.to_string(),
                    identity: id.to_string(),
                });
            }
        }
    }
    // (op (CONST) VAR) = VAR
    if args[1].trim() == rhs.trim() {
        if let Some((id, id_args)) = parse_sexpr(args[0]) {
            if id_args.is_empty() {
                props.push(Property::HasIdentity {
                    op: op.to_string(),
                    identity: id.to_string(),
                });
            }
        }
    }
}

/// Detect: `(op a (inv a)) = (id)` or `(op (inv a) a) = (id)`
fn detect_inverse(lhs: &str, rhs: &str, props: &mut Vec<Property>) {
    let Some((_rhs_op, rhs_args)) = parse_sexpr(rhs) else {
        return;
    };
    if !rhs_args.is_empty() {
        return; // RHS must be a nullary constructor (identity element)
    }
    let Some((op, args)) = parse_sexpr(lhs) else {
        return;
    };
    if args.len() != 2 {
        return;
    }
    // (op a (inv a)) = (id)
    if is_var(args[0]) {
        if let Some((inv_op, inv_args)) = parse_sexpr(args[1]) {
            if inv_args.len() == 1 && inv_args[0].trim() == args[0].trim() {
                props.push(Property::HasInverse {
                    op: op.to_string(),
                    inverse: inv_op.to_string(),
                });
            }
        }
    }
    // (op (inv a) a) = (id)
    if is_var(args[1]) {
        if let Some((inv_op, inv_args)) = parse_sexpr(args[0]) {
            if inv_args.len() == 1 && inv_args[0].trim() == args[1].trim() {
                props.push(Property::HasInverse {
                    op: op.to_string(),
                    inverse: inv_op.to_string(),
                });
            }
        }
    }
}

/// Detect: `(op (op a b) c) = (op a (op b c))`
fn detect_associativity(lhs: &str, rhs: &str, props: &mut Vec<Property>) {
    let Some((op1, args1)) = parse_sexpr(lhs) else {
        return;
    };
    let Some((op2, args2)) = parse_sexpr(rhs) else {
        return;
    };
    if op1 != op2 || args1.len() != 2 || args2.len() != 2 {
        return;
    }
    // LHS: (op (op a b) c), RHS: (op a (op b c))
    if let Some((inner_op1, inner_args1)) = parse_sexpr(args1[0]) {
        if let Some((inner_op2, inner_args2)) = parse_sexpr(args2[1]) {
            if inner_op1 == op1
                && inner_op2 == op1
                && inner_args1.len() == 2
                && inner_args2.len() == 2
                && is_var(args1[1])
                && is_var(args2[0])
                && is_var(inner_args1[0])
                && is_var(inner_args1[1])
                && inner_args1[0].trim() == args2[0].trim()
                && inner_args1[1].trim() == inner_args2[0].trim()
                && args1[1].trim() == inner_args2[1].trim()
            {
                props.push(Property::Associative {
                    op: op1.to_string(),
                });
            }
        }
    }
}

/// Detect: `(op a b) = (op b a)`
fn detect_commutativity(lhs: &str, rhs: &str, props: &mut Vec<Property>) {
    let Some((op1, args1)) = parse_sexpr(lhs) else {
        return;
    };
    let Some((op2, args2)) = parse_sexpr(rhs) else {
        return;
    };
    if op1 != op2 || args1.len() != 2 || args2.len() != 2 {
        return;
    }
    if is_var(args1[0])
        && is_var(args1[1])
        && args1[0].trim() == args2[1].trim()
        && args1[1].trim() == args2[0].trim()
    {
        props.push(Property::Commutative {
            op: op1.to_string(),
        });
    }
}

/// Detect: `(op a a) = a`
fn detect_idempotence(lhs: &str, rhs: &str, props: &mut Vec<Property>) {
    if !is_var(rhs) {
        return;
    }
    let Some((op, args)) = parse_sexpr(lhs) else {
        return;
    };
    if args.len() == 2
        && is_var(args[0])
        && args[0].trim() == args[1].trim()
        && args[0].trim() == rhs.trim()
    {
        props.push(Property::Idempotent { op: op.to_string() });
    }
}

/// Detect: `(op1 a (op2 a b)) = a` (absorption)
fn detect_absorption(lhs: &str, rhs: &str, props: &mut Vec<Property>) {
    if !is_var(rhs) {
        return;
    }
    let Some((op1, args1)) = parse_sexpr(lhs) else {
        return;
    };
    if args1.len() != 2 {
        return;
    }
    // (op1 a (op2 a b)) = a
    if is_var(args1[0]) && args1[0].trim() == rhs.trim() {
        if let Some((op2, inner_args)) = parse_sexpr(args1[1]) {
            if inner_args.len() == 2 && inner_args[0].trim() == rhs.trim() && is_var(inner_args[1])
            {
                props.push(Property::Absorbs {
                    op1: op1.to_string(),
                    op2: op2.to_string(),
                });
            }
        }
    }
}

/// Detect: `(op1 a (op2 b c)) = (op2 (op1 a b) (op1 a c))`
fn detect_distributivity(lhs: &str, rhs: &str, props: &mut Vec<Property>) {
    let Some((op1, args1)) = parse_sexpr(lhs) else {
        return;
    };
    let Some((op2, args2)) = parse_sexpr(rhs) else {
        return;
    };
    if args1.len() != 2 || args2.len() != 2 {
        return;
    }

    // LHS: (op1 a (op2 b c))
    if !is_var(args1[0]) {
        return;
    }
    let Some((inner_op, inner_args)) = parse_sexpr(args1[1]) else {
        return;
    };
    if inner_op != op2 || inner_args.len() != 2 {
        return;
    }

    // RHS: (op2 (op1 a b) (op1 a c))
    let Some((rhs_left_op, rhs_left_args)) = parse_sexpr(args2[0]) else {
        return;
    };
    let Some((rhs_right_op, rhs_right_args)) = parse_sexpr(args2[1]) else {
        return;
    };
    if rhs_left_op != op1
        || rhs_right_op != op1
        || rhs_left_args.len() != 2
        || rhs_right_args.len() != 2
    {
        return;
    }

    // Check variable consistency: a, b, c
    let a = args1[0].trim();
    let b = inner_args[0].trim();
    let c = inner_args[1].trim();
    if rhs_left_args[0].trim() == a
        && rhs_left_args[1].trim() == b
        && rhs_right_args[0].trim() == a
        && rhs_right_args[1].trim() == c
    {
        props.push(Property::DistributesOver {
            op1: op1.to_string(),
            op2: op2.to_string(),
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::theories::{
        abelian_group::abelian_group_theory, group::group_theory, lattice::lattice_theory,
        monoid::monoid_theory, ring::ring_theory,
    };

    #[test]
    fn monoid_properties() {
        let props = detect_properties(&monoid_theory());
        assert!(props.contains(&Property::HasIdentity {
            op: "mul".into(),
            identity: "e".into()
        }));
        assert!(props.contains(&Property::Associative { op: "mul".into() }));
        assert!(!props
            .iter()
            .any(|p| matches!(p, Property::HasInverse { .. })));
    }

    #[test]
    fn group_properties() {
        let props = detect_properties(&group_theory());
        assert!(props.contains(&Property::HasIdentity {
            op: "mul".into(),
            identity: "e".into()
        }));
        assert!(props.contains(&Property::HasInverse {
            op: "mul".into(),
            inverse: "inv".into()
        }));
        assert!(props.contains(&Property::Associative { op: "mul".into() }));
        assert!(!props.contains(&Property::Commutative { op: "mul".into() }));
    }

    #[test]
    fn abelian_group_properties() {
        let props = detect_properties(&abelian_group_theory());
        assert!(props.contains(&Property::Commutative { op: "mul".into() }));
    }

    #[test]
    fn lattice_properties() {
        let props = detect_properties(&lattice_theory());
        assert!(props.contains(&Property::Commutative { op: "meet".into() }));
        assert!(props.contains(&Property::Commutative { op: "join".into() }));
        assert!(props.contains(&Property::Idempotent { op: "meet".into() }));
        assert!(props.contains(&Property::Idempotent { op: "join".into() }));
        assert!(props.contains(&Property::Absorbs {
            op1: "meet".into(),
            op2: "join".into()
        }));
        assert!(props.contains(&Property::Absorbs {
            op1: "join".into(),
            op2: "meet".into()
        }));
    }

    #[test]
    fn ring_properties() {
        let props = detect_properties(&ring_theory());
        assert!(props.contains(&Property::HasIdentity {
            op: "add".into(),
            identity: "zero".into()
        }));
        assert!(props.contains(&Property::HasIdentity {
            op: "mul".into(),
            identity: "one".into()
        }));
        assert!(props.contains(&Property::HasInverse {
            op: "add".into(),
            inverse: "negate".into()
        }));
        assert!(props.contains(&Property::DistributesOver {
            op1: "mul".into(),
            op2: "add".into()
        }));
    }

    #[test]
    fn classify_monoid() {
        let classes = classify(&monoid_theory());
        assert!(classes.contains(&Classification::Monoid { op: "mul".into() }));
        assert!(!classes.contains(&Classification::Group { op: "mul".into() }));
    }

    #[test]
    fn classify_group() {
        let classes = classify(&group_theory());
        assert!(classes.contains(&Classification::Monoid { op: "mul".into() }));
        assert!(classes.contains(&Classification::Group { op: "mul".into() }));
        assert!(!classes.contains(&Classification::AbelianGroup { op: "mul".into() }));
    }

    #[test]
    fn classify_abelian_group() {
        let classes = classify(&abelian_group_theory());
        assert!(classes.contains(&Classification::AbelianGroup { op: "mul".into() }));
        assert!(classes.contains(&Classification::Group { op: "mul".into() }));
    }

    #[test]
    fn classify_lattice() {
        let classes = classify(&lattice_theory());
        assert!(
            classes.contains(&Classification::Lattice {
                meet: "join".into(),
                join: "meet".into(),
            }) || classes.contains(&Classification::Lattice {
                meet: "meet".into(),
                join: "join".into(),
            })
        );
    }

    #[test]
    fn classify_ring() {
        let classes = classify(&ring_theory());
        assert!(classes.contains(&Classification::Ring {
            add: "add".into(),
            mul: "mul".into()
        }));
        // Ring's additive part is also a group
        assert!(classes.contains(&Classification::Group { op: "add".into() }));
    }
}
