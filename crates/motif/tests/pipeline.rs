use motif::diff::equiv_diff;
use motif::theories::group::group_theory;
use motif::theories::lattice::lattice_theory;
use motif::theories::monoid::monoid_theory;
use motif::theories::ring::ring_theory;
use motif::theory::SaturationConfig;
use motif::translate::Translation;

/// Full pipeline test demonstrating the cross-compilation thesis:
///
/// 1. Build ring theory and group theory
/// 2. Create ring→additive group translation (add→mul, zero→e, negate→inv)
/// 3. Take a ring expression: (add (negate a) (add a b))
/// 4. Translate it to group language: (mul (inv a) (mul a b))
/// 5. Saturate under group theory
/// 6. Verify equivalence with simplified form b
///
/// Uses (-a) + (a + b) which simplifies to b via left inverse + left identity,
/// without requiring commutativity.
#[test]
fn ring_to_group_cross_compilation() {
    let _ring = ring_theory();
    let group = group_theory();

    let mut translate = Translation::new("ring_to_additive_group", "Ring", "Group");
    translate.map_op("add", "mul");
    translate.map_op("zero", "e");
    translate.map_op("negate", "inv");

    let ring_expr = "(add (negate (Var \"a\")) (add (Var \"a\") (Var \"b\")))";
    let group_expr = translate.apply(ring_expr);
    assert_eq!(
        group_expr,
        "(mul (inv (Var \"a\")) (mul (Var \"a\") (Var \"b\")))"
    );

    let config = SaturationConfig { iter_limit: 5 };
    let result = group.equiv(&group_expr, "(Var \"b\")", &config);
    assert!(
        result.unwrap(),
        "translated ring expression should equal b under group axioms"
    );
}

/// Verify that ring axioms themselves can simplify the same expression.
#[test]
fn ring_additive_simplification() {
    let ring = ring_theory();
    let config = SaturationConfig { iter_limit: 5 };

    let result = ring.equiv(
        "(add (negate (Var \"a\")) (add (Var \"a\") (Var \"b\")))",
        "(Var \"b\")",
        &config,
    );
    assert!(
        result.unwrap(),
        "(-a) + (a + b) should simplify to b in ring theory"
    );
}

/// Translation composition: ring → group → monoid via chained forgetful functors.
#[test]
fn ring_to_monoid_via_composition() {
    let monoid = monoid_theory();

    // Ring → Group (forget multiplicative structure, keep additive)
    let mut ring_to_group = Translation::new("ring_to_group", "Ring", "Group");
    ring_to_group.map_op("add", "mul");
    ring_to_group.map_op("zero", "e");
    ring_to_group.map_op("negate", "inv");

    // Group → Monoid (forget inverse)
    let group_to_monoid = Translation::new("group_to_monoid", "Group", "Monoid");
    // identity: e→e, mul→mul (same names, no mapping needed)
    // inv is simply dropped (monoid has no inverse)

    let ring_to_monoid = ring_to_group.compose(&group_to_monoid);
    assert_eq!(ring_to_monoid.source, "Ring");
    assert_eq!(ring_to_monoid.target, "Monoid");

    // Ring expression using only additive identity: (add a (zero)) = a
    let ring_expr = "(add (Var \"a\") (zero))";
    let monoid_expr = ring_to_monoid.apply(ring_expr);
    assert_eq!(monoid_expr, "(mul (Var \"a\") (e))");

    let config = SaturationConfig { iter_limit: 5 };
    assert!(monoid.equiv(&monoid_expr, "(Var \"a\")", &config).unwrap());
}

/// Axiom preservation: ring→group preserves additive axioms but not
/// distributivity (which references mul, unmapped in group theory).
#[test]
fn axiom_preservation_ring_to_group() {
    let ring = ring_theory();
    let group = group_theory();

    let mut translate = Translation::new("ring_to_group", "Ring", "Group");
    translate.map_op("add", "mul");
    translate.map_op("zero", "e");
    translate.map_op("negate", "inv");

    let config = SaturationConfig { iter_limit: 5 };
    let results = translate.preserves_axioms(&ring, &group, &config).unwrap();

    let preserved: Vec<&str> = results
        .iter()
        .filter(|(_, p)| *p)
        .map(|(name, _)| name.as_str())
        .collect();
    let not_preserved: Vec<&str> = results
        .iter()
        .filter(|(_, p)| !*p)
        .map(|(name, _)| name.as_str())
        .collect();

    // Additive group axioms should be preserved
    assert!(preserved.contains(&"add_right_identity"));
    assert!(preserved.contains(&"add_left_identity"));
    assert!(preserved.contains(&"add_right_inverse"));
    assert!(preserved.contains(&"add_left_inverse"));
    assert!(preserved.contains(&"add_associativity"));

    // Multiplicative/distributive axioms should NOT be preserved
    // (they translate to expressions involving unmapped ring `mul`)
    assert!(not_preserved.contains(&"left_distributivity"));
    assert!(not_preserved.contains(&"right_distributivity"));
}

/// Group→Monoid forgetful functor preserves identity + associativity.
#[test]
fn axiom_preservation_group_to_monoid() {
    let group = group_theory();
    let monoid = monoid_theory();

    // e→e, mul→mul (same names), inv is dropped
    let translate = Translation::new("group_to_monoid", "Group", "Monoid");

    let config = SaturationConfig { iter_limit: 5 };
    let results = translate
        .preserves_axioms(&group, &monoid, &config)
        .unwrap();

    let preserved: Vec<&str> = results
        .iter()
        .filter(|(_, p)| *p)
        .map(|(name, _)| name.as_str())
        .collect();

    // Identity and associativity should be preserved (same op names)
    assert!(preserved.contains(&"right_identity"));
    assert!(preserved.contains(&"left_identity"));
    assert!(preserved.contains(&"associativity"));
}

/// Cross-compilation diff: translate a ring expression to both group and monoid,
/// then compare what each theory can prove. Group has inverse so it can simplify
/// (-a) + (a + b) = b, while monoid cannot.
#[test]
fn cross_compilation_diff() {
    let group = group_theory();
    let monoid = monoid_theory();

    let mut ring_to_group = Translation::new("ring_to_group", "Ring", "Group");
    ring_to_group.map_op("add", "mul");
    ring_to_group.map_op("zero", "e");
    ring_to_group.map_op("negate", "inv");

    let mut ring_to_monoid = Translation::new("ring_to_monoid", "Ring", "Monoid");
    ring_to_monoid.map_op("add", "mul");
    ring_to_monoid.map_op("zero", "e");

    let ring_expr = "(add (negate (Var \"a\")) (add (Var \"a\") (Var \"b\")))";
    let group_expr = ring_to_group.apply(ring_expr);
    let monoid_expr = ring_to_monoid.apply(ring_expr);

    let config = SaturationConfig { iter_limit: 5 };
    let diff = equiv_diff(&group_expr, &["(Var \"b\")"], &group, &monoid, &config);

    // Group simplifies to b (has inverse); monoid cannot (expression uses inv)
    assert_eq!(diff.only_first(), vec!["(Var \"b\")"]);
    assert!(diff.only_second().is_empty());

    // Sanity: the monoid expression doesn't even use inv, but it still has
    // negate (unmapped), so equiv fails in monoid too
    assert!(!monoid
        .equiv(&monoid_expr, "(Var \"b\")", &config)
        .unwrap_or(false));
}

/// Lattice theory: absorption simplification (different algebraic flavor).
#[test]
fn lattice_absorption() {
    let l = lattice_theory();
    let config = SaturationConfig { iter_limit: 5 };

    // meet(a, join(a, b)) = a
    assert!(l
        .equiv(
            "(meet (Var \"a\") (join (Var \"a\") (Var \"b\")))",
            "(Var \"a\")",
            &config,
        )
        .unwrap());

    // Double absorption: join(a, meet(a, join(a, b))) = a
    assert!(l
        .equiv(
            "(join (Var \"a\") (meet (Var \"a\") (join (Var \"a\") (Var \"b\"))))",
            "(Var \"a\")",
            &config,
        )
        .unwrap());
}
