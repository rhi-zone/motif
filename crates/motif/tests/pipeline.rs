use motif::theories::group::group_theory;
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

    // Build the forgetful functor: Ring → (additive) Group
    let mut translate = Translation::new("ring_to_additive_group", "Ring", "Group");
    translate.map_op("add", "mul");
    translate.map_op("zero", "e");
    translate.map_op("negate", "inv");

    // Ring expression: (-a) + (a + b) — simplifies to b without commutativity
    let ring_expr = "(add (negate (Var \"a\")) (add (Var \"a\") (Var \"b\")))";

    // Translate to group language
    let group_expr = translate.apply(ring_expr);
    assert_eq!(
        group_expr,
        "(mul (inv (Var \"a\")) (mul (Var \"a\") (Var \"b\")))"
    );

    // Saturate under group theory and check equivalence with b
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

    // (-a) + (a + b) should equal b under ring axioms
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
