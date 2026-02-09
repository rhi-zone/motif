//! Automatic morphism discovery between theories.
//!
//! Given a source and target theory, enumerate arity-compatible operation
//! mappings and check which ones preserve axioms.
//!
//! All candidate-translated axiom expressions are added to a single shared
//! e-graph and saturated once; per-axiom equivalence checks are then O(1)
//! lookups. The shared graph is strictly more powerful than individual
//! per-check e-graphs because more intermediate terms enable more rewrites.
//! Per-axiom decomposition keeps the expression count manageable (each
//! axiom's Cartesian product is over only the 1-3 ops it references).

use std::collections::{HashMap, HashSet};

use egglog::EGraph;

use crate::explore::enumerate;
use crate::morphism::Morphism;
use crate::theory::{SaturationConfig, Theory};
use crate::translate::pattern_to_expr;

/// A discovered morphism with axiom preservation results.
#[derive(Debug, Clone)]
pub struct DiscoveredMorphism {
    /// The operation mapping: (source_op, target_op_or_template).
    pub mapping: Vec<(String, String)>,
    /// Per-axiom preservation results: (axiom_name, preserved).
    pub axioms: Vec<(String, bool)>,
    /// Number of preserved axioms.
    pub preserved_count: usize,
    /// Total number of axioms checked.
    pub total_count: usize,
}

/// A candidate mapping for a single source operation.
#[derive(Debug, Clone)]
enum Candidate {
    /// Simple rename to a target operation.
    Rename(String),
    /// Template expression, e.g. "(add $1 (negate $2))".
    Template(String),
}

/// Convert enumerated expression from `(Var "$1")` form to `$1` placeholder form.
///
/// Replaces all `(Var "$N")` patterns regardless of which N values are present,
/// so expressions that use only a subset of args (e.g., `$2` without `$1`) are
/// handled correctly.
fn var_to_placeholder(expr: &str, arity: usize) -> String {
    let mut result = expr.to_string();
    for i in 1..=arity {
        let var_form = format!("(Var \"${}\")", i);
        result = result.replace(&var_form, &format!("${}", i));
    }
    result
}

/// Check if a template is just a simple op application like `(op $1 $2)`,
/// which is already covered by rename candidates.
fn is_simple_rename(template: &str, arity: usize) -> bool {
    let trimmed = template.trim();
    if !trimmed.starts_with('(') || !trimmed.ends_with(')') {
        return false;
    }
    let inner = &trimmed[1..trimmed.len() - 1];
    let parts: Vec<&str> = inner.split_whitespace().collect();
    if parts.len() != arity + 1 {
        return false;
    }
    parts[1..]
        .iter()
        .enumerate()
        .all(|(i, p)| *p == format!("${}", i + 1))
}

/// Generate template candidates from the target signature for a given source op arity.
///
/// Always includes projections (`$1`, `$2`) and constant expressions (`(zero)`,
/// `(one)`) — these represent valid morphism interpretations that were previously
/// rejected. For compound templates (using both ops and variables), requires all
/// positional args to avoid exponential blowup in distributive theories.
fn generate_template_candidates(target: &Theory, arity: usize, depth: usize) -> Vec<String> {
    if arity == 0 || depth == 0 {
        return Vec::new();
    }
    let vars: Vec<String> = (1..=arity).map(|i| format!("${i}")).collect();
    let var_refs: Vec<&str> = vars.iter().map(|s| s.as_str()).collect();
    let exprs = enumerate(&target.signature, &var_refs, depth);

    let nullary_ops: Vec<String> = target
        .signature
        .ops()
        .iter()
        .filter(|op| op.arity == 0)
        .map(|op| format!("({})", op.name))
        .collect();

    exprs
        .into_iter()
        .map(|e| var_to_placeholder(&e, arity))
        .filter(|t| {
            if is_simple_rename(t, arity) {
                return false;
            }
            // Projections (bare $N): always kept.
            if !t.contains('(') {
                return true;
            }
            let has_any_arg = (1..=arity).any(|i| t.contains(&format!("${i}")));
            if !has_any_arg {
                // Pure constant: keep only nullary constructors (e.g., (zero)).
                // Compound constants like (add (zero) (one)) are redundant with
                // simpler constants under saturation.
                return nullary_ops.contains(&t.to_string());
            }
            // Compound with variables: require all positional args to limit
            // candidate explosion in distributive theories.
            (1..=arity).all(|i| t.contains(&format!("${i}")))
        })
        .collect()
}

/// Find which source op indices appear in an axiom expression.
fn extract_op_indices(expr: &str, src_op_names: &[&str]) -> Vec<usize> {
    src_op_names
        .iter()
        .enumerate()
        .filter(|(_, name)| {
            let with_space = format!("({name} ");
            let as_nullary = format!("({name})");
            expr.contains(&with_space) || expr.contains(&as_nullary)
        })
        .map(|(i, _)| i)
        .collect()
}

/// Cartesian product of index ranges.
fn index_cartesian(sizes: &[usize]) -> Vec<Vec<usize>> {
    if sizes.is_empty() {
        return vec![vec![]];
    }
    let rest = index_cartesian(&sizes[1..]);
    let mut result = Vec::new();
    for i in 0..sizes[0] {
        for combo in &rest {
            let mut new = vec![i];
            new.extend_from_slice(combo);
            result.push(new);
        }
    }
    result
}

/// Try to merge two partial op→candidate assignments. Returns None if they conflict.
fn try_merge(
    a: &HashMap<usize, usize>,
    b: &HashMap<usize, usize>,
) -> Option<HashMap<usize, usize>> {
    let mut merged = a.clone();
    for (&op, &candidate) in b {
        if let Some(&existing) = merged.get(&op) {
            if existing != candidate {
                return None;
            }
        } else {
            merged.insert(op, candidate);
        }
    }
    Some(merged)
}

/// Join two lists of partial assignments, keeping only compatible pairs.
fn join_partial(
    a: &[HashMap<usize, usize>],
    b: &[HashMap<usize, usize>],
) -> Vec<HashMap<usize, usize>> {
    let mut result = Vec::new();
    for pa in a {
        for pb in b {
            if let Some(merged) = try_merge(pa, pb) {
                if !result.contains(&merged) {
                    result.push(merged);
                }
            }
        }
    }
    result
}

/// Per-axiom check data: which ops are involved, what combos exist, their
/// translated expressions, and which combos passed the equivalence check.
struct AxiomCheckData {
    op_indices: Vec<usize>,
    combos: Vec<Vec<usize>>,
    viable: Vec<usize>, // indices into combos that passed
}

/// Discover morphisms from `source` to `target` that preserve at least one axiom.
///
/// Builds a single shared e-graph with all candidate-translated axiom
/// expressions, saturates once, then checks equivalences as O(1) lookups.
/// Per-axiom decomposition ensures expression count scales with the sum of
/// per-axiom candidate products, not the full Cartesian product.
///
/// `template_depth` controls template candidate generation:
/// - `0` = rename-only
/// - `>=1` = also try template expressions up to that depth
pub fn discover_morphisms(
    source: &Theory,
    target: &Theory,
    config: &SaturationConfig,
    template_depth: usize,
) -> Result<Vec<DiscoveredMorphism>, egglog::Error> {
    let source_ops = source.signature.ops();
    let target_ops = target.signature.ops();

    // 1. Generate candidates per source op
    let mut candidates_per_op: Vec<(&str, Vec<Candidate>)> = Vec::new();
    for src_op in source_ops {
        let mut candidates: Vec<Candidate> = Vec::new();
        for tgt_op in target_ops {
            if tgt_op.arity == src_op.arity {
                candidates.push(Candidate::Rename(tgt_op.name.clone()));
            }
        }
        if template_depth > 0 {
            for t in generate_template_candidates(target, src_op.arity, template_depth) {
                candidates.push(Candidate::Template(t));
            }
        }
        if candidates.is_empty() {
            return Ok(Vec::new());
        }
        candidates_per_op.push((src_op.name.as_str(), candidates));
    }

    let constructors: Vec<&str> = target_ops.iter().map(|op| op.name.as_str()).collect();
    let src_op_names: Vec<&str> = candidates_per_op.iter().map(|(name, _)| *name).collect();

    // 2. For each axiom, find referenced ops, enumerate per-axiom combos,
    //    translate expressions, and collect them for the shared e-graph.
    let mut all_exprs: HashMap<String, usize> = HashMap::new(); // expr → index

    struct AxiomComboEntry {
        op_indices: Vec<usize>,
        checks: Vec<(Vec<usize>, usize, usize)>, // (combo, lhs_idx, rhs_idx)
    }
    let mut axiom_combo_data: Vec<AxiomComboEntry> = Vec::new();

    let intern_expr = |expr: String, map: &mut HashMap<String, usize>| -> usize {
        let next = map.len();
        *map.entry(expr).or_insert(next)
    };

    for axiom in &source.axioms {
        let mut op_indices: Vec<usize> = extract_op_indices(&axiom.lhs, &src_op_names);
        for idx in extract_op_indices(&axiom.rhs, &src_op_names) {
            if !op_indices.contains(&idx) {
                op_indices.push(idx);
            }
        }
        op_indices.sort();

        let sizes: Vec<usize> = op_indices
            .iter()
            .map(|&i| candidates_per_op[i].1.len())
            .collect();
        let combos = index_cartesian(&sizes);

        let mut combo_checks = Vec::new();
        for combo in &combos {
            let mut morphism = Morphism::new("check");
            for (pos, &op_idx) in op_indices.iter().enumerate() {
                let (op_name, candidates) = &candidates_per_op[op_idx];
                match &candidates[combo[pos]] {
                    Candidate::Rename(t) => morphism.add_rename(op_name, t),
                    Candidate::Template(t) => morphism.add_template(op_name, t),
                }
            }
            let lhs = pattern_to_expr(&morphism.apply(&axiom.lhs), &constructors);
            let rhs = pattern_to_expr(&morphism.apply(&axiom.rhs), &constructors);
            let li = intern_expr(lhs, &mut all_exprs);
            let ri = intern_expr(rhs, &mut all_exprs);
            combo_checks.push((combo.clone(), li, ri));
        }

        axiom_combo_data.push(AxiomComboEntry {
            op_indices,
            checks: combo_checks,
        });
    }

    // 3. Check axiom combos. Use a shared e-graph when expression count is
    //    small (more intermediate terms → more complete). Fall back to
    //    per-combo e-graphs for large counts to avoid saturation blowup
    //    with distributive theories.
    let base_program = {
        let mut p = target.to_egglog();
        target.seed_constants(&mut p);
        p
    };

    let mut idx_to_expr: Vec<&str> = vec![""; all_exprs.len()];
    for (expr, &idx) in &all_exprs {
        idx_to_expr[idx] = expr;
    }

    let use_shared = all_exprs.len() <= 50;

    let mut shared_egraph = if use_shared {
        let mut program = base_program.clone();
        for (idx, expr) in idx_to_expr.iter().enumerate() {
            program.push_str(&format!("\n(let expr_{idx}__ {expr})"));
        }
        program.push_str(&format!(
            "\n(run-schedule (repeat {} (run axioms)))",
            config.iter_limit
        ));
        let mut egraph = EGraph::default();
        egraph.parse_and_run_program(None, &program)?;
        Some(egraph)
    } else {
        None
    };

    let mut axiom_checks: Vec<AxiomCheckData> = Vec::new();
    for entry in &axiom_combo_data {
        let mut viable = Vec::new();
        let combos: Vec<Vec<usize>> = entry.checks.iter().map(|(c, _, _)| c.clone()).collect();

        for (combo_idx, (_, li, ri)) in entry.checks.iter().enumerate() {
            let is_equiv = if let Some(ref mut egraph) = shared_egraph {
                let check_cmd = format!("(check (= expr_{}__ expr_{}__))", li, ri);
                match egraph.parse_and_run_program(None, &check_cmd) {
                    Ok(_) => true,
                    Err(e) => {
                        let msg = e.to_string();
                        if !msg.contains("Check failed") && !msg.contains("check failed") {
                            return Err(e);
                        }
                        false
                    }
                }
            } else {
                let mut program = base_program.clone();
                program.push_str(&format!(
                    "\n(let chk_lhs__ {})\n(let chk_rhs__ {})",
                    idx_to_expr[*li], idx_to_expr[*ri]
                ));
                program.push_str(&format!(
                    "\n(run-schedule (repeat {} (run axioms)))",
                    config.iter_limit
                ));
                let mut egraph = EGraph::default();
                egraph.parse_and_run_program(None, &program)?;
                match egraph.parse_and_run_program(None, "(check (= chk_lhs__ chk_rhs__))") {
                    Ok(_) => true,
                    Err(e) => {
                        let msg = e.to_string();
                        if !msg.contains("Check failed") && !msg.contains("check failed") {
                            return Err(e);
                        }
                        false
                    }
                }
            };
            if is_equiv {
                viable.push(combo_idx);
            }
        }

        axiom_checks.push(AxiomCheckData {
            op_indices: entry.op_indices.clone(),
            combos,
            viable,
        });
    }

    // 5. Join per-axiom results into full consistent assignments
    let mut joined: Vec<HashMap<usize, usize>> = vec![HashMap::new()];
    for check in &axiom_checks {
        let axiom_partials: Vec<HashMap<usize, usize>> = check
            .viable
            .iter()
            .map(|&combo_idx| {
                check
                    .op_indices
                    .iter()
                    .enumerate()
                    .map(|(pos, &op_idx)| (op_idx, check.combos[combo_idx][pos]))
                    .collect()
            })
            .collect();
        joined = join_partial(&joined, &axiom_partials);
        if joined.is_empty() {
            break;
        }
    }

    // Extend partial assignments to cover unconstrained ops (all candidates viable)
    let constrained: HashSet<usize> = joined.iter().flat_map(|a| a.keys().copied()).collect();
    let unconstrained: Vec<usize> = (0..candidates_per_op.len())
        .filter(|i| !constrained.contains(i))
        .collect();

    let full_assignments = if unconstrained.is_empty() {
        joined
    } else {
        let sizes: Vec<usize> = unconstrained
            .iter()
            .map(|&i| candidates_per_op[i].1.len())
            .collect();
        let extra_combos = index_cartesian(&sizes);
        let mut result = Vec::new();
        for base in &joined {
            for extra in &extra_combos {
                let mut full = base.clone();
                for (pos, &op_idx) in unconstrained.iter().enumerate() {
                    full.insert(op_idx, extra[pos]);
                }
                result.push(full);
            }
        }
        result
    };

    // 6. Build results
    let mut results = Vec::new();
    for assignment in &full_assignments {
        let mapping: Vec<(String, String)> = (0..candidates_per_op.len())
            .map(|op_idx| {
                let (op_name, candidates) = &candidates_per_op[op_idx];
                let target_str = match &candidates[assignment[&op_idx]] {
                    Candidate::Rename(t) => t.clone(),
                    Candidate::Template(t) => t.clone(),
                };
                (op_name.to_string(), target_str)
            })
            .collect();

        // Compute per-axiom preservation from the check results
        let axioms: Vec<(String, bool)> = source
            .axioms
            .iter()
            .enumerate()
            .map(|(axiom_idx, axiom)| {
                let check = &axiom_checks[axiom_idx];
                let target_combo: Vec<usize> = check
                    .op_indices
                    .iter()
                    .map(|&op_idx| assignment[&op_idx])
                    .collect();
                let preserved = check
                    .viable
                    .iter()
                    .any(|&ci| check.combos[ci] == target_combo);
                (axiom.name.clone(), preserved)
            })
            .collect();

        let preserved_count = axioms.iter().filter(|(_, p)| *p).count();
        let total_count = axioms.len();

        if preserved_count > 0 {
            results.push(DiscoveredMorphism {
                mapping,
                axioms,
                preserved_count,
                total_count,
            });
        }
    }

    results.sort_by(|a, b| b.preserved_count.cmp(&a.preserved_count));
    Ok(results)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::signature::Signature;
    use crate::theories::{group::group_theory, monoid::monoid_theory, ring::ring_theory};
    use crate::theory::Axiom;

    fn config() -> SaturationConfig {
        SaturationConfig { iter_limit: 5 }
    }

    #[test]
    fn group_to_ring_finds_additive_morphism() {
        let group = group_theory();
        let ring = ring_theory();
        let results = discover_morphisms(&group, &ring, &config(), 0).unwrap();

        assert!(!results.is_empty());

        let best = &results[0];
        assert_eq!(best.preserved_count, best.total_count);

        let has_mapping =
            |src: &str, tgt: &str| best.mapping.iter().any(|(s, t)| s == src && t == tgt);
        assert!(has_mapping("e", "zero"));
        assert!(has_mapping("inv", "negate"));
        assert!(has_mapping("mul", "add"));
    }

    #[test]
    fn monoid_to_ring_finds_both_monoids() {
        let monoid = monoid_theory();
        let ring = ring_theory();
        let results = discover_morphisms(&monoid, &ring, &config(), 0).unwrap();

        let full_morphisms: Vec<&DiscoveredMorphism> = results
            .iter()
            .filter(|r| r.preserved_count == r.total_count)
            .collect();

        assert!(
            full_morphisms.len() >= 2,
            "expected at least 2 full morphisms, got {}",
            full_morphisms.len()
        );
    }

    #[test]
    fn incompatible_signatures_yield_no_morphisms() {
        let group = group_theory();
        let monoid = monoid_theory();
        let results = discover_morphisms(&group, &monoid, &config(), 0).unwrap();
        assert!(results.is_empty());
    }

    #[test]
    fn identical_theory_finds_identity() {
        let group = group_theory();
        let results = discover_morphisms(&group, &group, &config(), 0).unwrap();

        let identity = results
            .iter()
            .find(|r| r.mapping.iter().all(|(s, t)| s == t));
        assert!(identity.is_some());
        let id = identity.unwrap();
        assert_eq!(id.preserved_count, id.total_count);
    }

    #[test]
    fn discovers_subtraction_template() {
        // Source: theory with sub/2 and zero/0, axiom sub(a,a) = zero
        // Depth 2 needed: (add $1 (negate $2)) requires negate($2) at depth 1,
        // then add($1, negate($2)) at depth 2.
        let mut sig = Signature::new();
        sig.add_op("zero", 0).unwrap();
        sig.add_op("sub", 2).unwrap();
        let source = Theory {
            name: "SubTheory".to_string(),
            signature: sig,
            axioms: vec![Axiom {
                name: "self_sub".to_string(),
                lhs: "(sub a a)".to_string(),
                rhs: "(zero)".to_string(),
            }],
        };

        // Use a minimal group-like target (fewer ops → fewer template candidates)
        let mut tgt_sig = Signature::new();
        tgt_sig.add_op("zero", 0).unwrap();
        tgt_sig.add_op("negate", 1).unwrap();
        tgt_sig.add_op("add", 2).unwrap();
        let target = Theory {
            name: "AdditiveGroup".to_string(),
            signature: tgt_sig,
            axioms: vec![
                Axiom {
                    name: "right_identity".into(),
                    lhs: "(add a (zero))".into(),
                    rhs: "a".into(),
                },
                Axiom {
                    name: "left_identity".into(),
                    lhs: "(add (zero) a)".into(),
                    rhs: "a".into(),
                },
                Axiom {
                    name: "right_inverse".into(),
                    lhs: "(add a (negate a))".into(),
                    rhs: "(zero)".into(),
                },
                Axiom {
                    name: "left_inverse".into(),
                    lhs: "(add (negate a) a)".into(),
                    rhs: "(zero)".into(),
                },
                Axiom {
                    name: "associativity".into(),
                    lhs: "(add (add a b) c)".into(),
                    rhs: "(add a (add b c))".into(),
                },
            ],
        };

        let results = discover_morphisms(&source, &target, &config(), 2).unwrap();

        let has_template = results.iter().any(|r| {
            r.mapping
                .iter()
                .any(|(s, t)| s == "sub" && t == "(add $1 (negate $2))")
                && r.preserved_count > 0
        });
        assert!(
            has_template,
            "expected to find sub → (add $1 (negate $2)), got: {:?}",
            results.iter().map(|r| &r.mapping).collect::<Vec<_>>()
        );
    }

    #[test]
    fn rename_still_works_at_depth_1() {
        let group = group_theory();
        let ring = ring_theory();
        let results = discover_morphisms(&group, &ring, &config(), 1).unwrap();

        let has_rename = results.iter().any(|r| {
            let has = |s: &str, t: &str| r.mapping.iter().any(|(a, b)| a == s && b == t);
            has("e", "zero") && has("inv", "negate") && has("mul", "add")
        });
        assert!(
            has_rename,
            "rename morphism should still be found at depth 1"
        );
    }

    #[test]
    fn depth_0_matches_rename_only() {
        let group = group_theory();
        let ring = ring_theory();
        let results_0 = discover_morphisms(&group, &ring, &config(), 0).unwrap();

        for r in &results_0 {
            for (_, t) in &r.mapping {
                assert!(
                    !t.contains('('),
                    "depth 0 should only produce renames, got template: {t}"
                );
            }
        }
    }

    #[test]
    fn var_to_placeholder_converts_correctly() {
        assert_eq!(var_to_placeholder("(Var \"$1\")", 1), "$1");
        assert_eq!(
            var_to_placeholder("(add (Var \"$1\") (negate (Var \"$2\")))", 2),
            "(add $1 (negate $2))"
        );
        // Non-sequential: only uses $2
        assert_eq!(
            var_to_placeholder("(add (Var \"$2\") (Var \"$2\"))", 2),
            "(add $2 $2)"
        );
    }

    #[test]
    fn is_simple_rename_detects_renames() {
        assert!(is_simple_rename("(add $1 $2)", 2));
        assert!(is_simple_rename("(negate $1)", 1));
        assert!(!is_simple_rename("(add $1 (negate $2))", 2));
        assert!(!is_simple_rename("(add $2 $1)", 2)); // wrong order
    }

    #[test]
    fn discovers_projection_template() {
        // Source: proj/2 with axiom proj(a, proj(b, c)) = proj(a, c)
        // This is satisfied by proj → $1 (first-arg projection).
        let mut sig = Signature::new();
        sig.add_op("proj", 2).unwrap();
        let source = Theory {
            name: "ProjTheory".to_string(),
            signature: sig,
            axioms: vec![Axiom {
                name: "proj_assoc".to_string(),
                lhs: "(proj a (proj b c))".to_string(),
                rhs: "(proj a c)".to_string(),
            }],
        };

        let mut tgt_sig = Signature::new();
        tgt_sig.add_op("zero", 0).unwrap();
        tgt_sig.add_op("add", 2).unwrap();
        let target = Theory {
            name: "Target".to_string(),
            signature: tgt_sig,
            axioms: vec![Axiom {
                name: "add_assoc".to_string(),
                lhs: "(add (add a b) c)".to_string(),
                rhs: "(add a (add b c))".to_string(),
            }],
        };

        let results = discover_morphisms(&source, &target, &config(), 1).unwrap();

        let has_projection = results.iter().any(|r| {
            r.mapping.iter().any(|(s, t)| s == "proj" && t == "$1") && r.preserved_count > 0
        });
        assert!(
            has_projection,
            "expected to find proj → $1, got: {:?}",
            results.iter().map(|r| &r.mapping).collect::<Vec<_>>()
        );
    }

    #[test]
    fn discovers_constant_map_template() {
        // Source: absorb/1 with axiom absorb(absorb(a)) = absorb(a)
        // This is satisfied by absorb → (zero) (constant map to zero).
        let mut sig = Signature::new();
        sig.add_op("absorb", 1).unwrap();
        let source = Theory {
            name: "AbsorbTheory".to_string(),
            signature: sig,
            axioms: vec![Axiom {
                name: "idempotent".to_string(),
                lhs: "(absorb (absorb a))".to_string(),
                rhs: "(absorb a)".to_string(),
            }],
        };

        let mut tgt_sig = Signature::new();
        tgt_sig.add_op("zero", 0).unwrap();
        tgt_sig.add_op("negate", 1).unwrap();
        let target = Theory {
            name: "Target".to_string(),
            signature: tgt_sig,
            axioms: vec![],
        };

        let results = discover_morphisms(&source, &target, &config(), 1).unwrap();

        let has_constant = results.iter().any(|r| {
            r.mapping
                .iter()
                .any(|(s, t)| s == "absorb" && t == "(zero)")
                && r.preserved_count > 0
        });
        assert!(
            has_constant,
            "expected to find absorb → (zero), got: {:?}",
            results.iter().map(|r| &r.mapping).collect::<Vec<_>>()
        );
    }
}
