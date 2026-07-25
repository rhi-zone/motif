# Ecosystem Survey: Who's Already Working On This

> Research findings from a prior session, not independently re-verified in this pass —
> dates/statuses may have drifted, and the HautevilleHouse repos in particular need direct
> inspection before being treated as real.

Companion to `FORMALIZATION_PRIORITIES.md`. Organized by the same 9 areas, same tiering
and order. For each area: source attributions (repo, paper/arXiv id, Zulip thread) and
status (merged / active / dormant / stale / unverified).

## Tier 1: Infrastructure

### 1. ∞-Categories
Two live-but-incomplete Lean 4 attempts, neither merged into Mathlib:
- **mckoen/quasicategory** — quasi-category formalization; per lean-pool's 2026-06-28
  triage it still has unresolved `sorry`s in `Quasicategory/Main.lean` and three other
  files, so not sorry-free/complete.
- **mariovagomarzal/HigherCategoryTheory** — active as of late April 2026 (too recent for
  lean-pool's staleness gate at curation time); direct content unknown (repo page 404'd on
  refetch, name was current at last check).
- Related, already-merged Mathlib work: colimits in `Cat` and full-faithfulness of the
  nerve functor (ITP 2025, Mario Carneiro) — a stepping stone toward ∞-categories, not
  ∞-categories themselves.
- No dedicated ∞-category project found in mathlib4, TauCeti, or lean-pool's merged set.

### 2. Real Analysis Gaps
- **Rouché's theorem**: no evidence found in Mathlib, lean-pool, or TauCeti of a direct
  formalization; TauCeti's roadmap instead has "Contour integration and the
  Hungerbühler–Wasem generalized residue theorem" (adjacent but not Rouché itself) and
  "Conformal mapping." lean-pool has `RiemannMappingTheorem` and `LeanComplexAnalysis`
  projects but no README content confirms Rouché specifically.
- **Path integrals**: no active project found.
- **Measure theory completeness**: no dedicated gap-filling project found; Mathlib's
  probability/measure library is mature but no specific "completeness" project surfaced.

### 3. Algebraic Geometry
- **Derived categories**: "Formalization of derived categories in Lean/Mathlib" (arXiv,
  AFM journal) — completed, merged work for the derived category of an abelian category.
- **Coherent sheaves**: lean-pool has `GrothendieckVanishing` (README was empty in the
  local checkout, so scope unconfirmed) — Grothendieck vanishing is a coherent-cohomology
  result, suggesting some coverage.
- **Moduli spaces**: mattrobball/BridgelandStability (Bridgeland stability conditions —
  moduli-adjacent) and YijunYuan/HarderNarasimhan (Harder–Narasimhan filtrations, arXiv
  2509.19632) are both active/recent per lean-pool's "dropped for recency" list — real
  activity, not yet stable/imported.
- **Other active pieces**: chrisflav/proetale and chrisflav/pi1 (pro-étale site, étale
  fundamental group), smorel394/Grassmannian, ExteriorPowers, ProjectiveSpace_lean4,
  Paul-Lez/Stacks-project (fibered categories/stacks) — all foundational AG fragments,
  none full moduli-space theory.

## Tier 2: High-Value Domains

### 4. Classification of Finite Simple Groups
No project attempts the full CFSG. Nearest work:
- "Classifying the Groups of Order p³ in Lean" (2026, ~3000 lines, arXiv 2606.26141).
- AlexBrodbelt/DicksonsClassificationTheorem.
- A Mathlib Zulip thread ("classification of finite simple groups") notes an old `cfsg`
  branch containing only a statement (mostly `sorry`, covering just cyclic/alternating/
  Mathieu groups) — effectively dormant.

### 5. Number Theory / Langlands (beyond our adele/idele work)
- **kbuzzard/ClassFieldTheory** — the most substantial active effort: "an ongoing project
  to formalize the main theorems of local and global class field theory," tied to the
  2025 Clay Mathematics summer school, 310+ commits, has a blueprint site, actively
  worked on.
- **Adeles/ideles**: base formalization already done (2022 ITP paper) plus a 2024/2025
  result proving local compactness of the adele ring — explicitly framed as a step toward
  Tate's thesis / Langlands for GL(1).
- **CBirkbeck/LeanModularForms** (merged into lean-pool, 77k LOC) covers modular forms.
- **mariainesdff/LocalClassFieldTheory** — local fields toward local class field theory
  (lean-pool shortlisted candidate, not yet merged).
- Several **HautevilleHouse/\*-langlands-\*-mathlib** repos turned up in lean-pool's
  `discovered.yml` (local/global/geometric/p-adic Langlands) — these have empty metadata
  and suspicious naming patterns ("canonical-lane-mathlib" repeated across many repos);
  **unverified, treat with suspicion** — not confirmed active formalization until
  inspected directly.
- No dedicated L-function or Weil-group project found beyond what's implicit in the
  modular-forms/adele work.

### 6. HoTT / ∞-groupoids
- **HoTTLean** (sinhp/HoTTLean, Sina Hazratpour) — active, formalizes the groupoid model
  of HoTT₀ (univalence restricted to set-truncated types) plus a synthetic proof mode
  ("SynthLean"); this is the live successor to the old Lean 2/Lean 3 HoTT ports (which are
  dead — Lean 3's kernel is inconsistent with univalence).
- jzxia/WhiteheadTheorem (homotopy groups) in lean-pool is adjacent but not HoTT-native.

## Tier 3: Verification Targets

### 7. Disputed Proofs (IUT)
**LANA Project** (Lean and Anabelian geometry), started by Kato Fumiharu at ZEN
Mathematics Center in late 2023, explicitly aims to formalize IUT to settle the
Mochizuki/Scholze–Stix dispute; Adam Topaz (U. Alberta) is involved. Per a July 2026
interim report, the project has made progress on profinite fundamental groups from SGA1
but has isolated a specific unresolved compatibility problem at Corollary 3.12 / Theorem
3.11 — the exact spot Scholze/Stix flagged in 2018. Active but stalled at the crux.

## Tier 4: Applications

### 8. Probability / Statistics
- **Doob's martingale convergence theorems** — already fully merged in Mathlib
  (`Mathlib.Probability.Martingale.Convergence`; arXiv 2212.05578).
- **RemyDegenne/clt** — a dedicated central limit theorem project, listed among
  lean-pool's "active mathlib-bound" near-misses (i.e., real, ongoing, staging for
  Mathlib upstream).
- **RemyDegenne/BrownianMotion, RemyDegenne/kolmogorov_extension4** — same author,
  actively pushed toward Mathlib, covering Brownian motion and Kolmogorov extension
  (empirical-process-adjacent foundations).
- **cameronfreer/exchangeability** — de Finetti/exchangeability, recently active (April
  2026).

### 9. Physics
**PhysLean** merged with **Lean-QuantumInfo** to form **Physlib** — active,
community-run, mainstream-physics-only (Maxwell's equations, quantum harmonic
oscillator, statistical mechanics, tight-binding model). This is the main active Lean
physics formalization effort.

## Meta-Projects (tracking infrastructure, not targets)

- **lean-pool** (Vasily Ilin / Justin Asher, UW Lean Hackathon) imports completed,
  sorry-free, permissively-licensed Lean projects (140 projects, ~944k LOC) sitting
  between Mathlib and looser repos.
- **TauCetiProject/TauCeti** is an AI-built library with human-written roadmaps/AI
  review, explicitly following Mathlib conventions — its current roadmap (13 active
  items) does not include any of the 9 target areas directly, though "Reductive algebraic
  groups" and "Contour integration" are the closest adjacent topics.
- **leanprover-community/intentions** is NOT a math-target tracker — it's a generic
  GitHub Action for claiming issues/tasks on a project board (TTL-based claim/release),
  containing no content about specific formalization targets. Noted explicitly to
  prevent future confusion.
