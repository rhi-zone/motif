# Time-Cost Estimate: Formalizing the Langlands Program

Companion to `ROADMAP.md`. Where a number is backed by a search result, a repo
clone, or a `wc -l`, it's cited with a source. Where it's a projection from
those data points onto the roadmap's phases, it's marked **[extrapolated]**
and should be read as considerably softer than the calibration data itself.
No number in this document is a substitute for actually starting Phase 0 and
re-measuring.

---

## 1. Calibration data points (real formalization efforts)

All figures below are from web search results and/or direct repo measurement
(`git clone --depth 1` + `wc -l` on `.lean` files, run 2026-07-24). Person-time
figures for team projects are almost never full-time-equivalent (FTE) —
contributor lists mix core full-timers with drive-by contributors — so
"N people over M years" is not N×M person-years; it's an upper bound with a
long tail of small contributions. This is flagged per entry.

| Project | Lines | Elapsed | People | Notes |
|---|---|---|---|---|
| **Feit–Thompson** (Coq, Gonthier et al., Inria) | 170,000 (~15,000 defs, ~4,200 theorems) | 6 years (2006–2012) | 15 named contributors | Team led by Gonthier; not all 15 were full-time for all 6 years — the commonly-cited "15 people, 6 years" is a contributor list, not an FTE count. A defensible FTE range is **15–30 person-years**; a claim of "90 person-years" surfaced in one search summary but could not be traced to a primary source and is **not used** below. [Springer chapter](https://link.springer.com/chapter/10.1007/978-3-642-39634-2_14), [phys.org](https://phys.org/news/2012-10-six-year-journey-proof-feit-thompson-theorem.html) |
| **Liquid Tensor Experiment** (Lean, Commelin et al.) | not separately measured here (lives partly in a satellite repo, partly upstreamed to Mathlib) | 1 month to state the theorem + 5 months to finish the proof ≈ **1.5 years total** end-to-end (challenge Dec 2020 → completion Jul 2022) | ~12 mathematicians + several engineers named (Commelin as lead, Topaz doing "vast amounts" of the condensed-math/homological-algebra core, Buzzard, Massot, Best, Brasca, and others) | Best available real "how long does a Scholze-grade research result take to formalize" data point. Effective concentrated effort (not all 12 full time throughout) — order-of-magnitude **3–8 person-years** for a single hard theorem with heavy new-infrastructure cost. [Lean blog](https://leanprover-community.github.io/blog/posts/lte-final/), [Xena](https://xenaproject.wordpress.com/2021/06/05/half-a-year-of-the-liquid-tensor-experiment-amazing-developments/) |
| **Perfectoid spaces** (Buzzard–Commelin–Massot) | 12,091 (measured directly) | "months-long effort" (2019, paper May 2020) | 3 named authors | Definitions-only project (state the definition of a perfectoid space and enough surrounding theory), not a theorem proof — cheaper per line than a proof-heavy project. **~0.5–1.5 person-years** [extrapolated from "months" + 3-author byline]. [arXiv:1910.12320](https://arxiv.org/pdf/1910.12320) |
| **Sphere eversion** (Massot–van Doorn–Nash) | 14,641 (measured directly) | ~1 year, 3 people, part-time | 3 | Explicitly reported as **~3 person-years** (3 people × ~1 year, part-time, so likely 1–2 person-years FTE in practice). [GitHub](https://github.com/leanprover-community/sphere-eversion) |
| **Polynomial Freiman–Ruzsa** (Tao–Dillies–Mehta + community) | not measured (large multi-contributor blitz) | **3 weeks** end-to-end from preprint to fully formalized, dependency graph closed | crowd-sourced, dozens of drive-by contributors coordinated via blueprint | Outlier-fast: this worked because (a) Tao ran a public blueprint/task-board that let strangers pick up single lemmas, (b) the underlying combinatorics needed almost no new Mathlib infrastructure. **Not representative** of infrastructure-heavy projects like Langlands phases 1/3/4/8 — cited here mainly as a ceiling on how fast formalization *can* go when infrastructure is already present. [Tao's blog](https://terrytao.wordpress.com/2023/11/18/formalizing-the-proof-of-pfr-in-lean4-using-blueprint-a-short-tour/) |
| **Adeles/idèles of a global field** (de Frutos-Fernández) | 2,914 (measured directly, Lean 3 repo) | paper at ITP 2022; work conducted ~2021–2022 | 1 primary author | Directly relevant calibration for Phase 0 of the roadmap (idele class group), since Phase 0 is explicitly "extend this same codebase." **~0.3–0.8 person-years** [extrapolated: single-author, sub-3k-line project, ~1 year elapsed but not full-time]. [arXiv:2203.16344](https://arxiv.org/abs/2203.16344) |
| **FLT (Fermat's Last Theorem)**, Buzzard et al., Imperial | 58,636 (measured directly, current snapshot) | Ongoing since Nov 2023; **2.7 years elapsed as of this writing** (2026-07-24), grant runs to Sep 2029 | 69 GitHub contributors (long-tailed — a handful of core people carry most of the volume; the "Lean for the Curious Mathematician" workshop model recruits many one-off contributors per module) | 25 files still contain `sorry` (measured directly) — i.e. still incomplete after 2.7 years and 58.6k lines. Buzzard's own words: **"this is at least a 5 year project — to be frank, it's probably a lot more than 5 years"** to reach *just* the reduction to 1980s-known claims, not a from-first-principles proof. This is the single most important calibration point for this document, since FLT and Langlands overlap heavily (modularity, Galois representations, automorphic forms) and Buzzard is explicitly not sandbagging. [FLT repo](https://github.com/ImperialCollegeLondon/FLT), [blueprint](https://imperialcollegelondon.github.io/FLT/blueprint.pdf) |

**Mathlib itself**, for scale: **~1.2–2.1 million lines** (sources disagree by
date of measurement), **274,045 theorems, 130,791 definitions, 772
contributors**, built over ~10 years by an open community. This is the "how
big is the mountain" reference point — the entire Langlands roadmap below is
a rounding error against Mathlib's current size but would still be one of the
largest single coherent sub-projects ever attempted inside it, comparable in
ambition to Mathlib's entire measure-theory or algebraic-geometry corpus.
[Mathlib stats](https://leanprover-community.github.io/mathlib_stats.html)

### 1.1 What these numbers say about lines-per-difficulty

There is no clean "lines per concept" constant — the range across projects
above is roughly:
- **~1,000–3,000 lines/person-year** for definition-heavy, low-proof-burden
  work with reusable infrastructure already in place (adeles/idèles: ~3–10k
  lines/person-year at the high end if the 0.3–0.8 py estimate is right;
  perfectoid spaces: ~8–24k lines/person-year).
- **~5,000–15,000 lines/person-year** for FLT-style "state a lot of
  interlocking structure, prove some of it, `sorry` the rest for now"
  (58,636 lines / ~2.7 years / a core team plausibly in the 3–8 FTE range ⇒
  roughly this band, very roughly).
- **~15,000–30,000 lines/(person-year)⁻¹ inverted, i.e. ~1,000–2,000
  lines/person-year** for genuinely new, proof-heavy, no-prior-art content
  (Feit-Thompson: 170,000 lines / 15–30 person-years ⇒ ~6,000–11,000
  lines/person-year, but this was 2006-2012 tooling, much less mature than
  today's Lean 4/Mathlib).

None of these ratios transfers cleanly to Langlands, because Langlands' cost
is dominated not by lines but by **missing foundational vocabulary** (§1.4,
§1.5, §1.8 of the roadmap — reductive groups, admissible representations, the
Weil group) that has no existing Mathlib analogue to extend, unlike every
project above except Feit-Thompson (which invented finite-group-representation
theory more or less from scratch inside Coq's SSReflect library, which is
part of why it took 6 years). This is the single biggest reason to treat the
per-phase estimates below as wide ranges, not point estimates.

---

## 2. Per-phase estimates

Person-months given as **optimistic / realistic / pessimistic**. All phase
numbers below are **[extrapolated]** — projections from §1's calibration data
onto the roadmap's own difficulty language ("small", "medium", "large",
"huge"), not independent measurements. Lines-of-Lean are order-of-magnitude
guesses calibrated against the closest analogue project in §1.

### Phase 0 — Idele class group
- **Analogue:** almost exactly de Frutos-Fernández's own adele/idele work
  (2,914 lines), extended with a quotient and topology instances.
- **Person-months:** 1 / 3 / 8
- **Lines of Lean:** 500–2,000
- **Risk:** low. Main risk is the note already in ROADMAP.md — compactness of
  the norm-one idele class group might reveal the restricted-product topology
  machinery isn't strong enough, which would bleed into Phase 2/8's timeline
  rather than blowing up Phase 0 itself.

### Phase 1 — Weil group / Weil–Deligne group
- **Analogue:** no close analogue in §1 — this is genuinely new content with
  no existing Mathlib scaffold beyond `AbsoluteGaloisGroup`/`ProfiniteGrp`.
  Closest comparison in kind (new algebraic gadget, bounded scope, one
  research-level definition) is perfectoid spaces (12,091 lines, ~0.5–1.5 py)
  but Weil group is smaller in surface area (one group extension + one
  compatibility condition, not a whole geometric theory).
- **Person-months:** 4 / 10 / 24
- **Lines of Lean:** 2,000–6,000
- **Risk:** medium. The valuation-to-ℤ extension and the semi-direct-product
  bookkeeping are routine; the risk is topology mismatches between the
  profinite Galois group and the discrete ℤ-factor (Weil group is *not*
  profinite, unlike Gal(K̄/K) — this kind of category mismatch has broken
  other formalizations before, e.g. topology instance conflicts are a
  recurring Mathlib pain point per the roadmap's own §1.3 notes on restricted
  products).

### Phase 2 — Local class field theory (local Artin map)
- **Analogue:** none directly, but this is explicitly a **proof-heavy**
  phase (existence theorem, norm groups, Brauer-group H² computation) rather
  than definitional — closer in kind to Feit-Thompson (real theorem, real
  proof burden, ~6,000-11,000 lines/person-year band) than to any
  definition-only project above.
- **Person-months:** 8 / 24 / 60
- **Lines of Lean:** 8,000–25,000
- **Risk:** high. "Genuine theorem with real proof burden" is the roadmap's
  own phrase. Local CFT proofs in the literature (Serre's *Local Fields*,
  Milne's notes) run 40-80 pages of dense cohomological argument; historically
  this class of argument (group-cohomology-heavy, several interlocking
  inductions) is exactly where formalization time estimates blow up 2-3x
  over the naive guess, per the general pattern noted in Feit-Thompson
  retrospectives (induction-heavy finite group theory was the slow part,
  not the "easy" combinatorial lemmas).

### Phase 3 — Reductive groups over a field (dual-group blocker)
- **Analogue:** the roadmap's own text calls this "comparable in scope to
  formalizing a chapter of Springer's *Linear Algebraic Groups*... plausibly
  the single biggest piece of the entire roadmap." No formalization of
  general reductive group theory exists in any proof assistant to compare
  against directly (checked: no hits for a dedicated "reductive groups in
  Lean/Coq/Isabelle" project in search results). The nearest scale analogue
  by ambition is Feit-Thompson's from-scratch group theory library (170,000
  lines, 15-30 py) — reductive group *scheme* theory (tori, root data,
  Chevalley classification, quasi-split forms with Galois action) is
  arguably harder per line because it mixes algebraic geometry (group
  schemes) with the combinatorics Mathlib already has (root systems), and
  that geometry layer (torsors, descent, group-scheme quotients) is itself
  underdeveloped in Mathlib.
- **Person-months:** 18 / 48 / 120 for the **split-only, de-scoped** version
  the roadmap recommends (skip non-split forms, skip general schemes,
  validate against `GL_n`/`SL_n`). The **general/quasi-split** version with
  full Galois-twisted dual groups is easily another 12-36 person-months on
  top, and a fully general (non-split, arbitrary base) theory of reductive
  group *schemes* would be its own multi-year project comparable to
  Feit-Thompson in scale — **not** included in the headline range below.
- **Lines of Lean:** 20,000–60,000 for the de-scoped split version.
- **Risk:** very high, and not just technical. The roadmap itself flags the
  real risk: this is "the piece most likely to already be wanted by other
  Mathlib contributors... worth checking Mathlib's Zulip/roadmap for parallel
  effort before starting, since duplicating a large in-flight project would
  be the worst outcome here." Coordination/duplication risk here is as large
  as the technical risk — if algebraic-geometry-focused Mathlib contributors
  are independently building group-scheme foundations, Phase 3's real cost
  depends on integration with their design choices, not just raw formalization
  labor.

### Phase 4 — Smooth/admissible representations
- **`GL_n`-only track** (usable before Phase 3 lands):
  - **Person-months:** 6 / 16 / 36
  - **Lines of Lean:** 5,000–15,000
  - **Risk:** medium — "smooth = every vector fixed by some compact open
    subgroup" is a clean, small definition; the risk is downstream (proving
    anything nontrivial about admissible reps, e.g. finite-dimensionality of
    fixed spaces, requires real p-adic analysis/measure theory work not yet
    scoped).
- **General-`G` track** (parabolic induction, Jacquet modules, supercuspidal
  support, Bernstein decomposition — gated on Phase 3):
  - **Person-months:** 24 / 60 / 150
  - **Lines of Lean:** 15,000–50,000
  - **Risk:** high — Bernstein decomposition alone is a hard graduate-level
    theorem with no formalization precedent anywhere.

### Phase 5 — Statement of local Langlands for `GL_n`
- **Person-months:** 1 / 3 / 8 (once Phases 1 and 4-`GL_n` exist — the
  roadmap's own assessment that this is "just writing the Prop" is credible;
  this is the cheapest phase in the entire roadmap by design).
- **Lines of Lean:** 200–1,000
- **Risk:** low, contingent entirely on Phases 1 and 4 landing first — the
  risk here is 100% inherited, not intrinsic.

### Phase 6 — Statement of Artin's conjecture
- **`n=1` track** (repackages Phase 0+2): **Person-months:** 2 / 5 / 12;
  **Lines:** 1,000–4,000; low-medium risk (mostly assembly, contingent on
  Phase 2's proof actually landing rather than being stated as an axiom).
- **General-`n` track** (needs Phase 8): **Person-months:** 6 / 15 / 40;
  **Lines:** 3,000–10,000; risk fully inherited from Phase 8.

### Phase 7 — Galois cohomology packaging
- **Person-months:** 2 / 5 / 12 (roadmap's own "small-medium," parallelizable,
  low risk — closest thing to a free lunch in this roadmap since Mathlib
  already has every underlying piece).
- **Lines of Lean:** 1,500–5,000
- **Risk:** low.

### Phase 8 — Automorphic representations, statement of global Langlands
- **Analogue:** none close. The roadmap calls this "the single most
  mathematically demanding phase, on par with or larger than Phase 3." The
  restricted-tensor-product bookkeeping ("almost all factors unramified") is
  a genuinely fiddly piece of infrastructure with no Mathlib precedent
  (nearest relative: the restricted-product-of-units machinery from adeles,
  but that's for a much simpler algebraic structure than a tensor product of
  representations).
- **Person-months:** 24 / 72 / 180
- **Lines of Lean:** 20,000–60,000
- **Risk:** very high, plus the roadmap's own explicit warning about
  duplication risk with non-Mathlib geometric-Langlands formalization
  efforts elsewhere — worth a literature check before committing, exactly as
  the roadmap says.

### Phase 9 — Functoriality statement
- **Person-months:** 2 / 6 / 15 once Phases 3, 5(generalized), and 8 exist —
  again "just" a `Prop`, but sitting at the end of the longest dependency
  chain, so its calendar-time cost is really "whenever everything upstream
  finishes," not its own labor cost.
- **Lines of Lean:** 500–3,000
- **Risk:** low intrinsic, 100% schedule risk inherited from upstream.

---

## 3. Totals

### 3.1 Fastest path to a *stated* local Langlands for `GL_n` (Phases 0,1,2,4-`GL_n`,5)

This is the path the roadmap itself identifies as fastest — it explicitly
avoids Phase 3.

| Phase | Realistic person-months |
|---|---|
| 0 | 3 |
| 1 | 10 |
| 2 | 24 |
| 4 (`GL_n` track) | 16 |
| 5 | 3 |
| **Total** | **~56 person-months ≈ 4.7 person-years** |

Range across optimistic/pessimistic column sums: **~21 to ~146 person-months
(1.8 to 12 person-years)**. Note Phase 2 (local CFT, a real theorem) is the
long pole here, not any definitional phase.

### 3.2 Full roadmap to *state* all four core conjectures for general `G`
(adds Phases 3, 4-general, 6-general, 7, 8, 9 on top of 3.1's realistic column)

| Phase | Realistic person-months |
|---|---|
| 0–2, 4-GLn, 5 (from 3.1) | 56 |
| 3 (reductive groups, de-scoped split version) | 48 |
| 4 (general-`G` track) | 60 |
| 6 (general-`n` track) | 15 |
| 7 | 5 |
| 8 | 72 |
| 9 | 6 |
| **Total** | **~262 person-months ≈ 22 person-years** |

Range: **optimistic ~66 person-months (5.5 py)** to **pessimistic ~477
person-months (~40 py)**. This is a **wide** range — a factor of ~7 between
optimistic and pessimistic — because Phases 3 and 8 alone (the two "huge,
uncharted" phases) account for more than half the realistic total and are
exactly the phases with no real formalization precedent to calibrate
against, anywhere, in any proof assistant.

**To additionally *prove* what's provable** (local Langlands for `GL_n` —
known since Harris–Taylor/Henniart in the 1990s-2000s; the modularity
theorem for elliptic curves over ℚ — Wiles/Taylor–Wiles plus BCDT's
extension to all elliptic curves over ℚ) is a categorically larger
undertaking than stating the conjectures, comparable to or exceeding
Feit-Thompson: Buzzard's own FLT project — which only targets the reduction
of FLT to 1980s-known claims, a strictly smaller target than full local
Langlands for `GL_n` or full modularity — is already 2.7 years in with 25
files still carrying `sorry`, and Buzzard himself estimates **"at least 5
years, probably a lot more"** for that narrower goal. Proving local Langlands
for `GL_n` in general (not just the cases needed for FLT) or the general
modularity theorem, on top of the "state everything" 22-person-year figure
above, is plausibly another **30–80+ person-years** — but this is a
**[heavily extrapolated]** figure with no direct calibration point; treat it
as "the same order of magnitude as several Feit-Thompson-scale efforts run
one after another," not a number to plan a budget against.

### 3.3 Headline numbers

- **To formally *state* local Langlands for `GL_n` only** (fastest path,
  skipping general reductive groups): **~2–12 person-years**, realistic
  estimate **~5 person-years**.
- **To formally *state* all four core conjectures for general reductive
  groups**: **~6–40 person-years**, realistic estimate **~22 person-years**.
- **To additionally *prove* the currently-known cases** (local Langlands for
  `GL_n`, modularity for elliptic curves /ℚ): add **very roughly another
  30–80+ person-years**, essentially unbounded above given that Buzzard's
  narrower FLT project alone is already tracking toward "a lot more than 5
  years" for less than this.

These are calendar-independent labor totals — a team of size *k* compresses
elapsed time roughly by *k* only where phases can run in parallel (Phase 7 can
run alongside 0-2; Phase 4-`GL_n` doesn't need Phase 3), and not at all past a
certain team size on phases that are inherently sequential single-person
design decisions (Phase 3's dual-group construction, in particular, is the
kind of foundational-API decision that historically does *not* parallelize
well — see Mathlib's own experience that large foundational refactors are
bottlenecked on a small number of people who can hold the whole design in
their head at once).

---

## 4. What the community itself says

- **Kevin Buzzard**, on his own *narrower* FLT project (which needs much of
  the same infrastructure — Galois representations, modular
  forms/automorphic forms, class field theory — as this roadmap's Phases
  1/2/6/8): **"this is at least a 5 year project — to be frank, it's
  probably a lot more than 5 years."** The FLT grant itself runs to
  September 2029 (6 years from the 2023 start) with the explicit, modest
  goal of reducing FLT to claims already known by the late 1980s — not a
  from-scratch proof. [Source found via search; grant/GENERAL.md confirm the
  2024-2029 funding window.]
- **Buzzard, more broadly** (per the "Beyond the Liquid Tensor Experiment"
  retrospective): explicitly declines to give a timeline for condensed
  mathematics or Langlands-scale efforts — **"I cannot see into the
  future"** — and pushes back on hype about formalization "outpacing"
  mathematicians as "complete science fiction." This is a datapoint about
  epistemic humility from the field's most active large-project organizer,
  not an estimate — worth weighting accordingly: the person with the most
  first-hand data explicitly refuses to give a number for anything at this
  scale.
- **No search result found** an explicit Scholze quote estimating a
  timeline for formalizing Langlands specifically; Scholze's public
  statements found relate only to the Liquid Tensor Experiment challenge
  itself, not to Langlands. This should be read as **absence of evidence**,
  not evidence that no such quote exists — it was not found in the searches
  run for this document.
- **General community pattern** visible across every project in §1: teams
  consistently report elapsed time exceeding initial estimates (Buzzard's
  own framing above is the clearest example), and the fast counterexample
  (PFR, 3 weeks) worked specifically because it required *no* new
  foundational infrastructure — the opposite of this roadmap's Phases 1, 3,
  4, and 8, which are foundational-infrastructure-heavy by construction.

---

## 5. Honesty about uncertainty

- **Real data, not extrapolated:** all rows in the §1 calibration table
  except the Feit-Thompson person-year range and the PFR representativeness
  caveat; all repo line counts (measured directly via `git clone` + `wc -l`
  on 2026-07-24); Buzzard's "5 years, probably more" quote; FLT's current
  58,636-line/25-sorry/69-contributor/2.7-year snapshot.
- **Extrapolated, flagged inline:** every per-phase person-month estimate in
  §2, the Feit-Thompson 15-30 person-year band (contributor-list-derived,
  not FTE-measured), and all of §3's totals, which are sums of §2's
  extrapolations and therefore compound whatever error each phase estimate
  carries.
- **Explicitly not found / could not verify:** a traceable primary source
  for a "90 person-year" Feit-Thompson figure (dropped from this document
  after failing to trace it); any Scholze quote on Langlands formalization
  timelines; any existing formalization of general reductive group theory in
  any proof assistant to calibrate Phase 3 against directly; current
  detailed FLT team-size-over-time data (only a cumulative 69-contributor
  count and a point-in-time line count were obtainable, not a labor-hours
  breakdown).
- **The single largest source of uncertainty** is Phases 3 and 8, both
  flagged by the roadmap itself as "huge" with the further risk of
  duplicating unknown parallel efforts elsewhere. Because they dominate the
  realistic total (48 + 60 general-track + 72 = 180 of 262 person-months,
  ~69% of the "state everything" total), the true uncertainty on the
  headline 22-person-year figure is closer to the pessimistic/optimistic
  spread (6–40 py) than the point estimate suggests — this is a genuine
  "we don't know" on the two phases that matter most, not false precision
  dressed as a range.
