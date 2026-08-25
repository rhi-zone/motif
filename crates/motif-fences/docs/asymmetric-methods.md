# Asymmetric generation methods for the fences problem

Scope: the nine open records (n = 8, 11, 13, 14, 16, 18, 19, 21, 23) that sit strictly
between consecutive "trivial" minimum-edge-polyomino n's. Target: group (d), the
free-form asymmetric pinwheels (n = 11, 14, 19), which currently have no generating
method — only a visual read of the record images.

Every claim below is tagged **DERIVED** (worked out here, derivation shown),
**VERIFIED** (checked against the record images or table), or **CONJECTURED**
(plausible, not checked — do not build on it as fact). Untagged prose is exposition
connecting tagged claims, not itself a claim.

## 1. Configuration space: degrees of freedom vs. constraints

### 1.1 Setup

A configuration of n fences is n unit segments in the plane. Each segment has two
endpoints, so the raw coordinate data is 2n points, 4n real numbers.

Constraints, generic case:

- **Length.** Each of the n fences has length exactly 1: `n` scalar equations
  (`|P_i1 - P_i0|^2 = 1`).
- **Incidence.** Every one of the 2n endpoints must lie on some *other* fence.
  Generically (endpoint lands in the open interior of the target fence — a
  T-junction) this is collinearity with the target's two endpoints: **1** scalar
  equation. The "between the target's endpoints" part is an open (inequality)
  condition and does not reduce dimension. So: `2n` scalar equations, one per
  endpoint, *in the generic/T-junction case*.

**DERIVED.** Generic expected dimension of the realization space for a fixed
combinatorial skeleton (fixed assignment of which endpoint lands on which fence):

```
dim = 4n (coordinates) - n (lengths) - 2n (incidences) = n
```

Quotient by the 3-dimensional group of orientation-preserving rigid motions
(2 translation + 1 rotation; scaling is excluded because length is pinned to 1;
reflection is a discrete symmetry, not a continuous one, so it doesn't change the
count):

```
dim(moduli) = n - 3
```

This assumes the constraint Jacobian has full rank `3n` at a generic point of the
given skeleton — i.e. genericity in the same sense as Laman-type bar-joint rigidity
theory. It is a genericity **assumption**, not automatic: specific skeletons (in
particular symmetric ones, §1.3) can have rank deficiency or excess, which changes
the count locally.

### 1.2 Corner vertices are dimension-neutral (VERIFIED by direct count, not against images)

A worry: doesn't an ordinary polygon corner, where two fences share an endpoint
exactly (not a T-junction), cost 2 equations (both coordinates forced equal) to
satisfy only... how many incidence requirements? Answer: **two** — fence A's
endpoint automatically "lies on" fence B (it *is* B's endpoint), and vice versa. So
one coincidence (2 equations) discharges 2 of the 2n incidence requirements at once:
exactly the same rate, 1 equation per requirement, as a generic T-junction. Ordinary
polygon corners (as in every "trivial" polyomino) are dimension-neutral relative to
the generic count in §1.1 — they don't need to be treated as a special case. This is
why the `n - 3` formula applies uniformly across polyomino-style and T-junction-style
skeletons.

**Consequence:** the flex space of a *generic asymmetric* valid skeleton is
`(n - 3)`-dimensional, not a point. Whether the actual area-maximizing configuration
for a given skeleton is an isolated point of that space, or lies on a positive-
dimensional locus of tied optima, depends on how many of the "field area ≤ 1"
constraints are *active* (exactly 1) at the optimum — see §1.4.

### 1.3 Hub coincidences: an m-way point cuts m-2 moduli dimensions, it does not forbid the hub (DERIVED, VERIFIED against n=11)

Contrast with a "wheel" skeleton where m spoke-fences all meet at one common
interior hub point. Requiring m unit-length points `P_1, ..., P_m` (the spokes' inner
endpoints) to all equal one location costs `2(m-1)` equations (pairwise-equal-to-P_1),
but discharges only `m` incidence requirements (each spoke's inner endpoint lies on
"another fence" — trivially true once it coincides with any other spoke's endpoint).
For m ≥ 3 this is over-determined relative to the naive generic budget by
`2(m-1) - m = m - 2` equations.

**This does not mean an m-way point hub is infeasible.** An earlier version of this
document read the excess as forcing a symmetry ansatz (only realizable at special
(n, m) pairs). That overstated the case. The measured rule, checked by numerical
Jacobian rank on both variants of the n=11 skeleton (`docs/`-adjacent
`tests/records.rs::split_hub_pinwheel_n11`, plus an unmerged point-hub sibling
solved alongside it):

```
dim(moduli) = n - 3 - (m - 2)
```

i.e. an m-way point coincidence is realizable at a *generic* (asymmetric) skeleton
too — it just costs `m - 2` moduli dimensions relative to the all-T-junction
baseline of §1.1, the same way any other extra coincidence would. It is not a
special stratum requiring a symmetric ansatz; it is a strictly worse budget
allocation.

**VERIFIED, n=11.** Two skeletons were solved for the same unit-edge-heptagon
boundary (B-E-G-R-S1-S2-D) with 4 interior chords (C-H1, Q1-*, Q2-*, F-*):

- **Split hub**: three of the four chords (Q1, Q2, F) share one 3-way endpoint
  coincidence H2 (m=3); the fourth chord (C) lands by ordinary T-junction on the
  *interior* of Q1's chord at a distinct point H1. 22 raw coordinates, 15
  independent constraint equations by numerical Jacobian rank → 7 moduli
  (`n - 3 = 8`, minus 1 for the one 3-way coincidence's `m - 2 = 1` excess — matches).
  Total area **3.5372167764**, matching the published record (Teodor Tohanean,
  3.53721+) to the precision of the numeric solve.
- **Point hub**: all four chords forced through the same single point (m=4). 20 raw
  coordinates, 14 independent equations → 6 moduli (`8 - (4-2) = 6` — matches).
  **Feasible** — total area **3.5017721551** — but strictly worse than the split
  hub by giving up 2 moduli dimensions (`m - 2 = 2`) instead of 1.

So the record's construction is best read as spending its incidence budget the
moduli-maximizing way: prefer several small coincidences (or none) over one large
one, because each unit of `m - 2` is a unit of lost optimization freedom, and here
that freedom converts directly into area (three of the split hub's four bounded
faces sit exactly at the area-1 cap at the optimum; the point hub's does too, but
starting from one fewer free dimension it cannot push its residual face as large).

**Worked check (VERIFIED against the record table).** For a *regular* unit-side
m-gon with unit-length spokes from every vertex to one common center, the center
distance (circumradius) is `R(m) = 1 / (2 sin(π/m))`. A true point-hub with unit
spokes requires `R(m) = 1`, i.e. `sin(π/m) = 1/2`, i.e. **m = 6** — the regular unit
hexagon, whose circumradius is exactly 1. This is the *only* m for which a symmetric
point-hub wheel is exactly realizable with unit fences.

- Checked against the table: n = 9's record area is `3√3/2`, exactly the area of a
  regular unit hexagon (six equilateral triangles of area `√3/4` each). This is
  consistent with hexagon geometry underlying that record, achieved with fewer
  fences (9) than a full rim+spoke hexagon wheel would need (12 = 6 rim + 6 spoke),
  because the record doesn't need every spoke drawn — only enough to keep both
  half-hexagon fields ≤ 1.
- Checked against the images: n = 18's outer shape is a regular unit-side 9-gon
  (area formula `9 cot(π/9)/4` matches exactly), and per the m=6 result above, unit
  spokes from a 9-gon's vertices *cannot* reach a common center (circumradius
  `1/(2 sin20°) ≈ 1.462 ≠ 1`). Re-reading `18.gif`: the spokes visibly do **not**
  meet at one point — they terminate at a small central inverted triangle (3 points),
  i.e. the hub degenerates from "1 coincidence point" to "pairwise T-junction
  landings forming a small sub-polygon," exactly the resolution the DOF count
  predicts for an over-determined single-point hub. Likewise n = 21's image
  (`21.gif`) shows spokes meeting at a small central *square*, not a point — same
  mechanism, different residual sub-polygon shape.

This is the central structural fact behind point 4 (§4): **symmetric skeletons are
a measure-zero special stratum**, realizable only at specific n/m combinations where
the extra coincidence equations happen to be satisfiable; asymmetric (all-T-junction,
no-forced-coincidence) skeletons are the *generic* stratum, realizable at every n,
with moduli dimension `n - 3` per §1.1.

### 1.4 Is the optimum isolated? (CONJECTURED, argument given, not a proof)

The objective (total enclosed area) is continuous on the `(n-3)`-dimensional moduli
space of a fixed skeleton, intersected with the closed region where every bounded
face has area ≤ 1. A maximum over a compact region cut out by inequality constraints
generically sits where enough constraints are *active* (tight, area exactly 1) that
the remaining tangent directions can't increase area — a KKT-type argument. If the
number of independent active area-cap constraints at the optimum equals `n - 3`, the
optimum is an isolated point (rigid up to the discrete skeleton choice) even though
the ambient skeleton is flexible. This matches the observed records: every image
inspected (§0, §1.3, and the group-(d) cases below) shows several faces sitting
visibly at or very near the size where they'd exceed 1 if perturbed outward — i.e.
plausibly several tight caps. **This is not verified with actual numeric area
computations per face** (the images are gifs, not annotated with exact coordinates);
it is offered as the load-bearing conjecture that justifies treating "optimize over
a fixed asymmetric skeleton" as a well-posed *finite-dimensional root-finding /
constrained-optimization* problem rather than a search over a continuum of tied
optima.

## 2. Combinatorial skeletons: separating discrete data from coordinates

Discrete data for a skeleton: a planar graph where each edge is a fence, each vertex
is either (a) an ordinary shared endpoint of ≥2 fences, or (b) a T-junction point
that is the endpoint of one fence lying in the relative interior of another. Given
this discrete graph plus a choice of which face is "outer" (unbounded), the
continuous data is exactly the `(n-3)`-dimensional moduli space of §1.1, and solving
for the area-maximizing point in it is the numeric part.

An **asymmetric family** = a rule producing, for a sequence of n (or n in some
target set), a discrete skeleton with no nontrivial automorphism (no rotation or
reflection symmetry of the graph), such that the coordinate-solve is well-posed
(§1.4) at every n in the family's domain. Below, four concrete skeleton-family
proposals, all **CONJECTURED** — none has been checked against the actual n=11/14/19
optimal coordinates (only against the qualitative *shape* of the record images).

### 2.1 Boundary-plus-T-junction-chain (best match to images; CONJECTURED)

Take a convex outer boundary of k unit fences (k-gon, ordinary corners, dimension-
neutral per §1.2). Add a chain of j interior fences one at a time: each new interior
fence has one endpoint at an existing vertex (already incident, free) and the other
endpoint landing via T-junction on a *previously placed* fence (boundary or interior)
— i.e. the interior chain is a path, not a fan (a fan would put every chord's foot
on the same central region, closer to a hub and hence more prone to the §1.3
over-determination if feet coincide). n = k + j. Because each chain step's target
fence is generically a *different* one, and the boundary arcs it cuts off differ in
length from step to step, the skeleton has no automorphism for generic (k, j) — it's
asymmetric by construction, not asymmetric by accident.

**Match to images (VERIFIED as a qualitative read, not a coordinate check):**
`11.gif`, `14.gif`, `19.gif` all show an outer polygon with 3–4 internal chords
crossing near the middle, each landing on another chord or on the boundary rather
than at one common point — consistent with a T-junction chain/pinwheel, not a
fan-to-a-point. `14.gif` in particular shows an inner near-square face bounded on
all sides by T-junctions on other interior chords, which is the chain mechanism's
signature (a late chain link closing off a small face using earlier links as its
walls, at ratio-1 cost — see M4 in §3).

Because (k, j) range independently, this family's n-values fill in *every* n above
some small threshold (not just the trivial polyomino n's or the wheel n's), which is
what's wanted for the open range — but this is a claim about **coverage of n**, not
about optimality: nothing here shows the chain construction actually *attains* the
recorded areas at n = 11, 14, 19, only that it's structurally the right shape of
object.

### 2.2 Spiral/pinwheel with independently growing arm count and arm length (CONJECTURED, unchecked)

A generalization of 2.1: instead of one chain, k "arms" radiating from a small
central asymmetric cluster, each arm built from a variable number of fences, arm
lengths not required equal. Arm count and per-arm length are independent parameters,
giving a 2-parameter family covering more n than 2.1 alone. No image evidence
distinguishes this from 2.1 at the resolution available; treat as a variant
worth testing numerically, not as an independently confirmed pattern.

### 2.3 Grid with a single moving defect (CONJECTURED, unchecked, and see §4's negative note)

Take an (a x b) polyomino skeleton (symmetric under its own dihedral group generically,
though most rectangles aren't square-symmetric) and perturb *one* cell boundary — e.g.
shear one column's fences off-axis (this is exactly the observed n=13 "perturbed
polyomino" mechanism, group (a) in the prior read, not group (d)). This produces
asymmetric skeletons parameterized by (grid shape, defect location, defect type), but
it is fundamentally a *perturbation* family (§3, moves M1/M-flap-like), not a
free-standing asymmetric generator — it needs a polyomino seed. Listed here for
completeness since the prompt asked for it, but it should not be conflated with
group (d) (11, 14, 19), which visually have **no** polyomino ancestry at all (no
right angles, no unit-square sub-cells visible in any of the three images).

### 2.4 Alternating two-cell-type boundary (speculative, CONJECTURED, weakest of the four)

A boundary that alternates two different unit-triangle/quad cell types in a ratio
that isn't a small integer ratio (motivated by trying to avoid periodicity forcing
symmetry). This is the least grounded of the four proposals — no image evidence
either supports or contradicts it, and no worked example was constructed. Flagged
explicitly as the weakest entry; do not treat as validated even provisionally.

## 3. Augmentation operators: local moves, Δn, Δarea, and the 1/2 threshold

Each move below is defined on the skeleton (§2), with generic Δn (new fences) and
Δarea (new enclosed area), assuming the move stays legal (no field exceeds area 1).

| Move | Description | Δn | Δarea | Ratio | Status |
|---|---|---|---|---|---|
| M1 flap | attach unit equilateral triangle to a free boundary edge (2 new fences, base = existing fence) | 2 | √3/4 ≈ 0.433 | 0.217 | DERIVED |
| M2 cell-1 | attach unit square sharing exactly 1 existing edge (3 new fences) | 3 | 1 | 0.333 | DERIVED |
| M3 cell-2 | attach unit square sharing exactly 2 existing edges (fills a concave notch, 2 new fences) | 2 | 1 | **0.5** | DERIVED |
| M4 chord-ear | one new fence, one endpoint at an existing vertex (free), other endpoint landing by T-junction on an existing fence, closing one new sliver face | 1 | determined by existing geometry, not free; bounded above by 1 (area cap) | up to ~1 in a single instance | DERIVED (mechanism), CONJECTURED (repeatability) |

**M4 is the interesting one and needs care.** The DOF count for it: the new fence
adds 1 new endpoint (2 new coordinates) with 1 length equation and 1 incidence
equation, net new moduli dimension = 2 - 1 - 1 = 0. So Δarea for an M4 move is *not*
a free design choice — it's algebraically determined by where the target fence and
anchor vertex already are. **DERIVED:** you cannot repeat M4 at a self-chosen
Δarea/Δn ratio; each application solves a fixed equation and returns whatever root
exists (0, 1, or finitely many solutions), so a *sustained* run of M4 moves at
ratio > 1/2 is not something you can engineer by construction — it would have to
happen to fall out of the specific coordinates at each step. No worked example in
this document achieves this; it is flagged as **open**, not refuted and not
demonstrated.

**On the 1/2 threshold generally.** The polyomino baseline (already established
before this doc, restated here for the ratio table): for A unit cells packed into a
near-square/staggered block, internal shared edges I ≈ 2A - O(√A), so edges
E = 4A - I ≈ 2A, giving area/edges → 1/2 as A → ∞. M3 (cell-2) is exactly this
move's per-step version and is the *only* move above that reaches 1/2 exactly and
repeatably (each application is again a cell-2 attachment, ratio 1/2 every time,
so it composes into an infinite family at rate 1/2, not above it).

**DERIVED, not merely asserted:** M1 and M2 are both strictly below 1/2, and the
gap is structural, not incidental — 1/2 requires each new bounded unit-area face to
share 2 of its sides with the *existing* structure (paying for only the other 2 out
of the new fence budget), and the *unit square* is the only regular tile that both
(a) exactly saturates the area-≤1 cap, and (b) admits 2-sided sharing against its
own kind (equilateral triangle also can 2-side-share, but its area √3/4 < 1 wastes
cap headroom — DERIVED from the M1 number 0.433 < 0.5 even discounting the flap's
1-sided-sharing handicap: a *2-sided* triangle attachment, Δn=1, Δarea=√3/4, ratio
0.433, is still below 1/2). So among regular-cell moves, square cells strictly
dominate triangle cells, and 1/2 is the resulting ceiling for that class of move.

**What is NOT established here:** whether *some* move outside this table —
specifically, an M4-chord-ear move whose target geometry happens to produce
Δarea close to 1 at Δn = 1, applied repeatedly along a growing boundary — could
sustain ratio > 1/2 over many steps. This is exactly the mechanism that would
explain group (d)'s existence as a *systematic* family rather than one-off ad hoc
solves, and it is the single most important open question this document leaves
unresolved. **CONJECTURED, unresolved:** no example was constructed either way.

## 4. Why asymmetry wins at the open n

**DERIVED, from §1.3 and §2.1 jointly, not a vibe:**

1. Fully symmetric wheel skeletons (m-fold rotational or dihedral arrangements,
   *every* spoke drawn from *every* rim vertex to one common center) are a
   different, stronger claim than an isolated m-way hub coincidence (§1.3 revised):
   a full rotational ansatz ties every vertex position to every other by the
   symmetry group, not just the m spoke feet to each other, so it is realizable
   only where the resulting exact geometric constraint holds — the hexagon m=6
   case (`sin(π/m) = 1/2`) being the only exact point-hub-to-every-vertex instance.
   An isolated m-way hub coincidence *within* an otherwise asymmetric skeleton is
   not similarly restricted — §1.3 (VERIFIED, n=11) shows it costs `m - 2` moduli
   dimensions and is realizable at generic n, no symmetry ansatz required; it is
   simply a worse budget allocation than spreading the same incidences across
   several smaller coincidences (or none). What remains true and sparse is the
   *fully symmetric wheel* family specifically (hexagon m=6 exact case; the
   9-gon/21-gon cases where the "hub" backs off to a small sub-polygon rather than
   a point, itself only working for the specific rim size chosen) — a **sparse,
   special set of n**, not a dense one.
2. Polyomino skeletons are a different special stratum: they need every interior
   face to be *exactly* a unit square (area exactly 1, saturating the cap) with
   axis-aligned right-angle corners — realizable exactly at n = (edge count of some
   minimum-edge A-cell polyomino), which is also a sparse, explicitly enumerable set
   of n (the "Trivial" column).
3. The open n are *by definition* everything not in either sparse set. At those n,
   no symmetric-wheel skeleton and no minimum-edge-polyomino skeleton exists that
   uses exactly that many fences (both families jump by more than 1 in n between
   consecutive members, and don't interleave to cover the gaps). Since §1.1 shows
   the *generic* (all-T-junction, no forced coincidence) skeleton family is realizable
   at **every** n with moduli dimension n - 3 ≥ 0 (for n ≥ 3), it is the only
   candidate family with no n-parity/coverage obstruction. Its generic realizations
   have no forced coincidences, hence no forced symmetry — asymmetric skeletons are
   not chosen for aesthetic reasons, they are what's left once the two symmetric
   strata are excluded by an n-coverage argument, not a proof that the true optimum
   at those n is asymmetric (a symmetric skeleton *could* in principle exist at an
   open n via some other, not-yet-considered symmetric ansatz — this document has
   only ruled out the two specific families checked, wheel and polyomino).

**This is a coverage/existence argument, not an optimality proof.** It explains why
asymmetric skeletons are *necessary* candidates at the open n (something has to fill
those n, and the two known symmetric families don't reach them) — it does not by
itself prove that the asymmetric skeleton beats every alternative on area; that's
established per-n only by the actual record (i.e., by whoever found the n=11/14/19/23
constructions and presumably checked no better configuration exists, which this
document has not independently re-verified).

## 5. Summary of status

| # | Question | Status |
|---|---|---|
| DOF formula `n - 3` | DERIVED |
| Corner vertices dimension-neutral | DERIVED |
| An m-way hub coincidence costs `m - 2` moduli, `dim = n - 3 - (m - 2)`; realizable at generic n, no symmetry ansatz needed | DERIVED, VERIFIED against n=11 split-hub (7 moduli, area 3.5372167764) and point-hub (6 moduli, area 3.5017721551, feasible but worse) |
| Full point-hub-to-every-vertex wheel realizable only at m=6 (hexagon) | DERIVED, VERIFIED against n=9 area and n=18/21 image re-read |
| n=11 split-hub skeleton reproduces the published record exactly | VERIFIED — `tests/records.rs::split_hub_pinwheel_n11`, area matches Tohanean's 3.53721+ record to 3.5372167764 |
| n=11 split-hub is the *global* optimum for its skeleton | OPEN — single SLSQP run from one traced initial guess, no multi-start |
| Other n=11 skeletons (not this boundary-plus-chain shape) | UNTESTED |
| Which of the 4 chords is the "odd one out" landing at H1 (vs. H2's 3-way point) | picked from pixel/image evidence only; the other 3 assignments (C, Q2, or F as the odd one out instead of... i.e. permuting which chord gets the ordinary T-junction and which three share the point) UNTESTED |
| Optimum is isolated (finite active-constraint count = n-3) | CONJECTURED (KKT-shaped argument, no per-face numeric check) — partially supported by n=11: 3 of 4 area constraints active at the optimum, matching 7 moduli minus... see note below |
| Boundary + T-junction-chain skeleton family | CONJECTURED, qualitatively matches 11/14/19 images; n=11 instance now VERIFIED as one concrete member (§1.3) |
| Spiral/arm-count family, grid-defect family, alternating-cell family | CONJECTURED, unchecked, listed in decreasing confidence order |
| M1/M2/M3 move ratios | DERIVED |
| Square cells dominate triangle cells for regular-tile moves | DERIVED |
| Ratio > 1/2 achievable sustainably (M4 repeated) | OPEN — neither constructed nor ruled out |
| Symmetric families cover only sparse n; asymmetric is the only n-complete candidate | DERIVED (coverage claim only, not an optimality proof) |

Note on n=11 and §1.4's active-constraint conjecture: the split-hub skeleton has
7 moduli dimensions and, at the numeric optimum found, 3 of its 4 bounded-face
area constraints sit at the cap (area = 1) with the 4th strictly below (0.5372...).
Three active constraints against 7 moduli does not by itself pin an isolated point
under the naive KKT count in §1.4 — the optimum found may sit on a positive-
dimensional tied-optimum locus, or the remaining directions may be constrained by
something §1.4 didn't enumerate (e.g. non-crossing / combinatorial-validity
boundaries rather than area caps). This was not resolved; flagged as part of the
same open "is this the global optimum" question above, not answered by it.

## 6. What would actually close group (d)

**n=11 done, VERIFIED**: the plan below (originally written before any numeric
solve existed) was carried out for n=11 — the "split hub" boundary-plus-chain
skeleton of §1.3, solved numerically (SLSQP from a traced initial guess) and
checked against `Configuration::validate()` in
`tests/records.rs::split_hub_pinwheel_n11`. It reproduces the published record
(3.53721+, Teodor Tohanean) exactly, to 3.5372167764. This upgrades §2.1 from
CONJECTURED to VERIFIED *for this one n and this one skeleton choice* — it does
not by itself establish the family for n=14, n=19, or rule out other n=11
skeletons; see the open items in §5's table (global optimality unverified,
other n=11 skeletons untested, the H1/H2 chord-assignment choice untested against
its 3 alternatives).

Remaining to actually close group (d): repeat this for n=14 and n=19 (the other
two group-(d) members), and — independent of n — either multi-start the n=11
solve to gain confidence in global optimality or find an argument that rules out
better skeletons for that n, since a single successful local solve doesn't
distinguish "this skeleton is optimal" from "this skeleton is merely valid and
happens to match the recorded digits by construction of the search target."

The original plan, for reference: pick one open n (e.g. 11, fewest fences,
smallest search space), enumerate boundary-plus-chain skeletons with k + j = 11
for small k, and numerically solve the `n - 3 = 8`-dimensional coordinate system
for each skeleton (maximize area subject to per-face ≤ 1), then compare against
the recorded area. That numeric solve was out of scope when this section was
first written (no coordinate data had been extracted from the images); it has
since been done for n=11 only.

## 7. A symmetry ansatz can collapse the moduli space to a point (DERIVED, measured on n=13)

The n=11 and n=8 solves both worked by tracing a record image, reading off a
skeleton, and solving. A third attempt — n=13 — reached a *valid* configuration
that nonetheless fell short of the published record, and the reason is worth
recording as a method rule rather than as an n=13 footnote.

**What happened.** `13.gif` looks mirror-symmetric about a horizontal axis. The
trace measured the two mirror-midpoint landmarks at y = 70.0 and y = 72.0 in a
160 x 140 image — a 2px discrepancy, read at the time as tracing noise. Exact
mirror symmetry was therefore imposed as a solve *ansatz*: paired vertices
constrained to be literal reflections of each other, axis-vertices pinned to the
axis.

The resulting solve is real and passes `Configuration::validate()` — total area
**4.0645952819** across 5 bounded faces (2 pentagons exactly at the area-1 cap,
2 quads at 0.9876, a tip triangle at 0.0893). But the published record is
4.07361+ (Bram Cohen), so it is short by **0.0090 (0.22%)**.

**Why.** Count the dimensions. The skeleton's unconstrained moduli dimension is
**5** — `n - 3` corrected by the coincidence rule of §1.3, `Σ(m_i - 2) = 5` across
its four coincidence vertices; see §8 for the count. After imposing the mirror
ansatz, gauge-fixing, and the
active area-cap constraint, the solve had effectively **0** free moduli left —
it was not optimizing over a space, it was evaluating a single determined point.
A determined point is not an optimum; it is whichever point the ansatz happened
to select. The 0.22% is the price of the ansatz, not a property of the skeleton.

**The rule.** *A symmetry that holds to within a pixel in a low-resolution trace
is not evidence of exact symmetry.* Two landmarks agreeing to 2px in a 160px
image constrain the true configuration to roughly 1% — nowhere near enough to
justify collapsing a 10-dimensional moduli space onto its symmetric stratum.
Before imposing any symmetry ansatz, compare the moduli dimension it leaves
against the number of active constraints expected at the optimum (§1.4): if the
remainder is 0 or negative, the ansatz is doing the optimizer's job for it and
the result should be read as a *feasible point*, not a maximum.

Note the asymmetry between the two failure directions. Solving in the full
moduli space and *discovering* a symmetric optimum costs only solver time and
loses nothing. Solving inside an assumed-symmetric stratum and being wrong is
silent: the solve converges, validates, and reports a plausible number with no
signal that a better configuration was excluded by construction. Prefer the
full-moduli solve and let symmetry emerge, exactly as §1.3's split-vs-point-hub
test at n=11 let the *coincidence structure* emerge rather than assuming it.

**Status of n=13 in this crate.** The symmetric construction is encoded in
`tests/records.rs::grid_wedge_n13` as a verified-valid configuration at
4.0645952819, explicitly *not* claimed to be the record. Closing the remaining
0.0090 requires re-solving the same skeleton with the symmetry constraints
dropped (all vertices free, gauge-fixed only), multistarting off perturbations
of the symmetric point — the symmetric point may well be a saddle in the larger
space, so a local solve started exactly there can sit still.

## 8. Second independent confirmation of dim = n − 3 − Σ(mᵢ − 2), on n=13 (VERIFIED)

§1.3 derived the coincidence-corrected moduli formula

```
dim = n - 3 - Σ_i (m_i - 2)
```

summed over vertices where `m_i >= 3` fence-endpoints coincide, and verified it on
the n=11 skeleton it was derived from (a 3-way coincidence costing 1, a 4-way
point hub costing 2). The n=13 skeleton (`tests/records.rs::grid_wedge_n13`)
provides a second confirmation, on a skeleton the rule was *not* derived from,
and at a larger total correction than n=11 exercised.

**The count.** Endpoint degrees, read off the committed fence list rather than
hand-transcribed:

| vertex | endpoint degree m | cost (m − 2) |
|---|---|---|
| C (centre, both dividers cross) | 4 | 2 |
| TM, LM, BM (boundary midpoints where a divider lands) | 3 each | 1 each |
| TL, TR, P, BR, BL (ordinary corners) | 2 each | 0 each |
| RM, UT, LT (T-junctions, sole endpoint of their fence) | 1 each | 0 each |

`Σ(m_i - 2) = 2 + 1 + 1 + 1 = 5`, so `dim = 13 - 3 - 5 = 5`.

**Cross-check by raw count**, independent of the formula: 12 vertices give 24 raw
coordinates; the constraints are 13 unit-length equations plus 3 T-junction
collinearity equations = 16; subtracting the 3 rigid motions gives
`24 - 16 - 3 = 5`. The two routes agree.

**Cross-check against measurement**: a numerical Jacobian rank computation at the
solved point returned dimension 5, full rank with no degeneracy at the symmetric
point. Three independent routes, same answer.

A bookkeeping note, since the intermediate numbers differ between routes: the
Jacobian computation reported 20 free coordinates against 15 independent
constraints (= 5), where the raw count above gives 21 against 16 (= 5). The
discrepancy is one coordinate and one constraint on each side and cancels
exactly — consistent with the numerical setup having eliminated one T-junction by
direct parametrization (building RM in as a point of the UT-LT chord rather than
carrying it as a free point plus a collinearity equation). The *net* dimension,
which is the quantity the rule predicts, agrees on all three routes.

**Correction to an earlier statement.** §7 of this document, and the n=13 commit
message, quote the skeleton's moduli dimension as `n - 3 = 10`. That is the
*uncorrected* generic count of §1.1 and is wrong for this skeleton: it ignores
the four coincidence vertices. The correct dimension is 5. This does not change
§7's conclusion or its magnitude — the mirror-symmetry ansatz still left
effectively 0 free moduli, and the point of §7 is that 0 is not enough to
optimize over. It changes only what the ansatz was being compared against: the
collapse was 5 → 0, not 10 → 0. The lesson stands and the arithmetic behind it
is now right.

**The n=8 skeleton** (`tests/records.rs::kinked_hexagon_n8`) has exactly one
coincidence vertex, BA, at degree 3 (fences BL-BA, BA-BR, BA-M), so
`Σ(m_i - 2) = 1` and the rule predicts `dim = 8 - 3 - 1 = 4`. The raw count
agrees: 18 coordinates, 8 lengths + 3 collinearities = 11 constraints, minus 3
rigid motions, = 4.

Its mirror-symmetric stratum, by hand count, has dimension 1: 9 free parameters
under the reflection (Apex, BA, M contribute their y only; SL, BL, PL contribute
both coordinates and determine SR, BR, PR), less 1 residual gauge freedom, against
5 independent lengths and 2 independent collinearities under the symmetry — `8 - 7
= 1`. **This is why n=8's symmetry ansatz succeeded where n=13's failed.** n=8's
ansatz left a live modulus to optimize over and the solve found a genuine interior
critical point on it; n=13's left none, so its solve could only evaluate the single
point the ansatz determined. The distinction is not that one problem was symmetric
and the other was not — it is entirely a question of what dimension survives the
ansatz, which is precisely the check §7 prescribes.

### 8.1 n=8: the rule confirmed by Jacobian rank, and the ansatz discharged (VERIFIED)

§8 predicted `dim = 4` for the n=8 skeleton from the coincidence rule (one
degree-3 vertex, BA). Measured, at the solved point, by complex-step
differentiation of the 11 constraints (8 unit-length + 3 collinearity) against
all 18 raw coordinates:

```
singular values: 3.490 3.397 2.985 2.942 2.851 2.706 2.159 1.958 1.295 1.084 0.648
rank = 11   ->   dim = 18 - 11 - 3 = 4
```

The rank cut is clean, not a judgement call: the smallest singular value is
0.648, i.e. 0.186 x the largest, with no near-zero tail anywhere. Rank is 11 at
40 random points of the constraint variety as well, so the count is structural,
not a property of the symmetric point. **Prediction confirmed.** Together with
§8's n=13 result this is the rule checked on three skeletons (n=11 derived,
n=13 and n=8 predicted-then-measured).

The 4-dimensional tangent space decomposes under the mirror involution as
**1 symmetric + 3 antisymmetric**, independently reproducing §8's hand-count of
a 1-dimensional symmetric stratum.

**Discharging the ansatz.** n=8's optimum was originally found under an imposed
mirror-symmetry ansatz — the same move that cost n=13 0.22% (§7). Re-solved
without it (all 18 coordinates free, gauge-fixed only, 480 symmetry-breaking
multistarts across noise scales 1e-3 to fully random): 362 feasible
convergences, **all 362** returning to the same configuration, **none**
exceeding it. Max feasible total found 2.0893244080014.

The perturbations genuinely left the symmetric stratum — recovered solutions'
residual asymmetry is 2.6e-10 median, so the runs came *back* to symmetry rather
than never leaving. This matters because criticality proves nothing here: the
objective and constraints are both symmetric, so the gradient at a symmetric
point vanishes in every antisymmetric direction automatically, and a saddle
would look identical to a maximum by that test. The reduced Hessian (Lagrangian
Hessian projected onto the tangent space) settles it:

```
-1.3982714  (symmetric)
-0.8686548  (antisymmetric)
-0.5075700  (antisymmetric)
-0.0160071  (antisymmetric)
```

Negative definite — a strict local maximum, with strictly negative curvature in
all three symmetry-breaking directions. So n=8's symmetry is **emergent, not
imposed**, and the record stands on the full moduli space rather than on a
stratum chosen in advance.

**The general point, stated once.** §7's rule is *not* "never use a symmetry
ansatz." n=8 and n=13 used the same ansatz to opposite effect. The difference is
entirely what dimension survives it: n=8 kept 1 of 4 and found a genuine
interior critical point on it; n=13 kept 0 of 5 and could only evaluate the
point the ansatz determined. An ansatz leaving positive dimension is a
legitimate search shortcut that still needs discharging afterwards, exactly as
done here. An ansatz leaving 0 is not a search at all.

**Numerical note.** The polished optimum is 2.0893244080014, against the
2.0893244027 first recorded here. The difference (5.3e-9) is convergence, not a
better configuration: the originally-stored coordinates satisfied the
constraints only to ~1.6e-8 residual, and re-polishing to ~1e-16 moves the area
by that order. Same critical point. `tests/records.rs::kinked_hexagon_n8` now
stores the polished coordinates, symmetrized so paired vertices are exact
negations and axis vertices sit exactly on x=0 (unit-length residuals 2.2e-16).
Flagged explicitly so the change isn't later mistaken for an improved record.

### 8.2 n=8: exact algebraic certificate for the area (VERIFIED)

§8.1 established that `kinked_hexagon_n8`'s optimum is a smooth interior
critical point (no area cap active) on a moduli space whose mirror-symmetric
stratum is emergent and 1-dimensional. That makes the record area a genuine
algebraic number — the solution of a polynomial critical-point system — not
just a converged float. This section derives its exact minimal polynomial.

**Reduction to the symmetric stratum.** Parametrize the symmetric locus by
`Apex = (0, ay)`, `SL = (-sx, sy)`, `SR = (sx, sy)`, `BL = (-bx, by)`,
`BR = (bx, by)`, `BA = (0, 0)`, with `PL, PR, M` forced onto the vertical axis
of symmetry. Two of the eight unit-length equations collapse to exact
rationals independent of everything else: `PL-PR` unit length forces
`PL = (-1/2, py)`, `PR = (1/2, py)`; `BA-M` unit length forces `M = (0, 1)` (so
`py = 1`). The T-junction condition `PL` on segment `Apex-SL` at parameter `t`
gives `t·sx = 1/2` and `ay + t(sy - ay) = 1`. Together with the three
remaining unit-length equations (`Apex-SL`, `SL-BL`, `BL-BA`), this leaves a
system of 5 polynomial equations in 6 unknowns `(ay, sx, sy, bx, by, t)` — a
1-dimensional variety, matching §8's measured 1-dimensional symmetric stratum.

**Criticality.** The area (`= 2·`shoelace of the symmetric hexagon
`Apex,SL,BL,BA,BR,SR`) is extremized along this curve exactly where the
augmented 6×6 Jacobian — the 5 constraint gradients plus the area gradient,
all with respect to the 6 unknowns — is singular. That determinant condition
plus the 5 constraints is a 0-dimensional system in 6 unknowns, solved by
elimination (`sympy.resultant`, chained: eliminate `bx` from the `detJ=0`
condition against the `BL-BA`/`SL-BL` pair, then eliminate `sy`, isolating
`t`; separately substitute the area variable `A` for `bx` via its affine
relation and eliminate `sy` then `t` to isolate `A`). Every elimination step
produced large spurious factors independent of the eliminated-toward variable
(artifacts of clearing denominators introduced by the rational
parametrization); these were discarded by `sympy.factor_list`, keeping only
factors that actually depend on the target variable.

**Result — the area's exact minimal polynomial**, degree 24, `Area = A`:

```
1099511627776*A^24 - 17763984736256*A^22 + 2473901162496*A^21
+ 166635872714752*A^20 - 293013406351360*A^19 - 378562762768384*A^18
+ 2106837956558848*A^17 - 1735106797568000*A^16 - 4633311266734080*A^15
+ 8290667836659712*A^14 + 2766034138808320*A^13 - 12499528462034672*A^12
+ 2323795836413312*A^11 + 8352756631200992*A^10 - 3611489073935488*A^9
- 2255207841503568*A^8 + 1546845296617728*A^7 + 64037587301256*A^6
- 215938761119392*A^5 + 37632088116392*A^4 + 2917102422976*A^3
- 1303252698872*A^2 + 96772141984*A + 186178441 = 0
```

(leading coefficient `2^40`; content — the gcd of all 25 integer coefficients
— is 1, so this is the primitive form.)

**Verification.**
- **Irreducibility over ℚ**: `sympy.factor_list` on the primitive polynomial
  returns it unchanged as a single irreducible factor of multiplicity 1. Since
  the area is a root of this irreducible polynomial, this *is* its minimal
  polynomial and the area's degree over ℚ is exactly 24 — not an artifact of
  an unreduced resultant.
- **Root match**: the critical-point system `(ay, sx, sy, bx, by, t)` was
  re-solved from the known float solution with `mpmath.findroot` at 600-digit
  working precision (Newton on the 3-variable reduced system `(bx, sy, t)`,
  with `t`'s own minimal polynomial — also degree 24, independently derived
  and confirmed irreducible along the way — checked to residual `~1e-246` at
  250 digits). The resulting area value satisfies the degree-24 polynomial
  above to residual `~1e-582` at 600-digit precision: 580+ digits beyond the
  precision used to find the candidate, ruling out coincidence.
- **Isolation**: the polynomial has 12 real roots; the matching one
  (`2.0893244080014165918...`) is isolated from its nearest real neighbors
  (`1.1541872908...` and `-2.0350440310...`) by more than 0.9, so there is no
  ambiguity about which root is the geometric solution.
- A companion degree-6 factor and a degree-36 factor also appeared in the
  elimination for other reasons (extraneous branches of the same resultant
  chain, e.g. the mirrored/negated configuration or non-optimal critical
  points on the same stratum); both were checked numerically against the
  600-digit area value and ruled out (residuals `~2.7e3` and `~1.2e28`
  respectively — not roots).

**Solvability in radicals: undetermined.** `sympy.polys.numberfields.galoisgroups.galois_group`
only supports degree ≤ 6, and no other Galois-group-capable tool (PARI/GP,
Magma) is available in this environment. Whether the degree-24 extension is
solvable — and therefore whether the record area has a closed radical form —
is open.

**High-precision decimal** (100 digits, from the 600-digit Newton solve):

```
2.089324408001416591804632432261812769506742933965250906477681404686273919752982712347650628283051578
```

This is a genuine refinement of the previously-recorded `2.0893244080014` —
consistent with it to all 14 given digits, extending it by 86 more.

### 8.2 n=13: the cap is not the whole gap — the record needs a different skeleton (VERIFIED)

A natural hypothesis for n=13's 0.009 shortfall (§7): since two pentagons sit
exactly at the area-1 cap at our optimum, maybe the published 4.07361 is *this
same construction* with its fields nudged slightly over 1 — i.e. an invalid
configuration reported as a record. If so, relaxing the cap to `1 + ε` should
climb straight to the record at small ε.

Tested directly by a cap sweep on the exact `grid_wedge_n13` skeleton (same
symmetric SLSQP solve, cap set to `1 + ε`, warm-started up the ε grid):

```
ε=0      total 4.0645952819   pentagons 1.000000 (active)
ε=0.001  total 4.0653799       pentagons 1.001000 (active)
ε=0.005  total 4.0678819       pentagons 1.005000 (active)
ε≥0.008  total 4.0685197304    pentagons 1.007517 (cap no longer binding)
ε=0.20   total 4.0685197304    (unchanged — plateau)
```

The total does **not** rise to the record. It **plateaus at 4.0685197304** once
ε ≳ 0.008, because at that point the cap stops binding and the solve sits at the
skeleton's *unconstrained* symmetric maximum (confirmed as the symmetric global
by 60 random restarts with the cap dropped entirely). The record 4.07361 is
**above that plateau by 0.0051** — so even with fields allowed to be arbitrarily
oversized, this topology cannot reach it.

Decomposing the 0.009015 gap: relaxing the cap buys at most **0.003924** of it
(43%), and the remaining **0.005090** is a hard ceiling of the skeleton itself,
not a cap violation. The sensitivity at the true cap is `dA/dε ≈ 0.80` and
decays to 0 at the plateau, so there is no small ε that reaches the record.

**Verdict: the hypothesis is refuted.** The record is not `grid_wedge_n13` with
slightly-oversized fields; less than half the gap is cap-related and the rest is
topological. Cohen's construction is a genuinely different skeleton than the one
traced here — consistent with the independent finding that 13.gif's right-side
cluster was mistraced. (Caveat of scope: this sweep is under the mirror-symmetry
ansatz, so 4.0685197304 is the symmetric unconstrained ceiling; an asymmetric
solve of the *same* skeleton could differ. But the cap-hypothesis is settled
regardless — the cap explains under half the gap either way.)
