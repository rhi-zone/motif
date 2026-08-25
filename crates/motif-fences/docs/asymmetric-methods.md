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

### 1.3 Hub coincidences: the over-determination that forces symmetry (DERIVED)

Contrast with a "wheel" skeleton where m spoke-fences all meet at one common
interior hub point. Requiring m unit-length points `P_1, ..., P_m` (the spokes' inner
endpoints) to all equal one location costs `2(m-1)` equations (pairwise-equal-to-P_1),
but discharges only `m` incidence requirements (each spoke's inner endpoint lies on
"another fence" — trivially true once it coincides with any other spoke's endpoint).
For m ≥ 3 this is over-determined by `2(m-1) - m = m - 2` equations relative to the
generic budget. A single-point m-spoke hub is **not** a generic realization; it
exists only where the excess equations become dependent, which happens exactly when
a symmetry ansatz (e.g. m-fold rotation) makes them consequences of each other rather
than independent cuts.

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

1. Symmetric skeletons (wheels, m-fold rotational or dihedral arrangements) require
   hub or rim coincidences that are algebraically over-determined in the generic
   moduli space (§1.3: excess = m - 2 equations for an m-fold point-hub). They
   become realizable only when a discrete symmetry ansatz collapses the excess
   equations into dependent ones — which happens only for special (n, m) pairs (the
   hexagon m=6 exact case; the 9-gon/21-gon cases where the "hub" backs off to a
   small sub-polygon rather than a point, itself only working for the specific rim
   size chosen). This is a **sparse, special set of n**, not a dense one.
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
| Hub over-determination, excess = m-2 | DERIVED |
| Point-hub realizable only at m=6 (hexagon) | DERIVED, VERIFIED against n=9 area and n=18/21 image re-read |
| Optimum is isolated (finite active-constraint count = n-3) | CONJECTURED (KKT-shaped argument, no per-face numeric check) |
| Boundary + T-junction-chain skeleton family | CONJECTURED, qualitatively matches 11/14/19 images |
| Spiral/arm-count family, grid-defect family, alternating-cell family | CONJECTURED, unchecked, listed in decreasing confidence order |
| M1/M2/M3 move ratios | DERIVED |
| Square cells dominate triangle cells for regular-tile moves | DERIVED |
| Ratio > 1/2 achievable sustainably (M4 repeated) | OPEN — neither constructed nor ruled out |
| Symmetric families cover only sparse n; asymmetric is the only n-complete candidate | DERIVED (coverage claim only, not an optimality proof) |

## 6. What would actually close group (d)

To turn §2.1 from a plausible shape into a real generating method: pick one open n
(e.g. 11, since it has the fewest fences and smallest search space), enumerate
boundary-plus-chain skeletons with k + j = 11 for small k, and numerically solve the
`n - 3 = 8`-dimensional coordinate system for each skeleton (maximize area subject to
per-face ≤ 1), then compare against the recorded area 3.53721. Matching that number
to the precision available would upgrade §2.1 from CONJECTURED to VERIFIED for that
n, and give real (not gif-estimated) coordinates to check the M4 ratio question in
§3 against. That numeric solve was out of scope here (no coordinate data was
extracted from the images) and is the natural next step.
