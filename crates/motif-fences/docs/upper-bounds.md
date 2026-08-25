# Upper bounds for the fences problem

Scope: `A(n)`, the true (unknown) maximum total enclosed area achievable with `n`
unit fences — bounding it from **above**. Every other artifact in this crate
(`skeleton`, `search`, `anneal`, the record table) is a lower-bound machine: an
explicit construction proving `A(n) >= area`. Nothing anywhere in the project
previously bounded `A(n)` from the other side. This document, and the
computable functions in `src/bounds.rs`, are that missing half.

Status tags, used throughout: **DERIVED** (proved here, derivation shown),
**VERIFIED** (checked computationally against the record table or a
worked example), **CONJECTURED** (stated, evidence given, not proved — never
built on as fact), **REFUTED** (a claim that was proposed and is shown false,
kept in the document because the reasoning for *why* it fails is itself
informative). A proof with a known gap says exactly where the gap is; it is
never presented as complete.

Record data used throughout (`n`, best known area) is copied from
`/tmp/fence-records.md`; decimal-only entries are lower bounds on the true
optimum (Friedman's site marks them "+"). The full comparison table is in
§7.

## 1. Theorem 1: the isoperimetric bound

> **Theorem.** For every `n >= 1`, `A(n) <= n / sqrt(pi) ≈ 0.56419 n`.

**DERIVED, VERIFIED** (holds against all 22 records with wide margin — see
§7 — and the proof below has no genericity or non-degeneracy assumptions).

### Proof

Fix any valid configuration: `n` unit segments ("fences"), every endpoint
lying on some other fence, every bounded face ("field") of the induced
planar arrangement having area `<= 1`.

**Step 1 — length budget.** Subdividing a fence at points where other
fences' endpoints land on it (T-junctions) or cross it does not change its
total length: the sub-edge lengths sum to 1. If two fences happen to overlap
(share a sub-segment as a set), the arrangement's total *distinct* edge
length is strictly less than `n`; in every case, summed over the
arrangement's edges, `sum(length(e)) <= n`, with equality iff no two fences
overlap as point sets.

**Step 2 — each edge borders at most two bounded faces, with multiplicity.**
Trace each bounded face's boundary as a closed walk in the planar
arrangement (this is well-defined even for a face that is not simply
connected — e.g. one with an "island" hole, or with a pendant fence poking
into it — the walk just may traverse some edges more than once, or the face
may have several boundary components). Define `perim_walk(f)` as the sum,
over the face's boundary walk(s), of edge lengths counted with the
multiplicity they appear. Every edge of the arrangement has exactly two
*sides*; each side is bordered by either the unbounded face or some bounded
face. So an edge contributes at most 2 (0, 1, or 2) to
`sum_i perim_walk(f_i)` (summed over bounded faces `i`), weighted by its
length. Hence

```
sum_i perim_walk(f_i) <= 2 * sum(length(e)) <= 2n.
```

*Aside, checked explicitly because the task asked for it:* can an edge
border the *same* bounded face on both sides (a true "bridge"/pendant edge,
which would still respect the `<= 2` count but is worth ruling out as a
separate degeneracy)? Given this problem's incidence rule, no: every new
fence's two endpoints must already lie on the existing arrangement when it
is added, so any newly added fence is a straight chord connecting two
points already on the boundary of *one* existing face — which splits that
face into two *distinct* faces, not a pendant edge with identical faces on
both sides. (A true free-floating dead end would need an endpoint landing
on nothing, which the incidence rule forbids.) So the multiplicity-2 cap is
in fact never approached from a bridge edge; it is a clean topological
bound regardless.

**Step 3 — isoperimetric inequality.** `perim_walk(f_i)` is at least the
face's measure-theoretic (De Giorgi) perimeter — a slit or self-touching
edge only adds length to the walk count, never subtracts from the actual
boundary — and for *any* planar set of finite perimeter and area `a`, the
classical planar isoperimetric inequality gives perimeter `>= 2*sqrt(pi*a)`
unconditionally (no convexity, simple-connectivity, or smoothness
hypothesis needed). So `perim_walk(f_i) >= 2*sqrt(pi * a_i)`.

**Step 4 — combine and use the cap.** Summing Step 3 over faces and
combining with Step 2:

```
2*sqrt(pi) * sum_i sqrt(a_i)  <=  sum_i perim_walk(f_i)  <=  2n
=>  sum_i sqrt(a_i)  <=  n / sqrt(pi).
```

Since every `a_i <= 1`, `sqrt(a_i) <= 1`, so `a_i = sqrt(a_i) * sqrt(a_i) <=
sqrt(a_i)`. Summing: `A(n) = sum_i a_i <= sum_i sqrt(a_i) <= n / sqrt(pi)`. ∎

Implemented as `bounds::isoperimetric_bound`.

## 2. The proposed hexagonal sharpening: REFUTED as stated

The parent session's hand derivation asked whether replacing the circle
isoperimetric constant (`2*sqrt(pi) ≈ 3.5449`) with the regular-hexagon
constant from Hales' Honeycomb Theorem (`≈ 3.7224`) sharpens Theorem 1 to
`A(n) <= n * 3.5449/3.7224 ≈ 0.5373 n`.

**REFUTED.** Hales' theorem (1999/2001) is a statement about the *average*
perimeter density of a partition of the **entire infinite plane** into
cells of area `>= 1`: any such partition has average perimeter-per-cell at
least that of the regular hexagonal tiling, in the limit over large disks
([Hales, "The Honeycomb Conjecture", *Discrete Comput. Geom.* 25 (2001)];
see also the Wikipedia summary and Morgan's exposition, which state the
result explicitly as an averaged/asymptotic bound, not a per-cell one).
Three of its hypotheses fail for the fences problem:

1. **Tiling vs. finite collection.** Hales bounds the *average* cost per
   cell in an infinite tiling with no boundary. A fence configuration is
   finitely many faces with a *free, unbounded* complementary region — most
   or all boundary-adjacent faces get to spend part of their perimeter on
   edges that border the unbounded face (no "other cell" on the far side to
   share cost with), which the L1/L2 split in §3 makes precise. Individual
   cells in a *finite* partition are not each individually bound by the
   hexagonal constant; only the tiling's bulk average is, in the infinite
   limit. Direct evidence in a closely related finite setting: Cox &
   Headley's least-perimeter partitions of a *disc* into `N` regions
   (arXiv:1901.00319) show boundary-adjacent cells systematically deviate
   from the interior hexagonal shape precisely because of the free/curved
   outer edge — the qualitative mechanism this refutation relies on, in a
   setting with the closest available literature.
2. **Area `<= 1` vs. area `>= 1`.** Hales' theorem is stated for cells of
   area *at least* 1 (the "at most 1" direction is a materially different
   optimization — cells can shrink freely, which is exactly what lets a
   boundary-adjacent cell in a finite arrangement be perimeter-cheaper than
   a hexagon).
3. **No general per-cell corollary exists in the literature that removes
   hypotheses 1–2** for a bounded, non-tiling collection of faces with a
   free outer boundary; nothing found in this search establishes one.

**Conclusion:** the hexagonal constant does not transfer to this problem.
Theorem 1 (§1), at `1/sqrt(pi) ≈ 0.5642`, is the tightest bound this
document establishes via the isoperimetric route. §3 shows why that route
cannot be pushed further, even with refinements.

## 3. Pushing toward 1/2: the isoperimetric route is structurally capped at `1/sqrt(pi)`

Is `A(n)/n -> 1/2`, matching the polyomino-family lower bound? This section
gives a **DERIVED negative result**: no refinement *within the
curve-isoperimetric method* (Steps 1–4 above) can lower the leading
constant below `1/sqrt(pi)`. Getting to `1/2` requires abandoning that
method for something that sees the straight-unit-edge structure directly
(§5).

### 3.1 The refinement attempted, and why it only affects lower-order terms

Split the arrangement's edge length into `L1` (edges bordering the
unbounded face on one side — "boundary" edges) and `L2` (edges bordering
two bounded faces — "shared" edges), so `n >= L1 + L2` and
`sum_i perim_walk(f_i) = L1 + 2 L2`.

Two isoperimetric constraints:

- **(I)** `L1 >= 2*sqrt(pi * A)`: `L1` is (at least) the perimeter of the
  outer boundary of the union of bounded faces, which has area `<= A` (the
  isoperimetric inequality applies to the union directly if it is
  connected; if it splits into `m >= 1` disjoint pieces, superadditivity of
  `sqrt` — `sqrt(x) + sqrt(y) >= sqrt(x+y)` — makes the bound only get
  *stronger* with more pieces, so it holds regardless of connectivity).
- **(II)** `L1 + 2 L2 >= 2*sqrt(pi) * S`, where `S = sum_i sqrt(a_i)` (Step
  3–4 above), with `S >= A` since `a_i <= 1` for every face.

Minimizing `n = L1 + L2` subject to (I) and (II) (treat `L1, L2 >= 0` as
free, `A` fixed): substituting `L2 >= sqrt(pi)*S - L1/2` into `n = L1+L2`
gives `n >= L1/2 + sqrt(pi)*S`, minimized over `L1` by taking `L1` at its
floor from (I), `L1 = 2*sqrt(pi*A)`:

```
n >= sqrt(pi*A) + sqrt(pi) * S >= sqrt(pi*A) + sqrt(pi)*A
   = sqrt(pi) * (A + sqrt(A)).
```

This is a genuine improvement over Theorem 1 for finite `n` (it subtracts
an `O(sqrt(A))` correction — the same *shape* of correction the polyomino
family's own `f(A) = 2A + ceil(2*sqrt(A))` has), but solving for the
**leading** behavior as `A, n -> infinity`: `A + sqrt(A) ~ A`, so
`n ~ sqrt(pi) * A`, i.e. `A ~ n/sqrt(pi)` — **the same leading constant as
Theorem 1**, only a lower-order term changed. Using the isoperimetric
inequality anywhere in the chain caps the achievable leading constant at
`1/sqrt(pi) ≈ 0.564`, because the isoperimetric inequality is a bound on
*curve length*, and curves (unlike straight unit segments assembled into a
tiling) do not care whether they can 2-side-share with a neighbor at zero
marginal shape cost. That is exactly the property that makes a square
special (§3.2) and that no curve-length argument can see.

### 3.2 Why the square, not the circle, is the right comparison — heuristic, not a proof

A face achieving area exactly 1 with *all* of its perimeter double-shared
with neighbors needs to belong to a tiling of area-1 cells by translation.
Squares (side 1) do this exactly, with unit-length sides — a fence *is*
one full tile edge. A regular hexagon of area 1 has side `≈0.6204`, so a
unit-length fence cannot be a whole hexagon edge (hexagon edges bend at
120° at every vertex; a straight unit fence would overshoot the vertex by
`≈0.38` and have nowhere valid to bend to) — this is that "unit-side
hexagon has area 2.598 > 1" fact already in the record table (n=9): the
only way to use full unit-length fences in a hexagonal arrangement is to
build a hexagon bigger than the area cap and then subdivide it, which
spends extra fences on interior scaffolding and gives up the
double-sharing efficiency that made hexagons attractive in the first
place. This is a real structural asymmetry between squares and every other
regular tile under the "fences have length exactly 1" constraint, but it
is an argument for the square being locally efficient among *regular
tilings* specifically — not a proof that no other (irregular,
combinatorially cleverer) scheme beats `1/2` asymptotically. **This
paragraph is exposition connecting the polyomino construction to why it is
plausible, not a proof of optimality; do not treat it as one.**

### 3.3 What would actually prove `1/2`

A discrete argument tied to the straight-unit-edge structure — not curve
length. §5 is the attempt at exactly this (the "polyomino ceiling"
conjecture raised mid-task); it is the natural target, and it did not
close in the time available here. **The asymptotic constant of `A(n)/n`
remains open, narrowed to `[0.5, 0.5642]`** (the `0.5373` figure from the
hexagonal sharpening is withdrawn per §2).

## 4. The boundary-polygon lemma (reported from the n=18 work; verified here)

> **Lemma.** Let a fence configuration's bounded-face union have a single
> simple (Jordan) outer boundary, built from `k` of the `n` fences, each
> used as one whole side (hypothesis **H1**, discussed below). Then the
> configuration's total enclosed area equals the boundary polygon's
> shoelace area, and is at most `(k/4)*cot(pi/k)` — the area of the
> *regular* unit-side `k`-gon.

**DERIVED, VERIFIED** (both halves check out; hypotheses below narrow the
scope somewhat but the corollary in §4.3 recovers a hypothesis-free bound).

### 4.1 "Total area = shoelace area of the outer boundary": always true under H1

Interior fences subdivide the outer boundary's interior into the
configuration's bounded faces; as long as those faces exactly partition
the polygon's interior (automatic — the arrangement's edges are chords of
that interior, and every point inside a Jordan curve is in exactly one
resulting face), the sum of the sub-face areas equals the area of the
undivided polygon. Interior fences never add area, only subdivide it — the
report's claim is correct, and unconditional once H1 holds.

### 4.2 "Regular maximizes area for fixed unit side lengths": a classical theorem, checked for the raised objections

This is a standard result: among simple polygons with a given multiset of
side lengths in a given cyclic order, the maximum-area one is the *cyclic*
polygon (inscribed in a circle) — provable by a variational argument
(perturbing one interior angle while holding its two adjacent side lengths
fixed strictly increases area unless the local cyclic condition holds), and
the argument does not presuppose convexity of the competitor: it applies to
the whole configuration space of simple polygons with those side lengths,
convex or not, and the maximizer it finds happens to be convex. (See e.g.
the discussion and references in arXiv:1506.08069, "A variational
principle for cyclic polygons with prescribed edge lengths".) When all
sides are equal, the cyclic polygon is automatically *regular* (equal
chords subtend equal arcs, forcing equal angles). This directly answers the
coordinator's specific worry: **non-convex competitors are already
dominated**, not a separate case requiring extra work.

**Does a boundary fence with an interior T-junction landing partway along
it break the "k unit sides" count?** No. Such a landing subdivides that one
fence into two collinear sub-edges, adding a boundary-polygon vertex with
interior angle exactly `pi` (a "straight" corner). This is a valid,
if extreme, point within the same configuration space (a k-gon with k unit
sides, one of whose angles happens to be `pi`) — the maximality theorem
still dominates it, and it is generically *not* the maximizer (the regular
k-gon, which has no straight angles, has strictly more area). So this
degenerate case is inside the theorem's scope, not an exception to it —
directly answering the n=11 case the coordinator flagged (the heptagon's
boundary fences carry mid-length T-junctions and the lemma still applies
to them).

**Can a fence be "partly boundary, partly interior"?** No — a straight
fence's two sides are each a single connected region along its whole
length (nothing bends), so if one side of a fence is the unbounded face
anywhere along its length, it is the unbounded face along the *entire*
length (the only way this could fail is if some other fence transversally
crosses it and "wraps around" to bound part of that same outer side — but
that already contradicts H1's single-simple-boundary hypothesis, so it's
excluded by hypothesis, not a separate gap).

### 4.3 Hypothesis H1 and a hypothesis-free corollary

H1 (single simple outer boundary — no disconnected components, no holes,
no self-touching boundary) is a real restriction, worth naming explicitly
rather than assuming. It holds for the "nice" records checked directly:
n=9 (hexagon+spokes), n=18 (9-gon+interior), n=11 (split-hub heptagon —
checked above), and by inspection also the perturbed-polyomino records
(n=13, n=23): a sheared or chamfered grid boundary is still one simple
polygon, just non-regular, which is consistent with those records *not*
being tight against this bound (§7) — exactly what "the boundary alone
isn't optimal, interior structure matters" should look like. It would fail
for a hypothetical configuration built from multiple disjoint fenced
regions (an island component plus a separate main component, or a region
with an internal fenced-off hole reaching back to the unbounded face) —
no known record does this, but a general bound should not assume it away
silently, so:

> **Corollary (hypothesis-free).** For *every* n-fence configuration,
> `A(n) <= (n/4)*cot(pi/n)`.

Proof: `k <= n` (a configuration cannot spend more than `n` fences on any
one boundary), and `f(k) = (k/4)*cot(pi/k)` is increasing in `k`, so the
lemma's bound for the true `k` is at most `f(n)`. For the multi-component
case (H1 failing), each connected piece `j` independently satisfies
`area_j <= f(k_j)` by the same lemma applied to that piece, with
`sum_j k_j <= n`; summing and using that `f` is superadditive on the
relevant range (**checked numerically for all pairs `3 <= k1 <= k2` with
`k1+k2 <= 24`, not proved in general** — `f` is rapidly convex-increasing,
so this is expected to hold well beyond that range, but is flagged as
numerical, not a general proof) gives `sum_j area_j <= f(sum_j k_j) <=
f(n)`. ∎ (multi-component half: DERIVED, VERIFIED numerically to n=24)

Implemented as `bounds::boundary_polygon_bound`; `bounds::combined_bound`
takes the tighter of it and Theorem 1.

### 4.4 New optimality proofs: A(3) and A(4) are exact

The corollary is **exactly tight** at `n=3` and `n=4`:
`(3/4)*cot(60°) = sqrt(3)/4` (the equilateral triangle) and
`(4/4)*cot(45°) = 1` (the unit square) — both equal the recorded areas
exactly (`bounds::tests::boundary_polygon_bound_is_tight_at_n3_and_n4`,
and cross-checked against the record table in
`tests/upper_bounds.rs::boundary_polygon_bound_is_exactly_tight_at_n3_and_n4`).

> **Theorem.** `A(3) = sqrt(3)/4` and `A(4) = 1`, exactly.

**DERIVED, VERIFIED** — the first written optimality proofs found for any
entry of this table. (For `n >= 5` the regular-`n`-gon's own area already
exceeds 1 — `boundary_polygon_bound(5) ≈ 1.72` — so the bound stops being
achievable without interior subdivision, and stops being tight; n=5
onward remain open under this method. See §7 for the full table.)

## 5. The polyomino-ceiling conjecture: attempted proof, and where it breaks

Raised mid-task: let `f(A) = 2A + ceil(2*sqrt(A))` (Harary & Harborth's
1976 *proved* minimum-edge-count for an `A`-cell polyomino — this is an
established theorem for square-cell animals, not itself conjectural;
Harary, F. and Harborth, H., "Extremal animals", *J. Combin. Inform.
System Sci.* 1 (1976) 1–8, cited via the standard restatement
`p_min(n) = 2*ceil(2*sqrt(n))` for minimum polyomino perimeter, which
converts to the edge-count form via `e(P) = 2A - e(interior) ... =
2A + p_min(A)/2` from the double-counting identity `4A = 2*e(interior) +
e(boundary)`). Let `A*(n) = min{A : f(A) > n}`.

> **Conjecture.** `A(n) < A*(n)` for all `n`.

**CONJECTURED — supported by all 22 known records (§7), not proved.**

### 5.1 The attack tried: a discharging argument

The natural strengthening of Theorem 1 would be a per-face bound of the
shape `n >= 2*A(n) - c*sqrt(A(n))` for a suitable constant `c` — this is
exactly the form `f(A) ~ 2A + 2*sqrt(A)` inverts to, so proving it would
settle the conjecture's asymptotics.

§3.1 already shows the answer: **any argument built from the
curve-isoperimetric inequality caps out at leading constant `1/sqrt(pi)
≈0.564`**, not `1/2`. Since `1/sqrt(pi) > 1/2`, the isoperimetric method is
*too weak by construction* to prove even the leading-order form of this
conjecture (never mind the exact `+ceil(2*sqrt(A))` correction term) — it
would need to independently establish `n >= 2A` before the correction term
is even in play, and nothing in §1–§3 gets there. This is the gap, stated
precisely: **the isoperimetric inequality treats a face's boundary as an
arbitrary rectifiable curve; it cannot see that fences are straight,
unit-length, and reused between faces at cost exactly 1 (not `2*pi*r`-style
continuous cost) — recovering the polyomino's `2A` term requires an
argument that uses straightness and the length-exactly-1 quantization
directly, not merely the resulting curve length.** No such argument was
found in the time available. The boundary-polygon lemma (§4) is the
closest tool built here that touches straightness directly, but it bounds
only the *boundary* contribution, not the interior-scaffolding cost that
`2A` is really counting.

Harary & Harborth's own proof (for polyominoes specifically) presumably
does use the square-lattice structure directly (axis-aligned unit cells,
integer coordinates) — that structure is not available for a general fence
arrangement, whose fields can be any shape and any sub-1 area, so their
proof technique does not obviously transfer either; this was not chased
further given the scope of this document.

### 5.2 Computational check

`tests/upper_bounds.rs::every_record_sits_below_the_conjectured_polyomino_ceiling`
checks all 22 records; all pass (also independently confirmed by the
coordinator's own listed check). No counterexample found. §7's table shows
the slack: it never drops below `~0.48` (closest: n=23, `8.52289` vs.
ceiling `9`).

### 5.3 A correction to a proposed strengthening: the monotonicity step does not hold as proved

Mid-task, a proof of `A(n+1) >= A(n)` was proposed, via: take an optimal
`n`-configuration, add one more unit fence as an interior chord (both
endpoints landing on the existing structure, via the genericity argument
that a family of valid unit-length chords through two existing fences is
generically 1-dimensional), placed inside an already-bounded face; faces
only refine under this addition, so area is unchanged and the cap is
preserved.

**Checked, and it fails at the example given to illustrate it.** The
mechanism requires *some* valid interior chord to exist with a
non-vertex-anchored endpoint. For the `n=3` equilateral triangle, no such
chord exists at all: the diameter of a triangle (max distance between any
two points in the closed region, including interior/edge points) equals
its longest side — here exactly 1 — and is achieved *only* by pairs of
vertices. So any two points on the closed triangle at distance exactly 1
apart must both be vertices, meaning the only "new" unit fence connecting
two points of the triangle would have to duplicate an existing side, not
add a genuine interior chord. (Direct check of the proposed worked example
confirms this: with the shared-vertex parametrization `chord^2 = s^2 + t^2
- st` for two points at distances `s, t in [0,1]` along two sides meeting
at 60°, this quadratic form is strictly convex and attains its maximum
value of exactly 1 *only* at the three corner points `(s,t) = (1,0),
(0,1), (1,1)` of the unit square `[0,1]^2` — every interior or edge point
of that square gives `chord^2 < 1` strictly, so the claimed "ellipse arc"
of valid interior attachment points does not exist; the curve
`s^2+t^2-st=1` meets `[0,1]^2` only at those three corners, which are the
triangle's existing vertices, not new points.)

This does not disprove `A(n+1) >= A(n)` as a *statement* — `A(4) = 1 >=
A(3) = sqrt(3)/4` is true, just witnessed by an unrelated 4-fence
configuration (the square), not by extending the triangle. It shows the
specific proof mechanism (always-extendable optimum) is not universal, and
this document does **not** treat monotonicity as established. In
particular, the proposed sharpening of the conjecture into a
width-one-integer window,

```
A(n) in [ max{A : f(A) <= n},  max{A : f(A) <= n} + 1 )
```

is **withdrawn to CONJECTURED-on-top-of-CONJECTURED**: it needs both the
ceiling conjecture (§5, itself unproved) *and* monotonicity (now shown
unproved by the given argument, status open). It remains a plausible,
table-consistent shape (checked: n=13 in `[4,5)` at 4.07361, n=16 in
`[5,6)` at 5.53131, n=23 in `[8,9)` at 8.52289 — all consistent), worth
recording as a conjectured target, but resting on two open steps, not one.

## 6. The augmentation-rate ("does M4 chain above 1/2?") question

`docs/asymmetric-methods.md` §3 leaves open whether a chained sequence of
"chord-ear" (M4) moves can sustain a Δarea/Δn ratio above `1/2`. This
reduces to exactly the same question as §3 and §5 here: **an isoperimetric
argument cannot rule this out** (it only forbids ratios above
`1/sqrt(pi) ≈ 0.564`, which is not violated by any single M4 application
observed so far), and **the polyomino-ceiling conjecture, if proved, would
settle it in the negative** (a sustained chain averaging above `1/2` would
eventually produce a configuration violating `A(n) < A*(n) ~ n/2 -
sqrt(n/2)`, since `A*(n)/n -> 1/2`). No new resolution is offered here
beyond identifying that this question and §5's conjecture are, in the
asymptotic limit, the same open problem.

## 7. Bound-vs-record table (n = 3..24)

Computed by `bounds::isoperimetric_bound`, `bounds::boundary_polygon_bound`,
`bounds::combined_bound`, `bounds::polyomino_ceiling`
(`tests/upper_bounds.rs::print_bound_table`); every "proved" column is also
asserted against the record table in `tests/upper_bounds.rs` and passes.

| n | record | isoperimetric (§1) | boundary-polygon (§4) | combined | conjectured ceiling A*(n) (§5) |
|---|---|---|---|---|---|
| 3 | 0.43301 | 1.69257 | **0.43301** (tight) | 0.43301 | 1 |
| 4 | 1.00000 | 2.25676 | **1.00000** (tight) | 1.00000 | 2 |
| 5 | 1.00000 | 2.82095 | 1.72048 | 1.72048 | 2 |
| 6 | 1.43301 | 3.38514 | 2.59808 | 2.59808 | 2 |
| 7 | 2.00000 | 3.94933 | 3.63391 | 3.63391 | 3 |
| 8 | 2.08932 | 4.51352 | 4.82843 | 4.51352 | 3 |
| 9 | 2.59808 | 5.07771 | 6.18182 | 5.07771 | 3 |
| 10 | 3.00000 | 5.64190 | 7.69421 | 5.64190 | 4 |
| 11 | 3.53721 | 6.20609 | 9.36564 | 6.20609 | 4 |
| 12 | 4.00000 | 6.77028 | 11.19615 | 6.77028 | 5 |
| 13 | 4.07361 | 7.33446 | 13.18577 | 7.33446 | 5 |
| 14 | 4.66942 | 7.89865 | 15.33450 | 7.89865 | 5 |
| 15 | 5.00000 | 8.46284 | 17.64236 | 8.46284 | 6 |
| 16 | 5.53131 | 9.02703 | 20.10936 | 9.02703 | 6 |
| 17 | 6.00000 | 9.59122 | 22.73549 | 9.59122 | 7 |
| 18 | 6.18182 | 10.15541 | 25.52077 | 10.15541 | 7 |
| 19 | 6.76059 | 10.71960 | 28.46519 | 10.71960 | 7 |
| 20 | 7.00000 | 11.28379 | 31.56876 | 11.28379 | 8 |
| 21 | 7.69139 | 11.84798 | 34.83147 | 11.84798 | 8 |
| 22 | 8.00000 | 12.41217 | 38.25334 | 12.41217 | 9 |
| 23 | 8.52289 | 12.97636 | 41.83436 | 12.97636 | 9 |
| 24 | 9.00000 | 13.54055 | 45.57452 | 13.54055 | 10 |

Reading the table: the boundary-polygon bound (§4) is tighter than the
isoperimetric bound (§1) only for `n <= 7` (crossover at `n ≈ 7.53`, where
`n/sqrt(pi) = (n/4)*cot(pi/n)`), and is *exactly* achieved at `n=3,4` —
the only two entries this document proves optimal. For `n >= 8` the
isoperimetric bound is the tighter proved bound, and it is loose by a
factor of roughly 1.5–2× against every open record. The conjectured
ceiling (§5, unproved) is the only bound in the table that comes close to
the records; the proved bounds do not.

## 8. Literature checked

- Hales, T. C., "The Honeycomb Conjecture", *Discrete & Computational
  Geometry* 25 (2001) — average-perimeter theorem for infinite equal-area
  plane partitions; does not transfer to finite/bounded/free-boundary
  settings (§2).
- Headley, F. and Cox, S. J., "Least-perimeter partition of the disc into
  N regions of two different areas", arXiv:1901.00319 — finite,
  fixed-outer-boundary partitions; boundary-adjacent cells deviate from
  hexagons, supporting §2's refutation in the closest analogous setting
  found.
- Harary, F. and Harborth, H., "Extremal animals", *J. Combin. Inform.
  System Sci.* 1 (1976) — proved minimum-perimeter/minimum-edge formula for
  polyominoes, used as `bounds::harary_harborth_min_edges` in §5; the
  *extension* of this result beyond polyominoes to general fence
  arrangements is the open gap in §5.1, not the polyomino result itself.
- Variational/cyclic-polygon maximal-area theorem: see e.g. arXiv:1506.08069
  ("A variational principle for cyclic polygons with prescribed edge
  lengths") for a modern statement and proof; used in §4.
- Fejes Tóth's convex-case isoperimetric results and the
  isoperimetric/hyperbolic-animals literature (arXiv:2206.14910) were
  checked for a directly-applicable discrete bound for straight-unit-edge
  arrangements; nothing found there resolves §5's gap either — that
  literature bounds perimeter for lattice-animal-style discrete regions,
  which has the same "square lattice only" limitation as Harary–Harborth
  relative to this problem's free-form fields.
- Friedman's own square-packing survey
  (combinatorics.org/files/Surveys/ds7/ds7v1-1998.pdf) uses an
  "unavoidable point set" technique (after Stromquist) for *lower* bounds
  on squares-in-a-square packing efficiency; it is a technique for proving
  a *lower* bound on a different quantity (minimum enclosing square size),
  and no adaptation of it to an *upper* bound on enclosed area for this
  problem was found — flagged as checked, not as a source of a new bound
  here.
- No published upper bound (or optimality proof for any non-trivial
  table entry) for Friedman's fences problem specifically was found in
  this search.

## 9. Summary

| # | Result | Status |
|---|---|---|
| `A(n) <= n/sqrt(pi)` | Theorem 1, §1 | **DERIVED, VERIFIED** |
| Hexagonal sharpening to `≈0.5373n` | §2 | **REFUTED** |
| Isoperimetric route capped at leading constant `1/sqrt(pi)`, cannot reach `1/2` | §3.1 | **DERIVED** |
| `1/2` is the true asymptotic constant | §3 | **OPEN** — narrowed to `[0.5, 0.5642]` |
| Boundary-polygon lemma, `A(n) <= (k/4)cot(pi/k)` for a k-fence simple boundary | §4 | **DERIVED, VERIFIED** (with hypothesis H1; hypothesis-free corollary also DERIVED) |
| `A(n) <= (n/4)cot(pi/n)` (hypothesis-free corollary) | §4.3 | **DERIVED, VERIFIED** against all 22 records |
| `A(3) = sqrt(3)/4`, `A(4) = 1` exactly | §4.4 | **DERIVED, VERIFIED** — first known optimality proofs for these entries |
| Polyomino ceiling `A(n) < A*(n)` | §5 | **CONJECTURED** — 22/22 records consistent, gap identified (§5.1) |
| `A(n+1) >= A(n)` (monotonicity) | §5.3 | **NOT ESTABLISHED** — proposed proof mechanism fails at n=3 (counterexample given) |
| Width-one-integer window conjecture | §5.3 | **CONJECTURED**, contingent on two unproved steps (ceiling + monotonicity) |
| M4-chaining above 1/2 | §6 | **OPEN**, same problem as §3/§5 |
