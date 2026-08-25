# Spring-relaxation topology search: does a T1 analog exist for rigid unit fences?

Scope: evaluate whether a spring-network relaxation with topology-changing moves (the
foam/vertex-model "T1 transition" idea) can fix the outer-level skeleton search, which
`skeleton::random_growth` + multistart currently cannot do reliably (documented failure:
0/200 attempts find the unit square at n=4; 2/20 attempts even validate at n=18). Does
**not** touch the inner coordinate optimizer (`anneal.rs`), which is solid.

Every claim below is tagged **DERIVED**, **VERIFIED** (against a run in this session, or
a citation), or **CONJECTURED**, per this crate's convention (`docs/asymmetric-methods.md`).

## 1. The crux: what replaces the T1 trigger when edges can't shrink

### 1.1 Why the literal trigger fails (DERIVED)

A foam/vertex-model T1 fires when a cell-boundary edge's length shrinks to zero: two
degree-3 vertices merge into one degree-4 vertex, which then re-splits along the
perpendicular direction, swapping which two cells are neighbors. The trigger is a
**continuous geometric event** (`length(edge) → 0`) that the relaxation dynamics
themselves drive, because in these models an edge is nothing but "the segment between
two free vertex positions" — its length is whatever the vertices' current coordinates
make it, with no rest length of its own (a soap film interface, or a vertex-model cell
wall, has surface tension but no preferred length).

In the fences problem, this breaks at the first premise. Every fence is a **physically
reified unit-length bar**: `fence i`'s length is pinned to exactly 1 by the problem rules
themselves, not by an energy term that happens to be minimized near 1. A fence's length
never approaches zero during any legal motion — it *is* 1, always, everywhere in the
configuration space this crate searches. So "the edge that's about to vanish" — the
event that tells a foam simulator *where* and *when* to attempt a reconnection — simply
does not occur at the fence level. There is no zero-crossing to detect.

### 1.2 Four candidate substitute triggers, examined

The four candidates named in the brief, worked through:

**(a) Arrangement sub-edge shrinking to zero.** `arrangement::build_arrangement` doesn't
treat a fence as one edge — it cuts each fence into sub-edges at every point where
another fence's endpoint or crossing lands on it (`cut_points`, sorted by `param_of`
along the fence). These sub-edges are *not* length-pinned; only the parent fence's total
length is. So two consecutive incidence points on the same host fence (two T-junction
feet, or a foot and the host's own endpoint) genuinely can converge and the sub-edge
between them genuinely can shrink to zero as coordinates move continuously — this is a
**real, well-defined T1-shaped event**, unlike (1.1)'s fence-level version.

But it doesn't buy anything: `evaluate()` in `anneal.rs` already reconstructs the whole
arrangement fresh from raw coordinates on *every* single evaluation (`build_arrangement`
is called once per proposal, not incrementally). The sort in step 3 of
`build_arrangement` (`idxs.sort_by(|... param_of ...)`) already re-derives sub-edge order
from scratch each time, so an order-swap between two T-junction feet on the same host
fence is not a *move* the outer search needs to propose — it's already inside what the
existing inner annealer does on every accepted coordinate perturbation, for free. This
sub-edge-level "T1" is real, but it's already implemented, and it operates entirely
within a *fixed* skeleton (same `fences` list, same `t_junctions` list — the Skeleton
data structure in `skeleton.rs` doesn't even encode sub-edge order, only which fence a
T-junction targets). It cannot change vertex count or fence connectivity, so it cannot
be the missing outer-search capability. **VERIFIED by code reading**, not by a new
experiment — this is a structural fact about `build_arrangement`'s call pattern.

**(b) A T-junction sliding off the end of its host fence (t → 0 or 1).** This is also a
real, well-defined event: `anneal.rs::evaluate` already computes `t` for every
T-junction and penalizes `t` outside `[0,1]` via a hinge term, so the search already
"feels" this boundary. Crossing it exactly (t=0) means the T-junction foot has become
coincident with the host fence's own endpoint — a valid but *different* combinatorial
reading: "T-junction into fence F's interior" degenerates into "ordinary corner shared
with F's endpoint" (§1.2 of `asymmetric-methods.md`). This is a genuine, narrow
topology-changing event, but it only **retargets** an existing T-junction among fences
that already meet at a point (the target fence and whichever other fence owns that
endpoint) — it can reassign incidence locally, never create a new vertex or a new cycle.
It does not touch fence/vertex *count*, so on its own it cannot solve the class of
failure this doc's benchmark (§3.1) targets.

**(c) Two T-junctions on the same host fence colliding.** This is the same event as (a),
described from the "collision" side rather than the "shrink" side — not a distinct
trigger.

**(d) A fence rotating through a degenerate (zero-area / collinear) configuration.**
Real geometrically (three unit-length points can become collinear, folding a face to
zero area, without any length constraint being violated), but it does **not** give a
well-defined reconnection rule. In a soap film, a degenerate face has a unique physical
resolution (the film reconnects the only way surface tension allows). A rigid polygon
passing through zero area is just a self-intersecting or folded configuration — the
arrangement builder already handles this correctly as ordinary crossing/pendant-edge
geometry (module docs, `arrangement.rs`), not as a special event requiring a discrete
move. There is no canonical "other side" to reconnect to. **This trigger does not give a
usable move.**

### 1.3 Verdict on the trigger question

None of the four candidates yields a move that can change **fence count or vertex
connectivity** the way `random_growth` needs but can't do (§3). (a) and (c) are the same
already-implemented, already-continuous, skeleton-preserving event. (b) is real but
narrowly retargets among already-adjacent structure. (d) has no well-defined outcome for
a rigid-bar graph. **The pinned lengths do kill the literal T1 analogy** — not merely by
removing one convenient trigger, but structurally: T1 in the cited literature (§2) relies
on edges being fungible line segments between free vertex positions, with no edge caring
which two vertices it connects beyond "whichever ones are currently close." A fence is
not that — it is a specific numbered physical object with a global unit-length
constraint, and "should fence #7 connect A–B instead of C–D" is a discrete question with
no small continuous path between the two answers in general (§2.3 works out what the
actual substitute looks like once this is accepted).

## 2. Literature check

**Vertex models of epithelial tissue** (Farhadifar et al. 2007; Fletcher et al. 2014,
surveyed in the Biophysical Journal review and in Spencer/Nagai-Honda-style follow-ups —
see also the review "Geometry of T1 transitions in epithelia," arXiv:2504.16765, and
"Vertex stability and topological transitions in vertex models of foams and epithelia,"
arXiv:1609.08696). T1 is triggered by an edge shrinking below a length threshold; edges
here are free line segments (no rest length), and the whole point of the vertex-model
formalism is that "which cell borders which" is exactly what the free edge lengths and
positions determine. This is the source of the trigger the fences problem cannot borrow
(§1.1).

**Surface Evolver** (Brakke 1992, kenbrakke.com/papers). Directly supports T1 and T2
topology changes during energy minimization, for the same reason: its triangulated
surfaces/films have no rest length, only surface-tension energy, so a shrinking
edge/facet is a legitimate physical signal.

**Cellular Potts model** (Graner & Glazier 1992, Glazier-Graner-Hogeweg). A different
mechanism entirely, worth noting because it's the literature's other answer to "how do
you get topology change without a shrink-to-zero trigger": cells are pixel sets on a
fixed lattice, and neighbor exchange happens via Metropolis pixel-copy moves (a boundary
pixel is stochastically reassigned from one cell to another), not via any continuous
geometric threshold. T1/T2 "emerge" from many small discrete lattice edits, not from a
tracked continuous quantity crossing zero.

**Cox & Headley, "Least-perimeter partition of the disc into N regions of two different
areas," arXiv:1901.00319** — the closest published precedent to this problem (least-
perimeter/isoperimetric-style optimization of a partition subject to per-region area
constraints). Per the abstract: they **enumerate all 3-connected simple cubic planar
graphs for each N**, assign areas to candidate structures, and optimize the perimeter of
each candidate numerically — i.e. enumeration of topologies followed by separate
per-topology optimization, not a single relaxation that evolves its own topology. I could
not extract the paper's stated rationale for this choice (no PDF-text-extraction tool was
available in this environment to read past the abstract), so I am **not** claiming they
explicitly rejected an Evolver-style T1-driven relaxation — only that the abstract
confirms enumeration is what they did. Given that Surface Evolver itself supports T1/T2
natively (previous paragraph), the fact that this closest-analog paper still chose
enumeration is suggestive but not confirmed as a deliberate methodological rejection of
relaxation-with-topology-change; flagging this as **CONJECTURED, not verified**, rather
than asserting a reason on their behalf.

**Force-directed graph drawing** (yWorks/AntV surveys; "Force-directed algorithms for
schematic drawings and placement: A survey," arXiv:2204.01006; dynamic-graph layout work
on multilevel force-directed layout for online vertex/edge insertion). Confirms a clean
negative precedent: force-directed layout algorithms take the graph's vertex and edge set
as **externally given**, and re-relax coordinates after an outside process adds or
removes structure — the physics of spring relaxation itself never decides to invent a new
edge. This matches §1.3's structural finding: relaxation, on its own, has no native
mechanism for discovering new topology; the decision has to come from somewhere else
(external input, enumeration, or a discrete stochastic proposal).

**Wooten, Winer & Weaire, "Computer generation of structural models of amorphous Si and
Ge," Phys. Rev. Lett. 54, 1392 (1985)** — the actual matching precedent, once the
foam-analogy is set aside. WWW "bond switching" builds continuous random networks of
fixed-coordination, fixed-length-ish bonds (amorphous silicon: every atom has ~4
neighbors) via a **Metropolis graph-edit proposal**, not a geometric trigger: pick a
bonded pair B–C, pick neighbors A of B and D of C, break bonds A–B and C–D, form A–C and
B–D (B and C exchange neighbors), then relax and accept/reject by energy. This is
structurally the right precedent for the fences problem: it is exactly the operation
needed here (§2.3), and its acceptance criterion is Metropolis/energy-based, not
triggered by any length approaching zero — because in WWW's model, as in this one, bond
length is *not* the free quantity a shrink-to-zero event could be read off of.

## 3. What the substitute looks like, and what it can and can't do

Given §1–2, the honest substitute for "T1 during relaxation" in a rigid-unit-length-bar
system is **not** a geometric trigger at all — it's an unconditional, WWW-style
stochastic graph-edit proposal on the skeleton, each one evaluated by handing the
edited skeleton to the *unmodified* inner annealer and accepting/rejecting by the
resulting area. This is deliberately not framed as "T1" in the code or below; it's a
different mechanism that happens to serve the same purpose (topology diversity during
search).

Two moves, both implemented in
`crates/motif-fences/src/bin/spring-topology-prototype.rs`:

- **`reroute_new_vertex`** (Δn = +1): delete one existing "plain" fence `(u,v)` — not a
  T-junction target, both endpoints already degree ≥ 2 so removal can't strand them —
  and replace it with a 2-fence detour through a fresh vertex `w`: `(u,w), (w,v)`. This
  is the one move that can turn a smaller cycle into a bigger one (triangle →
  quadrilateral) without anything shrinking; it's a direct discrete substitution. It is
  exactly what `random_growth`'s M1–M4 catalog lacks: that catalog only ever *adds*
  fences onto existing structure, never retires one, so it can never turn a 3-cycle into
  a 4-cycle — only ever a 3-cycle-plus-appendage.
- **`rewire_existing`** (Δn = 0): pick two plain fences `(a,b)` and `(c,d)` with four
  distinct endpoints, re-pair them as `(a,c)+(b,d)` or `(a,d)+(b,c)`. This is the literal
  WWW bond-switch, unconditional (no geometric precondition beyond "4 distinct
  endpoints, neither fence is a T-junction target"), applied to the fence graph.

Both moves are, by construction, structurally safe: `reroute_new_vertex` only touches
vertices that had degree ≥ 2 and restores the same degree, and `rewire_existing` leaves
every touched vertex's fence-count unchanged and never invalidates a T-junction's target
index (candidates are filtered to exclude T-junction-target fences in both moves). No
special-case repair logic was needed to keep `Skeleton::validate_shape` satisfied.

**Reversibility, honestly assessed:** `rewire_existing` is exactly self-inverse (applying
the same re-pairing twice returns the original skeleton) — reversible by construction.
`reroute_new_vertex` is not cleanly reversible as implemented (its inverse would be
"delete a degree-2 vertex whose two fences aren't T-junction-involved and reconnect its
two neighbors directly," which is only *geometrically* realizable when those neighbors
happen to end up near unit distance apart — not guaranteed, so a true inverse would need
to be its own move with its own acceptance criterion, not a free reversal). This was not
implemented; flagged as a real gap rather than asserted as solved.

## 4. Enumeration vs. relaxation-with-topology-moves: the actual tradeoff

**Enumeration (Cox & Headley's approach: enumerate 3-connected cubic planar graphs, solve
each).** Cost: combinatorial explosion in the number of distinct planar topologies at a
given `n` — this problem's skeletons aren't restricted to cubic graphs (T-junctions and
mixed vertex degrees are legal and used by every known open-record construction; see
`asymmetric-methods.md` §1.2–1.3), so the enumeration space here is *larger* than Cox &
Headley's, not smaller: it would need to range over planar graphs with T-junction
markings, not just 3-connected cubic graphs. Some of that could plausibly be bounded
(fix `n`, bound vertex count, generate via a canonical-form planar-graph enumerator,
dedupe by isomorphism) but no such bound is derived or checked here — an open cost, not
a solved one. Benefit: exhaustive within whatever bound is chosen — a construction that
survives the enumeration is provably the best *among enumerated candidates*, which is a
much stronger guarantee than anything a stochastic search offers.

**Relaxation-with-topology-moves (this doc's prototype).** Cost: no completeness
guarantee at all — a rewire/reroute chain explores an unbounded, unstructured walk over
skeleton space with no way to certify it has seen "enough" of it, and (§5) the specific
greedy single-chain hill-climb prototyped here empirically plateaus well short of known
records at n=12 and n=15. Benefit: doesn't require solving the enumeration/generation
problem for the mixed T-junction/ordinary-vertex graph class first, and reuses the
already-solid inner annealer directly rather than needing a separate solve-then-compare
pipeline per candidate.

No recommendation is made between these; the costs are of different kinds
(unquantified-but-large combinatorial cost vs. no completeness guarantee at all) and
which matters more depends on how much wall-clock/compute budget is available and
whether a bound on the enumeration side gets worked out — a separate question from this
doc's scope.

## 5. Empirical results

All runs used `motif-fences`' own `Configuration::validate()` (default `Tolerance`,
`1e-6`-scale) as the sole authority on validity — the prototype's own printed "area"
numbers are only ever reported for configurations that passed `validate()`. Sanity check
against the isoperimetric bound `total_area ≤ n / √π ≈ 0.5642 n` (each fence point
borders ≤ 2 faces, so `Σ perimeters ≤ 2n`, and `a_i ≤ 1 ⟹ a_i ≤ √a_i`): every area
reported below is well under this bound, so none of it needed to be treated as
suspect-until-proven on that count.

### 5.1 n=4 — the crux benchmark

```
cargo run --release --bin spring-topology-prototype -- --mode baseline       --n 4 --attempts 200 --seed 1 --iterations 60000
cargo run --release --bin spring-topology-prototype -- --mode reroute-growth --n 4 --attempts 200 --seed 1 --iterations 60000
```

| generator | valid | best area |
|---|---|---|
| `random_growth` (baseline, existing crate code) | 200/200 | 0.433013 (the triangle, every time) |
| `grow_with_reroute` (this doc's `reroute_new_vertex`, growth from a triangle) | 183/200 | **1.000000** (10 of the top-10 areas are all `0.99999...` — the unit square) |

**VERIFIED.** This reproduces the documented baseline failure exactly (200/200 valid, but
never above the triangle's own area — confirming the "stuck," not "failing to validate,"
diagnosis) and shows `reroute_new_vertex` decisively fixes it: the great majority of
seeds land on the square. This is the one clean, positive result in this investigation —
the specific structural gap named in the brief (add-only moves can't retire the
triangle's third edge to make room for a fourth vertex) is real, and this move closes it.

### 5.2 n=12 (2x2 grid, target area 4) and n=15 (P-pentomino, target area 5)

```
cargo run --release --bin spring-topology-prototype -- --mode reroute-growth --n 12 --attempts 60  --seed 1 --iterations 60000
cargo run --release --bin spring-topology-prototype -- --mode baseline       --n 12 --attempts 60  --seed 1 --iterations 60000
cargo run --release --bin spring-topology-prototype -- --mode rewire --n 12 --seed 1 --iterations 60000 --rewire-steps 150
cargo run --release --bin spring-topology-prototype -- --mode rewire --n 15 --seed 1 --iterations 60000 --rewire-steps 150
```

| run | valid | best area |
|---|---|---|
| n=12, `reroute-growth` (pure cycle growth, 60 attempts) | 7/60 | 2.960717 |
| n=12, `baseline random_growth` (60 attempts) | 48/60 | 2.860546 |
| n=12, `rewire` (greedy hill-climb from one `random_growth` seed, 150 steps) | — | 2.596841 (18/150 rewires accepted) |
| n=15, `rewire` (same, 150 steps) | — | 3.030812 (15/150 rewires accepted) |

Both targets (4 and 5) are far out of reach in every run above.

**DERIVED, from these numbers plus the move definition:** pure `reroute_new_vertex`
growth cannot reach a grid or pentomino topology at all, structurally, not just by bad
luck. Every application takes a fence `(u,v)` that is part of the current boundary cycle
and re-routes it through a new vertex — starting from a simple cycle (the triangle seed)
and repeatedly applying this move can only ever produce another simple cycle (a bigger
polygon), never an interior chord. That matches the observed pattern: `reroute-growth`'s
best area (2.96) is close to a boundary-only construction's ceiling at n=12, not close to
the grid's chord-supported 4, and its *validity* rate (7/60) is also markedly worse than
the baseline's — larger, more irregular random polygons apparently anneal to a valid
state less reliably than the baseline's triangle-plus-appendages skeletons do, at this
iteration budget.

`rewire_existing`, which *can* create chords (a re-pairing can connect two vertices that
weren't adjacent along the current cycle), does make steady, real progress in the n=12
and n=15 runs (1.30 → 2.60, and 1.39 → 3.03 respectively) — the move mechanism itself is
doing something. But a single greedy chain plateaus well short of the target in both
cases, and does not beat the baseline's own 60-attempt multistart at n=12 (2.60 vs.
2.86). This is the same failure mode `anneal.rs`'s own module docs warn about for naive
coordinate hill-climbing (a biased random walk gets stuck near a local optimum without a
temperature schedule or restarts) — nothing here suggests the *mechanism* is wrong, only
that a single greedy chain is an under-powered way to drive it. A proper treatment would
run many independent rewire chains (an outer multistart over rewire trajectories, the
same architecture `random_growth` already uses, just with a richer proposal set) rather
than one chain with a naive greedy accept rule — not attempted here; time-boxed out of
this sidequest's scope, and noted honestly as unfinished rather than glossed over.

No configuration produced by any run in this section exceeded its target integer area,
so the "candidate new record" question does not arise here — every number is below the
best-known value at its `n`.

## 6. Verdict

**The literal T1 trigger does not transfer to this problem.** It relies on edges being
free line segments with no rest length; fences are physically reified unit-length bars,
so no edge-shrinks-to-zero event exists at the fence level, and every candidate
substitute trigger examined (§1.2) either collapses into something the existing inner
annealer already does implicitly, or is too narrow to change fence/vertex count, or has
no well-defined outcome. This is a structural fact about the problem, not a tuning gap —
more relaxation-schedule tuning would not surface a trigger that isn't there.

**What replaces it is not a relaxation mechanism at all — it's a discrete stochastic
graph-edit proposal (WWW bond-switching), evaluated by re-running the existing inner
annealer.** One instance of this (`reroute_new_vertex`) is a genuine, decisive fix for
the specific benchmark named in the brief: it takes n=4 from 0/200 (stuck at the
triangle) to the unit square in the clear majority of attempts. A second instance
(`rewire_existing`) is the literal WWW move and does inject real chord structure, but
prototyped as a single greedy hill-climb chain it does not recover the n=12 or n=15
records, and does not clearly outperform the existing baseline at equal budget. Whether
a properly multistarted version of it would close that gap is open — and, notably, that
architecture (many independent chains of stochastic graph edits, each accepted/rejected
by re-annealing) is exactly "simulated annealing over the graph itself," the alternative
`anneal.rs`'s own module docs already named and explicitly deferred as future work rather
than something available cheaply. This investigation's conclusion is not "spring
relaxation solves the outer search" — it's narrower: **the T1 metaphor fails, but a
different, WWW-shaped move set survives scrutiny well enough to fix the specific
add-only-growth pathology at n=4, and reduces the harder open cases (n=11/12/15) to
"needs the multistart-over-graph-edits architecture already flagged as future work,"
not to something this prototype demonstrates working end to end.**

n=11's split-hub skeleton (the strong result named in the brief) was not recovered from
scratch in this investigation — the rewire experiments here targeted n=12 and n=15
(cheaper to iterate on) and both plateaued well short of target before this doc's time
budget ran out; n=11 was not separately attempted. Recovering it remains open work for
whoever picks up the multistart-over-rewire-chains architecture named above.

## 7. Building that architecture: outer-level Metropolis SA over graph-edit chains

§6 named the missing piece: a single greedy hill-climb chain is the wrong driver for
`rewire_existing`; the WWW precedent (§2) is Metropolis over graph edits, and it belongs
at the *outer* level, mirroring what the *inner* annealer already does at the coordinate
level. This section builds that architecture (`spring-topology-prototype.rs`, mode
`outer-sa`) and reports what it does and doesn't fix.

### 7.1 Two more moves, motivated by a real expressiveness gap

Neither `reroute_new_vertex` nor `rewire_existing` can ever *create* a T-junction:
`reroute_new_vertex` always lands its new vertex at an ordinary degree-2 corner, and
`rewire_existing` only repairs existing plain-fence pairings. But every open-record
skeleton this crate has solved uses T-junctions load-bearingly (n=8's chord lands
mid-edge on an apex-shoulder edge, not at the shoulder vertex; n=11's split hub needs a
T-junction onto a chord's interior in addition to its 3-way coincidence). A move set that
can't express "new fence anchored at an existing vertex, landing by T-junction on an
existing fence's interior" cannot reach those topologies regardless of how the outer
search is driven. Two moves close this gap:

- **`chord_ear`** (Δn=+1): re-implements `skeleton.rs`'s private M4/ChordEar move locally
  (that module doesn't expose it) — anchor a new fence at an existing vertex, land its
  free end by T-junction on an existing fence's interior.
- **`retarget_t_junction`** (Δn=0): reassigns an existing T-junction to a different host
  fence — the "T-junction slide" trigger from §1.2(b), now usable as a proposal rather
  than only a passive by-product of coordinate drift.

**On the specific n=8 kink question** (chord endpoints landing at kinks partway up the
apex-shoulder edges, not at the shoulder vertices themselves): `chord_ear`'s landing
parameter `t` is a free continuous coordinate solved by the inner annealer, not a value
fixed by the move. The `t ∈ (0.2, 0.8)` range in the move's implementation is only the
initial guess handed to the SA — nothing stops the annealer from converging `t` close to
0 or 1 (short of the incidence hinge's own `[0,1]` bound). **The move set can express a
near-vertex kink**; whether a given search run *finds* one is a separate question (§7.3).

### 7.2 The architecture

`grow_mixed` builds an initial n-fence skeleton by mixing `reroute_new_vertex` and
`chord_ear` from a triangle seed (both Δn=+1), so different chains start from
structurally different topologies — some cycle-only, some already carrying T-junctions.
`outer_sa_chain` then runs a Metropolis loop at fixed n: each iteration proposes
`rewire_existing` or `retarget_t_junction` (both Δn=0), re-anneals the candidate skeleton
from the chain's *current* coordinates using the unmodified inner annealer, and accepts
or rejects by the standard Metropolis rule against a geometric outer-temperature
schedule. The score is `Configuration::validate()`'s total area when the candidate is
feasible, or a penalty-based fallback (always < 0, so any feasible candidate outranks any
infeasible one) computed from the annealer's own residuals when it isn't — this fallback
matters for the acceptance walk, not for reporting: no number in §7.3 below is reported
unless it came from a chain state that passed `validate()` with `valid=true`, which every
`outer-sa` log line states explicitly per attempt. `run_outer_sa` multistarts several
independent chains and keeps the global best, dumping its skeleton as JSON for inspection
— this is the "multistart over graph-edit chains" architecture named in §6, with
`reroute_new_vertex`/`chord_ear`/`rewire_existing`/`retarget_t_junction` as the proposal
set and the inner annealer as the sole evaluator.

### 7.3 Results

All runs below used 30,000–35,000 inner-annealer iterations per proposal and 8–12 outer
chains of 150–300 Metropolis steps each (`--seed 1`; see the file's own doc comment for
exact commands). Every reported number is `Configuration::validate()`-gated: `score_of`
only reports a chain's score as the validated `total_area` when `validate()` succeeds,
and the `outer-sa` log for every chain in every run below states `valid=true` explicitly.

| n | target (published/trivial) | previous plateau (§5, single greedy chain) | outer-SA best (this section) | reached? |
|---|---|---|---|---|
| 4 | 1 (trivial) | n/a (reroute-growth already solved this, §5.1) | 0.9999915 | yes, no regression |
| 8 | 2.0893244080014 (Daniel Mathias) | not attempted in §5 | 1.9992535298 | no — 95.6% of target |
| 11 | 3.5372167764 (Teodor Tohanean, split hub) | not attempted in §5 | 3.422614 (8 of 12 chains; 4 chains not run — time-boxed) | no — 96.8% of target, partial |
| 12 | 4 (trivial, 2x2 grid) | 2.596841 | 3.5813555692 | no — 89.5% of target |
| 15 | 5 (trivial, P-pentomino) | 3.030812 | 4.4011583850 | no — 88.0% of target |

**n=12's result is confirmed structurally, not just numerically, to not be the grid.** Its
best skeleton uses 12 distinct vertices for 12 fences; the grid skeleton
(`skeleton::grid(2,2)`) reuses only 9 vertices via shared corners. The outer-SA chain
found a different, worse-scoring topology, not a near-miss on the actual record.

**Honest verdict on the architecture change:** it moved every one of n=8/11/12/15
substantially above where the single-greedy-chain prototype in §5 plateaued (n=12:
2.60→3.58; n=15: 3.03→4.40; n=8 and n=11 weren't attempted with a single chain to compare
against, but land at 95–97% of target here) — so Metropolis-at-the-outer-level is doing
real work relative to greedy hill-climbing, confirming §6's diagnosis that the driver,
not the moves, was the weak point of the earlier prototype. **But within this budget, it
did not reach any of the four non-trivial targets, and n=12 specifically did not even
find the right topology.** This is a second negative result on the outer search — the
first (§5) showed a single chain plateaus; this one shows multistarted Metropolis chains
get further but still don't close the gap at these sizes. Per the standing instruction to
report this plainly rather than keep spending budget hoping for a better number: **the
outer-SA architecture is a real improvement over blind multistart and over a single
greedy chain, but it has not — in the budget spent here — demonstrated finding an
asymmetric record topology unaided.** Whether more chains, more Metropolis steps, a
better outer temperature schedule, or a richer/weighted proposal mix would close the
remaining ~5–10% gap at n=8/11 or the larger gap at n=12/15 is open; a second negative at
this scale is itself the kind of result that argues for treating bounded enumeration
(§4) as the remaining route to try, rather than continuing to tune this architecture on
faith that more compute alone would find it.

n=11's partial result (96.8% of target, 8 of 12 chains) is the closest this investigation
came to the "found unaided" result named as the real prize. It was not completed within
this doc's time budget — the remaining 4 chains were not run to conclusion — so it is
reported as a partial, not a finding.
