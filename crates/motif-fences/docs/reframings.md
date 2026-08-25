# Reframing the fences problem into other mathematical settings

Scope: the work so far (`docs/asymmetric-methods.md`, `src/skeleton.rs`, `src/anneal.rs`,
`src/search.rs`) attacks the fences problem as plane geometry — combinatorial skeletons
plus continuous coordinate optimization. This document evaluates deliberately reframing
it into other mathematical settings, on the theory that a different mental model exposes
a different attack surface, and grades each reframing against the four concretely open
questions:

- **(A)** global optimality of the n=11 split-hub KKT point (3.5372167764) for its own
  skeleton — unknown, no multi-start was run.
- **(B)** the skeleton search / discrete layer — `skeleton::random_growth` fails
  structurally (misses the n=4 unit square in 200 attempts; 4.594 vs 6.18182 target at
  n=18). This is the actual blocker; the inner coordinate optimizer is fine.
- **(C)** whether any infinite family beats the 1/2-area-per-fence asymptotic ceiling.
- **(D)** proving optimality (not just producing a good construction) — nobody has done
  this for **any** entry in the table, "trivial" ones included. Harary-Harborth's
  `f(A) = 2A + ceil(2*sqrt(A))` is proven as the minimum *edge count among polyominoes*
  of A unit cells — that's a lower bound on edges needed by a polyomino, equivalently a
  construction giving area A at n = f(A) fences, not a proof that no non-polyomino beats
  area A at that same n. "Trivial" on Friedman's page means trivial *to find*, not
  trivial to prove optimal, and the page itself claims no optimality proof for any entry.
  The concern is not hypothetical: at n=13 the best polyomino gives area 4 but the record
  is 4.0736 (a sheared grid pulled toward a point beats the square grid); at n=16 the best
  polyomino gives 5 but the record is 5.531. Non-square fields under the area-≤1 cap
  genuinely beat squares at some n, which is exactly why a polyomino-based lower bound
  can't be mistaken for an optimality proof anywhere in the table.

Every claim below is tagged **DERIVED**, **VERIFIED**, or **CONJECTURED** per repo
convention. Coordination note: I checked for a landed force-network / pressure-dual
write-up from the parallel KKT/force-network agent before writing item 4 below and found
none in the tree as of this writing (`grep` for "force network", "pressure", "dual
formulation", "polyhedral lift" across `crates/motif-fences` turned up nothing besides
this document and the skeleton/test files already in the repo) — item 4's analysis below
is independent, not a duplicate.

**Toolchain check (VERIFIED, load-bearing for the feasibility calls below).** `nix
develop`'s shell provides only `rustc`, `cargo`, `clippy`, `rustfmt`, `mold`, `clang`, and
`bun` (`flake.nix`). There is no `python3`, `julia`, `z3`, or `dReal` in that shell (checked
directly: `which python3 julia z3 dReal` all fail inside `nix develop`). Network access to
`cache.nixos.org` does work, so these *could* be added to `flake.nix`, but that's a shared
file every parallel agent's shell depends on, plus a from-scratch Julia+HomotopyContinuation.jl
or Python+SciPy toolchain would be a multi-hundred-MB, several-minute-plus install with no
guarantee of finishing in this session's budget. This crate's own toolchain is pure Rust.
That fact by itself kills or downgrades several of the reframings below — noted per item.

## 1. Polynomial system / numerical algebraic geometry

**Maps onto:** exactly what §1.1 of `asymmetric-methods.md` already derived. Fix a
skeleton. Coordinates are `2 * vertex_count` reals. Constraints (length = 1 per fence,
collinearity per T-junction) are polynomial (degree 2 for length, degree 2 for the
collinearity determinant) in those reals. The objective (sum of bounded-face shoelace
areas) is polynomial too. So "is the KKT point the global max for this skeleton" is
literally "find all real roots of the polynomial system obtained by setting the
Lagrangian's gradient to zero, and compare objective values" — a homotopy-continuation
problem, which (unlike general algebraic geometry) *does* solve for every isolated
complex root, not just find one.

**Attacks:** (A) directly, head-on. Not (B), (C), or (D) — it only says something about a
skeleton already chosen.

**Size at n=11 (split-hub skeleton, `tests/records.rs::split_hub_pinwheel_n11`):** 13
vertices, 26 raw coordinates, minus 3 for the rigid-motion quotient (fix one vertex,
fix one angle) = 23 free reals after gauge-fixing, or work in the full 26 and add 3 gauge
equations. 11 length equations, 5 incidence equations (from `t_junctions`), plus however
many area-cap constraints are active at the optimum (§1.3/§1.4 observed 3 of 4 bounded
faces at the cap) — each a degree-2 polynomial equality once "active" is assumed. The
Lagrangian critical-point system for a constrained polynomial optimization has degree
scaling combinatorially with the number of constraints via elimination; a rough
Bézout-style upper bound (product of constraint degrees, all degree ≤ 2 here) is on the
order of `2^(11+5+3) ≈ 2×10^5` for the equality-only KKT system before even folding in
the area objective's gradient (which is itself only piecewise-quadratic per face, but
differentiating through *which* faces are active adds combinatorial branching on top of
the algebra). That is a description of what a real run would have to search, not a
number anyone here computed by running a solver.

**Feasibility here:** genuinely uncertain, and this is not a guess — it's a size
description without a run to confirm it. A well-tuned Bertini/PHCpack/
HomotopyContinuation.jl run on a system this size with mostly-quadratic equations is
plausibly within reach on a workstation (published examples in that literature solve
comparable or larger polynomial systems), but "plausibly within reach for that
software" and "actually solved it" are different claims, and this environment has
neither the software nor, within this session, the budget to stand up a fresh
Julia+HomotopyContinuation.jl toolchain from the network and validate it before running
it. **This was not run.** Reframing 1 is not settled here — it is scoped precisely
enough (system size, degree bound, what solver would be needed) that a future session
with that toolchain available could attempt it directly instead of re-deriving the setup.

**Verdict: real leverage on (A), blocked purely by toolchain, not by the math.** Highest
apparent value of the "hard tooling" reframings, but unexecuted. See the prototype
section below for what *was* run instead — a pure-Rust proxy (repeated-restart local
search) that answers a weaker version of the same question with the tools actually
available.

## 2. Decidability / SMT over nonlinear real arithmetic (Tarski / CAD)

**Maps onto:** "does a feasible point exist realizing this skeleton with total area >
X" is a sentence in the first-order theory of real closed fields (existential
quantifiers over the same polynomial system as item 1, comparison `> X` added).
Decidable by Tarski's theorem; Cylindrical Algebraic Decomposition (or Z3's `nlsat`, or
dReal's delta-decidable relaxation) implements this in practice. If it terminates and
says "no configuration beats X" at the recorded X for some open n, that is an actual
**proof** — the first one ever produced for *any* entry (trivial-labeled entries are
equally unproven, per the (D) correction above), closing (D) for that n.

**Attacks:** (D) directly (proving optimality, not just constructing). Weakly (A) too
(same question, decision-procedure framing instead of root-counting framing) but with a
strictly worse complexity profile for actually finding the optimal value (CAD proves a
yes/no comparison against a fixed X; finding the true supremum this way means a bisection
loop over X, each iteration a full CAD/SMT call).

**Complexity ceiling — where does this actually die:** CAD is doubly exponential in the
number of *variables* (not equations). At n=11 (split-hub), the gauge-fixed variable
count is ~23; general-purpose CAD implementations (Mathematica's `Resolve`/`Reduce`,
Z3's incomplete-but-often-effective `nlsat`, QEPCAD) are reported in the literature as
practical up to roughly 4-8 variables for *full* CAD, with `nlsat`-style incomplete
methods (SAT-modulo-theories search rather than full elimination, no completeness
guarantee) sometimes handling more in specific favorable cases but with no general
bound. **n=8** (the smallest open entry, skeleton size unknown pending that agent's
result, but on the order of n − 3 ≈ 5 moduli dimensions gauge-fixed, roughly 10-16 raw
variables before gauge-fixing) is already at or past the edge of what full CAD handles
reliably; **n=11**'s ~23 variables is well past it for a complete decision procedure.
An incomplete solver (`nlsat`/dReal) might still terminate with an answer at n=8 or
n=11 without a completeness guarantee — worth trying if the tool is ever available —
but "might terminate, no guarantee" is a materially weaker claim than "CAD terminates
and proves it," and this document does not have a run to report either way.

**Feasibility here:** blocked the same way as item 1 — no Z3, no dReal, no CAD tool in
`nix develop`, and standing one up from network is out of scope for this session's
budget (see toolchain note above).

**Verdict: real leverage on (D) specifically — the question nobody has ever closed for
any entry — but the honest ceiling is small (roughly n=8, maybe not even that, for a
*complete* method) and it's unexecuted here for the same toolchain reason as item 1.**

Given the (D) correction above (no entry is proven, "trivial" ones included), the
**natural first target is not one of the nine open n, but the smallest "trivial" entry**
— e.g. n=12 (the 2×2 unit-square grid, area exactly 4). It has the simplest possible
skeleton (integer coordinates, a dihedral symmetry group that CAD/SMT solvers can
sometimes exploit to cut the effective variable count, and a small, well-understood
moduli space), so proving `A(12) = 4` — a first for this problem regardless of which
entry it's proven for — is plausibly the actual easiest non-trivial *proof* target this
whole document points at, more so than n=8 (which is open, asymmetric, and has no
symmetry to exploit). Worth flagging to a future session with Z3 available: try `nlsat`
on n=12 first, both because it's the cheapest attempt and because a negative/
inconclusive result there is informative before spending the same setup cost on a
genuinely open n.

## 3. The discrete layer as a graph / matroid enumeration problem

**Maps onto:** (B)'s actual failure mode. `random_growth` grows skeletons by applying
M1-M4 moves from a triangle seed; it's a *sample* of the move-reachable subset of valid
skeletons, not an enumeration of all of them, and the move set provably cannot reach some
valid skeletons (the n=4 unit square: a 4-cycle needs the *first* move from the triangle
seed to already be a degree-preserving rewire, and none of M1 (triangle flap, adds a
vertex), M2 (quad sharing 1 edge), M3 (quad closing a notch, needs an existing
2-incident vertex — the triangle's vertices are 2-incident, but M3's notch move as coded
consumes 2 existing fences at a shared vertex and produces a 2-fence detour between their
*other* endpoints, which for a triangle's vertex 0 (incident to fences (2,0) and (0,1))
targets vertices 2 and 1 that are already fence-adjacent, degenerately closing back to
the same triangle rather than opening a square) or M4 (T-junction chord, adds a fence
that lands mid-segment, never produces a plain 4-cycle) can turn a 3-cycle into a 4-cycle
in one or more steps without ever producing an intermediate non-simple or self-overlapping
graph that the search would then have to accept. Recast as combinatorics: the right object
is not "graphs reachable by these 4 moves" but the actual target class — planar graphs
(straight-line, since fences are straight segments and only cross at valid incidences)
with every vertex either degree ≥ 2 (ordinary corner) or degree-1-plus-a-T-junction-
target, `n` edges, realizable with unit edge lengths (a further, geometric, filter on top
of the pure combinatorics — see caveat below). Cox et al. (arXiv:1901.00319) enumerate
3-connected cubic planar graphs for the analogous least-perimeter partition problem, which
is the closest existing precedent for "enumerate the right graph class exhaustively
instead of sampling it."

**Attacks:** (B) directly — this is the actual blocker, not a hypothetical. Indirectly
(D): an exhaustive enumeration at small n, combined with the inner coordinate optimizer
(already reliable — see `anneal.rs`'s SA converging every polynomial and hub-family case
tried), would let you check "no skeleton beats the record" across *every* combinatorial
possibility at that n, which is close to a computer-assisted proof of (D) modulo the
open question (A) (global-not-just-local coordinate optimum per skeleton).

**What's the right graph class, concretely:** vertices partition into "ordinary" (degree
≥ 2 in the fence graph) and "T-junction" (degree 1, with a designated target edge to land
on, target ≠ any edge incident to the vertex). Edges = fences, exactly n of them. Planar,
straight-line-realizable (not every abstract planar graph is; this is a real filter, not
just a bookkeeping label — see caveat below). No two edges may cross except at a valid
incidence (endpoint-on-endpoint or endpoint-on-interior); this is stronger than plain
planarity of the abstract graph, since it also constrains geometric realizability, which
is where item 3 and item 1 have to hand off to each other (enumerate the discrete
skeleton here, then hand each candidate to the item-1-style coordinate solve).

**Feasibility at the open n (13-18):** this is the honest hard part, and unlike items 1-2
it is *not* blocked by missing tooling — it's blocked by the enumeration itself being
large and by not having a clean generating grammar for "planar graphs with this exact
degree/T-junction mix, straight-line-realizable, n edges" the way there's a known one for
3-connected cubic planar graphs. A crude upper bound: even restricting to simple planar
graphs on `v` vertices with `n` edges (ignoring the T-junction / realizability filters
entirely), the count grows explosively — planar graph enumeration on 15-20 vertices
(a plausible vertex count for n=13-18 skeletons, since `vertex_count` runs comparable
to or somewhat above `n` once T-junction targets add fresh vertices) is already in
the billions+ range in the unrestricted case (McKay/Brinkmann-style planar-graph
generators such as `plantri` report counts of unlabeled 3-connected planar
triangulations climbing past 10^8-10^9 well before 20 vertices; this class here is
looser than triangulations, so no direct number is claimed for it, but the growth rate
is the same qualitative "explodes fast" shape) — this is offered as an order-of-magnitude
sanity check on why naive enumeration is not obviously tractable, not as a computed count
for this specific graph class, which nobody has generated. The redeeming structural fact,
not yet exploited by this crate: the target isn't "all planar graphs of that vertex
count," it's specifically graphs built from *unit-length, area-capped* pieces, which is a
much sharper filter than planarity alone — most planar graphs on 15+ vertices don't admit
any unit-edge-length straight-line realization at all (that's a strong geometric
constraint, not just a combinatorial one), so the *real* search space, after both filters,
is almost certainly orders of magnitude smaller than the raw planar-graph count above.
Nobody has characterized how much smaller, which is precisely the open research question
this reframing would need to answer to become tractable rather than merely well-posed.

**Verdict: highest-value reframing of the six, and the correct diagnosis of why (B) is
failing — it's being attacked as growth-heuristic search instead of exhaustive/structured
enumeration.** Not fully executed here (no new enumerator was built — see prototype
choice below for why item 1's proxy was chosen instead within this session's time), but
concretely scoped: the actionable next step is a **constrained** enumerator (unit-length
realizability as an early-pruning filter, not planarity alone as a late one) rather than
either `random_growth`'s move-sampling or brute planar-graph enumeration.

## 4. Linear / convex structure

**Maps onto:** with the skeleton *and* combinatorial face structure fixed, is any part
of the optimization convex or LP-representable? Face areas (shoelace formula) are
bilinear in vertex coordinates, hence **not** convex or concave in the coordinates
directly — same obstruction the docs' §1.1/§1.4 already note (the objective is smooth
but not convex; SA is used precisely because there's no cheap convex relaxation). A
change of variables to make it linear would need face areas themselves (or something
that determines them, like a stress/tension per edge in a bar-and-joint framework) as
the primary variables instead of coordinates — the natural move here is a **force /
stress-network dual**: treat each fence as a bar carrying a scalar tension/compression,
Maxwell-Cremona-style, and ask whether the area-maximizing configuration corresponds to
a self-stress with a sign pattern that's LP-checkable. This is exactly the territory the
parallel KKT/force-network + 3D-polyhedral-lift agent is already working (Maxwell-Cremona
reciprocal diagrams lift a planar stressed framework to a 3D polyhedral surface, the
classical bridge between plane frameworks and convex/LP structure) — as of this check no
write-up from that agent has landed in the tree, so this item is left at the level of
"this is the right direction and someone else is already pursuing it in more depth," not
independently re-derived or duplicated here.

**Attacks:** potentially (A) (a certificate that a stress-network optimum is optimal
would be a much cheaper proof than the full polynomial system of item 1) and, if it
generalizes, (D). Not directly (B) or (C).

**Verdict: real structure exists (bilinear objective, rigidity-matroid-flavored
constraints, a plausible Maxwell-Cremona dual), but the actual leverage — whether the
LP-checkable sign pattern exists and whether it certifies global rather than just local
optimality — is being worked by the parallel force-network agent, not re-derived here to
avoid duplicating that effort.** Re-check that agent's output before doing further work
on this item.

## 5. motif's own domain: egglog / equality saturation

**Maps onto:** in principle, skeletons as terms and augmentation moves (M1-M4) as
rewrite rules, with equality saturation exploring the skeleton space and an extraction
cost function picking the best-area result. Read against this crate's own
`CLAUDE.md` egglog caveats before judging, not just against what sounds appealing in the
abstract:

- Equality saturation proves **equalities** between terms under confluent-enough rewrite
  systems; it is not naturally a *search-and-optimize* engine for "find the assignment of
  continuous coordinates that maximizes a real-valued objective subject to inequality
  constraints." egglog's e-classes carry symbolic terms, not floating-point numeric state
  that an inequality constraint (area ≤ 1) needs to be checked against continuously. The
  actual hard part of this problem — n − 3 continuous degrees of freedom per skeleton,
  optimized against a bilinear objective with an active-inequality-constraint KKT
  structure (§1.4) — has no natural expression as term rewriting at all; that part stays
  exactly what `anneal.rs` already does, and reframing it into egglog would not change it.
- What egglog *could* express is the **discrete** move layer of item 3 (M1-M4 as rewrite
  rules on a skeleton-as-term representation), with equality saturation exploring which
  sequences of moves reach a target n and deduplicating skeletons that are really the same
  graph reached by different move orders. This is a real but narrow fit — it only touches
  (B), and only the "which skeletons are move-reachable and how many redundant ways can
  you reach the same one" part of (B), not the "why does the move set fail to reach the
  unit square" part (item 3's actual diagnosis: the move set's expressive gap, not a
  redundant-search-order problem — equality saturation deduplicates redundant paths to
  the *same* reachable set, it does not enlarge the reachable set itself). Fixing
  `random_growth`'s coverage gap (item 3) needs new moves or a different generation
  grammar, not a better search strategy over the existing moves' reachable set — so
  equality saturation would optimize the wrong bottleneck here.
- The bidirectional-rewrite-safety caveat in `CLAUDE.md` (`f(x) = x` and inverse laws are
  forward-only; associativity is the safe bidirectional case) matters directly here:
  M1-M4 are inherently one-directional growth moves (a skeleton gains fences), so encoding
  them as egglog rewrites would already be forward-only by construction, consistent with
  the caveat, but that also means egglog buys nothing over just running the moves forward
  in the existing Rust code — there's no equality being discovered that a direct forward
  application wouldn't already produce, only deduplication of reaching the same graph two
  ways, which for a growth-only (never-shrinking) move set is a comparatively small win.

**Attacks:** at most a sliver of (B) (deduplicating redundant discrete-search paths), and
even that is marginal since it doesn't address why the move set has a coverage gap in the
first place.

**Verdict: no, not a fit, and this is checked against the actual caveats rather than
asserted — the problem's genuine hard part (continuous optimization under an inequality-
constrained bilinear objective) has no natural egglog encoding, and the part egglog
*could* touch (discrete move-search dedup) is not where the real leverage on (B) is (item
3's diagnosis: a move-set expressiveness gap, not a redundant-path problem). A forced fit
to the host repo would be worse than none, per the task's own instruction — recorded here
as "relabelling, no leverage."**

## 6. Other candidates considered

- **Integer programming.** Once a skeleton and its coordinates are both fixed, there is
  no integer-valued decision left (everything is continuous or already resolved by the
  skeleton choice) — IP would only enter if the *discrete* skeleton-choice layer (item 3)
  were formulated as an integer program over which edges/incidences to include, which is
  a restatement of item 3's enumeration problem in a different solver's input format, not
  a new source of leverage. **Relabelling of item 3, no independent leverage.**
- **Sphere-packing-style LP/Delsarte dual bounds for an upper bound on achievable area.**
  This is the one candidate that could give something the crate currently has *nothing*
  for: an upper bound proving no configuration at a given n can beat some value, which is
  exactly what's missing for (D) (every current number is a lower bound from a
  construction; nothing gives upper bounds). The Delsarte/LP-bound method in sphere
  packing works by exhibiting a single auxiliary function whose linear-programming
  duality forces an upper bound on a packing density, independent of the packing's
  structure. Whether an analogous auxiliary function exists here is genuinely unclear and
  not derivable by inspection — packing LP bounds exploit translation/rotation
  invariance and a well-understood inner-product structure (positive-definite kernels on
  a homogeneous space) that this problem's finite, combinatorially-varying-face-count
  setup does not obviously have an analogue of. **CONJECTURED, unexplored**: flagged as
  the single most valuable unexplored direction for (D) specifically (upper bounds,
  which nothing else here produces even in principle — item 2's CAD/SMT route also
  produces upper-bound-flavored certificates but only per-instance and only within its
  small-n ceiling, whereas an LP/Delsarte-style bound, if one exists, would be a *formula*
  valid at every n at once) — but this document does not have an argument for why the
  needed auxiliary function would exist, only that the *class* of technique is the right
  shape for the missing gap. Not prototyped: no plausible auxiliary function was found to
  even attempt encoding, and inventing one without a derivation would be exactly the kind
  of unearned confident guess the task's disposition rules forbid.

  **Coordination note (from the coordinator, attributed, owned by the parallel
  upper-bounds agent — recorded here because it bears directly on this item, not
  independently derived or worked further by this document):** there is a standing
  **polyomino ceiling conjecture** — `A(n) < A*(n)` where `A*(n) = min{A : f(A) > n}`
  (the largest polyomino area still reachable within n edges by the Harary-Harborth
  formula). It holds on all 22 recorded table entries and is far tighter than the
  isoperimetric bound `n/sqrt(pi) ~= 0.5642n`. It is unproven, and its missing step is
  exactly the same gap the (D) correction above names — it implicitly assumes squares
  are area-optimal, which is unproven, so it cannot presently be *used* to derive
  anything, only observed to hold. If a dual/LP formulation (of the kind this item
  speculates about) could prove it, that would settle the asymptotics in one shot:
  inverting `f` gives `A*(n) ~= n/2 - sqrt(n/2)`, which the polyomino family already
  achieves, so the conjecture would pin `A(n)` to within `O(sqrt(n))` for every n at
  once — a stronger and more general result than anything else surveyed in this
  document. This is the sharpest concrete form the "does an LP/Delsarte-style bound
  exist here" question could take, and it belongs to the upper-bounds agent's thread;
  not duplicated here.
- **Tropical geometry.** The natural tropicalization move (replace `+, ×` with
  `min/max, +`) fits problems whose defining relations are naturally piecewise-linear in
  log-coordinates (Newton polytopes, valuations) — this problem's defining relations
  (Euclidean length = 1, collinearity, shoelace area) are not naturally expressed that
  way; distance and area do not tropicalize into anything meaningful without first
  discarding almost all the metric information that makes the problem the problem it is.
  **No fit found; not pursued further** — recorded so a future pass doesn't re-open it
  without new information.

## Summary table

| # | Reframing | Attacks | Concrete cost/feasibility here | Verdict |
|---|---|---|---|---|
| 1 | Polynomial system / homotopy continuation | (A) | ~23 free vars at n=11, degree bound ~2^19; no Julia/PHCpack/Bertini in `nix develop`, not installed this session | Real leverage, blocked by toolchain, unexecuted; scoped for a future session that has the tool |
| 2 | SMT / CAD (Tarski decidability) | (D), weakly (A) | CAD ceiling ~4-8 vars in general; n=8 already at/past that, n=11 well past; no Z3/dReal here | Real leverage on the one question nobody has closed, but honest ceiling is small and unexecuted |
| 3 | Graph/matroid enumeration of the discrete layer | (B) directly, indirectly (D) | No tooling blocker; blocked by enumeration size and lack of a realizability-first generating grammar | **Highest-value** — correctly diagnoses why (B) fails; not fully executed, concretely scoped |
| 4 | Convex/LP structure, force-network dual | (A), possibly (D) | Bilinear objective, no direct convexity; Maxwell-Cremona dual plausible | Real structure, being worked by the parallel force-network agent — deferred, not duplicated |
| 5 | egglog / equality saturation | sliver of (B) | Checked against `CLAUDE.md` caveats directly | **No leverage** — relabelling; continuous part has no natural encoding, discrete part isn't where the coverage gap is |
| 6a | Integer programming | — | — | Relabelling of item 3 |
| 6b | Sphere-packing LP/Delsarte dual bounds | (D) | Unclear if an auxiliary function exists; not derivable by inspection | Most valuable *unexplored* direction for upper bounds, but genuinely open, not prototyped |
| 6c | Tropical geometry | — | No natural fit to Euclidean length/area constraints | No fit |

## Prototype: item 1's tool-constrained proxy, run against (A)

Full homotopy continuation (item 1) and CAD/SMT (item 2) were both scoped in detail above
and both blocked by the same fact: `nix develop` here provides only the Rust toolchain,
no Julia/Python/Z3/dReal, and standing one of those up from the network mid-session was
judged not worth the risk of destabilizing a shared `flake.nix` while five other agents
are live in this tree, for a payoff that still wasn't guaranteed to finish in budget.

What *is* available and directly answers the specific gap `asymmetric-methods.md` §5
names ("global optimality... UNKNOWN — no multi-start was run") is a pure-Rust proxy:
run the existing `anneal.rs` SA optimizer many independent times on the *same fixed*
n=11 split-hub skeleton, from both small perturbations of the traced solution and fully
independent random initial guesses, and see whether any run finds a valid configuration
beating 3.5372167764.

This is not a certificate — SA finding nothing better is evidence, not proof (that
distinction belongs to items 1/2, which remain the way to actually *prove* (A)). It's
built as `examples/n11_split_hub_multistart.rs` (52 runs: 4 noise levels × 8 seeds of
"near" perturbation of the traced coordinates, plus 20 "far" fully-random-in-a-bounding-
box starts, each run at 300,000 SA iterations, matching `AnnealParams::default()`'s
schedule otherwise).

**Result (VERIFIED, this run):** 52 runs total, 25 valid (27 hit an unresolved SA
penalty residual and were correctly excluded, not counted as competing points — see
`Configuration::validate` gate in `search.rs`'s own convention). Across all 25 valid
runs, **no run beat the published record**; the closest approaches were:

- Best "near" run (small perturbation of the traced solution): 3.53682420 (sigma=0.3,
  seed=0) — just under record.
- Best "far" run (fully random init, no information from the traced solution at all):
  3.53707729 (seed=16) — also just under, and notably a *fully independent* random start
  converged to within 1.4e-4 of the recorded value without ever seeing the traced
  coordinates.
- The single best area found across every run was **3.5370772893**, ~1.4e-4 below
  3.5372167764 — consistent with SA's own convergence noise (the crate's default
  tolerance target is 1e-6, but that requires the specific fine-tuned schedule the
  `split_hub_pinwheel_n11` test's exact traced start gets; a generic multistart at the
  same iteration budget lands close but not bit-for-bit).
- **A second, distinctly worse basin appeared repeatedly among the far-random starts**:
  10 of the 20 far-random runs converged to area ~2.38-2.43 (seeds 0,1,2,6,8,9,11,12,18,
  19), a materially different value from both the ~3.53-3.54 basin and each other-random
  seed's failures — i.e. this skeleton's coordinate landscape has at least one other
  attracting region reachable from generic starting points, and it is worse than the
  known optimum every time it was found. This is itself informative: it shows the
  multistart is actually exploring different basins (not just re-finding the same point
  from everywhere, which would say less), and every basin found is either near the
  known optimum or below it, never above.
- At the widest perturbation tested (sigma=0.6), **every one of the 8 near-runs came
  back invalid** — consistent with §1.4's picture of an isolated (or nearly isolated)
  optimum: push far enough and the SA schedule used here (300,000 iterations, otherwise
  default) doesn't reliably re-find a valid configuration at all, let alone a better one.

**Reading of this result:** this is empirical support, not proof, for the n=11 split-hub
skeleton's KKT point being at least a strong, basin-dominant local optimum — 52
independent runs from both near and far starting points, at a substantial iteration
budget, never found anything better, and the only competing basin found is
substantially worse. It does **not** resolve (A): SA multistart, however extensive,
cannot rule out an untried basin the same way homotopy continuation's exhaustive root
enumeration (item 1) or a CAD/SMT "no better point exists" certificate (item 2) would.
Framed against the summary table above: this prototype is the pure-Rust proxy for item
1, run because item 1 itself is blocked by toolchain availability, and it narrows (A)
from "no multi-start was ever run" to "an extensive multi-start was run and found
nothing better," which is real progress on the open question but explicitly short of
closing it.

Reproduce with:
```
cd crates/motif-fences && cargo run --release --example n11_split_hub_multistart
```
