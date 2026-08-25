# Force-network / equilibrium characterization of fence optima

Scope: is there a useful force-network (graphic-statics / Plateau-equilibrium sense,
**not** granular-jamming) characterization of area-maximizing fence configurations, and
does it prune the skeleton search? Grounded in `docs/asymmetric-methods.md` (the DOF/
moduli counting, §1) and the n=11 split-hub solve (`tests/records.rs::split_hub_pinwheel_n11`,
commit 3a96e7a).

**Status correction carried through this whole document:** the n=11 split-hub
configuration (area 3.5372167764) and the point-hub variant (3.5017721551) are
**KKT points** — local stationary points of a single SLSQP run from a pixel-traced
initial guess, each `Configuration::validate()`-valid and matching a published
best-known value (Tohanean's 3.53721+ for split-hub) to numeric precision. Neither is
established as a global optimum for its own skeleton (no multi-start), and Friedman's
page claims no optimality proof for any non-trivial entry either. Everything below that
says "the force balance holds at n=11" is a statement about the derivation being
consistent with a KKT point of the stated Lagrangian — evidence the *math* is right, not
evidence the *configuration* is optimal.

Tags per repo convention: **DERIVED**, **VERIFIED**, **CONJECTURED**. Untagged prose is
exposition linking tagged claims.

Numerical verification scripts: `docs/force-network-verify/*.py` (Python/numpy/scipy,
run via `nix-shell -p "python3.withPackages(ps: [ps.numpy ps.scipy])"` — this crate's own
flake has no Python, these are one-off verification scripts, not part of the Rust build).

## 1. Setting up the Lagrangian

**DERIVED.** A configuration lives on the equality-constraint variety of
`docs/asymmetric-methods.md` §1.1 (unit lengths, T-junction collinearity) intersected
with the region where every bounded face's area is `<= 1`. The objective is total
enclosed area `A`.

**Key structural fact, used throughout (DERIVED):** for any valid configuration, the
bounded faces of the arrangement tile the interior of the outer (unbounded-face)
boundary exactly, so `A = sum of bounded face areas = area enclosed by the outer
boundary polygon`. Consequently **`grad A` is nonzero only at vertices that sit on the
outer boundary** — interior vertices (chord feet, hub points, T-junction landings not
on the outer ring) feel zero direct pull from the objective. This is not a special
feature of the n=11 skeleton; it holds for any planar arrangement where bounded faces
tile the outer boundary's interior (true of every construction and skeleton this crate
handles). It means every interior vertex's stationarity condition is a *pure* constraint
force balance, with no external "driving" term — structurally identical to an interior
node of a Plateau/soap-film network, or a free (unloaded) joint in a truss.

Lagrangian for the maximization, with `g_i` the `n` length constraints
(`|P_{u_i}-P_{v_i}|^2 - 1 = 0`), `c_j` the T-junction collinearity constraints
(`cross(host_a, host_b, foot) = 0`), and `a_F <= 1` the per-face area caps:

```
L = A - sum_i lambda_i * g_i - sum_j mu_j * c_j - sum_{F active} pi_F * (a_F - 1)
```

Stationarity `grad_{x_v} L = 0` at every vertex `v`, for a max problem with `<=`
constraints, requires `pi_F >= 0` on every *active* face (area exactly 1) at the
optimum — the standard KKT sign condition.

### 1.1 Physical read of each term (DERIVED)

- **Length term.** `-2*lambda_i*(x_v - x_other)` is a force along fence `i`'s own
  direction, magnitude `2*lambda_i` (edge length is 1), pulling toward or pushing away
  from the fence's other endpoint. This is literally an axial **tension/compression**
  along each fence — the same object as a bar's internal force in truss statics.
- **Face-area term.** `d(area_F)/d(x_v) = (1/2) * rot90(next_F(v) - prev_F(v))` (the
  standard discrete-shoelace-gradient identity, `next_F`/`prev_F` being `v`'s neighbors
  in face `F`'s boundary cycle). `-pi_F * grad(area_F)` is a force **perpendicular to
  the chord joining `v`'s two neighbors in that face**, magnitude proportional to that
  chord's length — the discrete form of "pressure times normal," i.e. a **pressure
  force** from face `F` pushing on vertex `v`.
- **T-junction (collinearity) term.** For foot `p` on host fence `(a,b)`,
  `grad_p(cross(a,b,p)) = rot90(b-a)` — purely **normal to the host fence's direction**.
  A T-junction constraint can only react perpendicular to its host, never tangentially
  (a bead-on-a-wire / roller). Consequence: **at a T-junction, only the tangential
  component of the sum of all other forces (fence tensions, face pressures) needs to
  vanish** — the normal component is whatever `mu_j` needs to be, absorbed by the
  constraint, exactly as the task brief anticipated.
  Also **DERIVED, easy to miss:** the same collinearity constraint has nonzero gradient
  at the *host's own endpoints* `a`, `b` too (`grad_a(cross)`, `grad_b(cross)`, both
  nonzero and dependent on the between-ness fraction `t` of where the foot lands). A
  T-junction therefore doesn't just react at the foot point — it also transmits a
  reaction, split `(1-t)`/`t` between the host's two endpoints, exactly like a point
  load on a beam transmitting to its two supports. This is a genuinely non-classical
  (non-bar-only) feature of this problem's force network: T-junctions are structurally
  more like beam contacts than pin joints.
- **An `m`-way endpoint coincidence** (§1.3 of `asymmetric-methods.md`) is not a special
  case of the force balance at all — it's just a free vertex where `m >= 3` fence
  tensions (instead of 2) sum into the same 2-equation balance, plus whatever face
  pressures border it. No new mechanism, more terms in the same equation.

## 2. Does the 120° rule survive? (DERIVED)

**No — and the mechanism is exactly what the brief anticipated.** In classical Plateau
minimal networks, edge *lengths* are free, so the length term in the Lagrangian is
`sum |e_i|` (not a constraint), and stationarity at a free 3-valent vertex gives
`sum_i unit_vector_i = 0` — a *fixed-magnitude* (all 1) vector-sum condition, which for
three edges forces exactly 120° angles between them.

Here, length is *pinned* by an equality constraint whose multiplier `lambda_i` is
**free** (any sign, any magnitude) — the force along each fence is `2*lambda_i` times a
unit vector, with `lambda_i` absorbing whatever magnitude is needed. At a free vertex
with only length-constrained neighbors and *no* adjacent active-area-cap face, the
balance `sum_i lambda_i * unit_vector_i = 0` is, for generic (non-collinear) edge
directions, solvable for **some** choice of real (possibly negative) `lambda_i` at
**any** angle configuration — two unknowns (or more, for `m > 2` edges) against a
2-component vector equation has a solution for all but measure-zero degenerate
direction sets. So the length multiplier's freedom **does** wash out any angle
condition at a plain junction: **the tangential/free-vertex stationarity condition is
not a geometric constraint on angles at all, generically** — it is solvable trivially,
and becomes a genuine constraint on the *sign and existence* of a consistent multiplier
assignment only once a vertex also carries a fixed (non-free) pressure term from an
adjacent active-cap face, since `pi_F` is *not* free at that point (it's shared by every
vertex bordering `F`, so it must be consistent everywhere at once) — at those vertices
the balance is a real equation in the `lambda`'s and `pi`'s, but still says nothing
about angle per se; it says the *stresses*, not the *geometry*, must satisfy a linear
compatibility condition. **Verdict: the 120° rule is correctly replaced by nothing
geometric — the constraint structure genuinely degenerates the angle condition away,
exactly the "clean vacuous" outcome the brief flagged as an acceptable finding for this
sub-question.** What survives instead is a *linear-algebra* solvability condition on
signed multipliers (self-stress existence, §5-6) — a Maxwell-type condition, not an
angle law.

## 3. Numerical verification

Method for each case: fix the (already-solved) coordinates, build the full constraint
Jacobian (length + collinearity rows, one active-face-area row per face with area `==1`
to numerical precision), and solve `J^T v = grad(A)` by least squares for the combined
multiplier vector `v = (lambda, mu, pi)`. If the point is a genuine KKT point, this
residual should vanish to numerical-differentiation precision (finite-difference
gradients here use central differences at `eps=1e-7`, so residuals around `1e-8` are
the expected floor, not a discrepancy).

### 3.1 n=11 split-hub (VERIFIED — closes)

13 vertices, 11 fences, 5 T-junctions (`docs/force-network-verify/kkt_n11_splithub.py`,
coordinates lifted from `tests/records.rs::split_hub_pinwheel_n11`). Active faces:
`pent1`, `pent2`, `hexf` (all area `1.0` to float precision); `quad` inactive at
`0.5372167764`, matching the doc's existing note in `asymmetric-methods.md` §1.4.

```
J shape: 19 x 26   (11 length + 5 collinearity + 3 active-area rows; 13 vertices x 2)
rank(J^T): 19 (full column rank)
residual ||J^T v - grad(A)||: 1.3e-8
```

All recovered multipliers:

- Length tensions `lambda_i`: **all 11 positive** (range 0.106 to 0.375) — every fence
  is in tension, none in compression.
- T-junction reactions `mu_j`: 4 of 5 positive, one (`H1` landing on `Q1-H2`) negative
  — sign here is a convention artifact of collinearity-triple orientation, not
  independently meaningful without fixing an orientation convention per T-junction (not
  investigated further).
- Active-face pressures `pi_F`: **all 3 positive** (0.33-0.40) — satisfies the KKT sign
  requirement `pi_F >= 0` for a `<=`-constrained active cap in a maximization.

**The balance closes.** Residual at the finite-difference noise floor, correct KKT
signs throughout. This is a statement about the Lagrangian derivation, not about global
optimality (see the status note at the top).

### 3.2 n=11 point-hub (VERIFIED — closes)

Same boundary, all four chords forced through one point `H` (m=4). Re-solved from
`/tmp/fences-img/solve_pointhub.py`'s SLSQP run to confirm coordinates
(`eq residual 6.7e-16`, `ineq min -4.4e-16` — a tight solve), area 3.5017721551,
matching the recorded value. `docs/force-network-verify/kkt_n11_pointhub.py`:

```
J shape: 18 x 24   (11 length + 4 collinearity + 3 active-area rows; 12 vertices x 2)
rank(J^T): 18 (full column rank)
residual: 5.8e-8
```

All 11 `lambda`'s positive, all 3 active `pi`'s positive (0.23-0.43). Balance closes
here too, same as split-hub.

### 3.3 n=12 trivial 2x2 grid (VERIFIED — closes, with genuine redundancy)

9 vertices, 12 fences, no T-junctions, all 4 unit cells active (area exactly 1 each) —
the sanity-check case, worked by hand-checkable symmetry.
`docs/force-network-verify/kkt_n12_grid.py`.

```
J shape: 16 x 18   (12 length + 4 active-area rows; 9 vertices x 2)
```

Unlike the two n=11 cases, **the multiplier system here is genuinely
under-determined**: `J^T` (18x16) has singular values `[3.78, 3.78, 3.67, 3.46, 3.46,
3.46, 2.35, 2.05, 2.05, 2.00, 2.00, 2.00, 8.9e-10, 4.5e-10, 3.1e-10, 1.1e-10]` — a clean
gap between 12 real singular values (order 1) and 4 that are numerical zero. **Rank 12,
not 16: a 4-dimensional space of self-stresses with zero net load exists.** (An earlier
pass through `scipy.linalg.lstsq`'s own rank estimate mis-reported this as full rank —
its default `rcond` threshold didn't resolve the gap; the SVD with explicit inspection
of the singular-value list is the correct check and is what's used for the number
quoted here.)

Imposing the D4 symmetry of the square explicitly (one tension `a` for all 8 boundary
edges, one tension `b` for all 4 interior edges, one pressure `c` for all 4 cells)
gives an exact solution: `a = 0.10454545..., b = 0.20909090... = 2a, c = 0.58181818...`,
residual `4.4e-9`. All three values positive — correct KKT signs.

**Interpretation (DERIVED from the rank computation):** the fully symmetric grid's
force network is *statically indeterminate* (hyperstatic, in structural-engineering
language) — there is more than one way to distribute stress consistently with
equilibrium, a direct consequence of the configuration's symmetry. The two n=11 cases,
by contrast, have **zero** self-stress redundancy (full column rank, unique
multipliers). This is the first piece of evidence for §6's rigidity/stress duality:
*asymmetric* configurations get an *isostatic* (uniquely determined) force network;
*symmetric* ones get redundant stress freedom. Consistent with, though not a proof of,
`asymmetric-methods.md` §4's claim that symmetric skeletons are a special, sparse
stratum.

## 4. Does it prune? (mixed — mostly negative, one real finding)

**The straightforward hoped-for result — "an incidence pattern admits no consistent
force balance, therefore can't be optimal, check this before solving coordinates" —
does NOT hold as a combinatorics-only test, for a structural reason:** which faces are
*active* (the `pi_F` terms) is not combinatorial data — it depends on the actual solved
areas, which depend on coordinates. The force-balance system's unknown count (`n`
lambdas + `T` mus + `|active|` pis) and hence its solvability isn't fixed by the
skeleton alone; it's fixed by the skeleton **plus** which faces happen to saturate their
cap at the optimum, which is exactly the thing coordinate-search has to find. So the
force network, as derived here, is not a pre-coordinate combinatorial filter in the way
hoped. **This is the requested honest negative for item 4's main question — no
manufactured positive.**

What *does* fall out, weaker but real (DERIVED from §3's rank computations):

- **Existence is not the bottleneck.** By the Maxwell-Cremona-Whiteley correspondence
  (§5), *any* framework that admits a nontrivial equilibrium (self-stress, in the
  extended sense of §5.1) automatically has a valid abstract force network — nothing
  about our two positive checks (§3.1, §3.2) shows the force-balance test excluding
  anything; it merely confirmed consistency at points already known to be KKT points.
  No skeleton was rejected by this test in this investigation.
- **The symmetry/redundancy split (§3.3) is a real, checkable, cheap-to-compute
  signal**, even without knowing the true optimum in advance: a skeleton with a
  candidate *fully-active* (all bounded faces at cap) assignment and a symmetric
  automorphism will generically show self-stress redundancy (rank deficiency in `J^T`),
  while an asymmetric skeleton with the same all-active assignment will generically be
  full rank. This doesn't prune skeletons from being *valid*, but it is consistent with
  (and gives an independent numeric handle on) `asymmetric-methods.md` §4's existing
  argument that symmetric skeletons are the sparse, special stratum — redundancy is
  *wasted* stress freedom relative to what an asymmetric layout gets for the same
  active-constraint budget, one more angle on why symmetric wheel/polyomino skeletons
  are outcompeted at generic n. This is suggestive corroboration, not a new pruning
  rule, and was not turned into an actual search-time filter.
- **What would be needed for a real prune** (not attempted, flagged open): a bound of
  the form "for a skeleton with `V` vertices, `T` T-junctions, and `k` faces, no
  assignment of `0/1` active-face flags to any subset of the `k` faces admits `pi_F >=
  0` solutions" — i.e. a *sign-constrained* linear-feasibility argument independent of
  which subset is active, checkable by e.g. an LP feasibility solve over all `2^k`
  activity patterns (or smarter, via the structure of the equilibrium matroid). This is
  the concrete next step if pruning is wanted; it was not carried out here — it would
  need an implementation of the constraint-matrix builder used in §3's Python scripts,
  ported to Rust and run against `skeleton::random_growth`'s candidates before handing
  them to the coordinate annealer. **CONJECTURED viable, not built.**

**Bottom line for the crate's actual outer-search problem** (the thing motivating this
whole investigation — `random_growth` missing the unit square at n=4 in 200 attempts):
the force network as derived does not hand over a cheap discrete filter that would fix
that. The failure mode there is almost certainly move-selection / seed-shape bias in
`random_growth`, not a force-balance-infeasible skeleton being generated and wastefully
explored — this document doesn't investigate that failure mode further (out of scope
here; owned by `asymmetric-methods.md`'s search-quality thread).

## 5. Maxwell-Cremona / reciprocal diagrams

### 5.1 The theorem, and how it applies here (DERIVED + literature)

Maxwell (1864) and Cremona showed a planar bar framework carrying a self-stress
(edge stresses `omega_e` such that at every free vertex `sum_e omega_e*(v-u) = 0`, i.e.
equilibrium under **zero external nodal load**) has a reciprocal diagram and lifts to a
piecewise-linear polyhedral surface in R^3 (each face of the framework lifts to a
planar facet; the fold direction/sign across each edge encodes the stress sign).
Whiteley (1982) proved the converse: every reciprocal diagram / polyhedral lifting
comes from a self-stressed planar framework. [Sources: search results citing this
history and the Whiteley converse — see citations at the end of this section.]

**The subtlety, worked out here (DERIVED):** our full stationarity system is *not* a
pure self-stress in Maxwell's original (bar-only, zero-external-load) sense, because
the active-face pressure terms `pi_F` act as genuine nonzero nodal loads at every vertex
bordering an active face — this is a *loaded* framework, the generalization handled in
the graphic-statics literature by reciprocal "form and force" diagrams / Thrust Network
Analysis (Block & Ochsendorf and the "algebraic 3D graphic statics" line of work found
via search), not the textbook zero-load Maxwell-Cremona statement.

However, there is a clean way to fold the load back into a genuine zero-load
self-stress (DERIVED, and numerically confirmed as an identity, not an assumption): the
**unbounded outer face itself can be treated as a face of the arrangement carrying unit
pressure**. For any planar subdivision with consistent (interior-on-the-left)
orientation of every face's boundary cycle, the signed areas of *all* faces (bounded,
positively oriented, plus the outer face traversed the opposite way) sum to exactly
zero — confirmed numerically for the n=12 grid
(`docs/force-network-verify/lift_attempt_n12_grid.py`: four unit cells at signed area
`+1.0` each, outer face at signed area `-4.0`, sum `0`). Assigning the outer face
`pi_outer = -1` (matching this sign) reproduces `-grad(A)` exactly via the same
shoelace-gradient formula used for every other face. **So the full KKT system, extended
to include the outer face as a genuine face with fixed pressure `-1`, is exactly a
zero-external-load self-stress on the complete planar arrangement graph** — Maxwell's
theorem's hypothesis is met once the outer face is included this way, not before.

### 5.2 Attempting the actual flat-faceted lift: a genuine negative result (VERIFIED)

Given the reframing in §5.1, the natural next step is to build the actual polyhedral
lift for a checked case and see what solid it is. This was attempted for the n=12 grid
(`docs/force-network-verify/lift_attempt_n12_grid.py`), using the *classical* Maxwell
construction: assign each face `F` a slope vector `s_F`, propagate slope differences
across each shared edge via `s_F1 - s_F2 = omega_e * rot90(v-u)` (`omega_e = 2*lambda_e`,
the edge tension computed in §3.3) by BFS over the face-adjacency graph, then integrate
heights and check that every vertex gets a single consistent height across all its
incident faces.

**It does not close.** Height mismatches of up to `0.42` (same order of magnitude as
the multipliers themselves — not numerical noise) appear at most vertices once more
than 2 faces meet there. **Diagnosis (DERIVED):** the classical edge-jump formula only
encodes the *bar-tension* (`lambda`) contribution to equilibrium; it has no term for the
*face-pressure* (`pi`) contribution, which in the vertex-balance equation acts as a
genuine additional nodal load, not something absorbable into a flat-faceted per-edge
slope relation. Re-including the outer face as `pi_outer = -1` (§5.1) makes the *total*
system a proper zero-net-load self-stress in aggregate, but that doesn't mean the
naive bar-only lift construction — which only ever looks at `lambda`, never `pi` —
sees the pressure loads at all. A face-pressure load is fundamentally a *distributed*
force reaching a vertex from a 2D region (the face), not something transmissible along
a 1D edge the way tension is; folding it into the same flat-faceted-polygon machinery
Maxwell built for bar-only trusses is not simply "add another face" — it needs a
genuinely different (and not derived here) construction.

**This is the requested clean negative, not manufactured:** the naive Maxwell-Cremona
lift does not directly produce a flat-faceted 3D solid for these configurations, because
the fences problem's force network is not a bar-only framework — it has both tension
(edges) and pressure (faces) simultaneously, and the classical theorem's flat-facet
guarantee is specifically a bar-only-framework result. Whether some *other*, more
general lift (curved facets, or bar-only after adding explicit "virtual load bars" from
each pressure-loaded vertex to a common reference — the standard graphic-statics trick
for handling external point loads, sketched but not built here) closes cleanly is an
**open question, not resolved in this investigation.** No dome, bowl, or other
recognizable solid is reported, because none was successfully constructed — reporting
one would be exactly the manufactured-positive this brief warned against.

### 5.3 Generator, not just a test? (negative)

Item asked whether the reciprocal-diagram correspondence gives a *generator* for valid
skeletons, not just a feasibility test. Given §5.2's result (the lift construction
itself doesn't close for this problem's mixed tension+pressure network), there is no
generator to report here — a generator would need the lift (or an equivalent
self-stress parametrization) to actually work first. **Not established, not pursued
further given §5.2.**

### 5.4 Does the graphic-statics literature have a counterpart to this problem's specific constraints? (negative, checked)

Searched: computational/algebraic graphic statics (Van Mele et al.'s "Algebraic 3D
Graphic Statics" line), Thrust Network Analysis (Block & Ochsendorf), classical
Rankine/Maxwell/Cremona reciprocal-figure theory, and pseudo-triangulation/rigidity
surveys. **No counterpart found** for this problem's specific constraint bundle:

- **Unit member lengths** (all bars forced to the same fixed length) is not a standard
  assumption in graphic statics — member lengths there are free, determined by the
  form diagram's geometry, not pinned.
- **T-junction (point-on-segment-interior) incidence** has a rough analogue in
  mechanism/linkage theory (a sliding/roller joint) but isn't a standard feature of
  reciprocal-diagram theory, which is normally built on pin-jointed (vertex-to-vertex)
  frameworks.
- **Per-face area CAP (`<= 1`, an inequality, not a fixed target)** has no counterpart
  found. The graphic-statics literature searched deals in *prescribed loads* (equalities
  on the force/form diagrams) and in some form-finding contexts fixed target areas or
  volumes — not an inequality cap that is only sometimes active, which is exactly the
  KKT complementary-slackness structure this problem has and that literature doesn't
  seem to.

Reported plainly as a gap, not stretched into a false match.

**Sources (from the searches run for this section):**
- [Graphic statics and symmetry](https://www.sciencedirect.com/science/article/pii/S002076832300389X)
- [A Toroidal Maxwell-Cremona-Delaunay Correspondence (Erickson & Lin)](https://jeffe.cs.illinois.edu/pubs/pdf/mctorus.pdf)
- [A differential approach to Maxwell-Cremona liftings](https://arxiv.org/pdf/2312.09891)
- [On Generalized Reciprocal Diagrams for Self-Stressed Frameworks](https://www.researchgate.net/publication/228624375_On_Generalized_Reciprocal_Diagrams_for_Self-Stressed_Frameworks)
- [Algebraic 3D Graphic Statics: Constrained Areas](https://arxiv.org/pdf/2007.15133)
- [Algebraic 3D Graphic Statics: Reciprocal constructions](https://arxiv.org/pdf/2007.15720)
- [Maxwell's reciprocal diagrams and discrete Michell frames](https://www.researchgate.net/publication/257335175_Maxwell's_reciprocal_diagrams_and_discrete_Michell_frames)

## 6. Self-stress count vs. the rigidity (moduli) count — the dual consistency check

`asymmetric-methods.md` §1.3 established (VERIFIED against n=11, via Jacobian rank on
the *primal* side — coordinates modulo constraints): moduli `dim = n - 3 - (m-2)` for an
`m`-way hub; split-hub gives 7, point-hub gives 6.

This document's §3 computed the *dual* side directly: rank of the **transpose**
Jacobian (mapping multipliers to nodal loads), i.e. the dimension of the self-stress
space (kernel of `J^T`, zero-load solutions).

| Case | Primal moduli (rank of constraint Jacobian, `asymmetric-methods.md`) | Dual self-stress dim (this doc, kernel of `J^T`) |
|---|---|---|
| n=11 split-hub (asymmetric) | 7 | 0 (full column rank, 19 unknowns / 19 rank) |
| n=11 point-hub (less asymmetric, one 4-way hub) | 6 | 0 (full column rank, 18 unknowns / 18 rank) |
| n=12 2x2 grid (fully symmetric, D4) | not computed here (trivial by inspection: 0 T-junctions, `n-3=9` before any hub, all 4 cells active) | **4** (rank 12 of 16 unknowns) |

**DERIVED, and this is a genuine consistency check, not a coincidence, though the
exact general Maxwell-counting formula for this problem's mixed edge+T-junction+face
system was not derived (see caveat below):** the two *asymmetric* configurations checked
both have **zero** self-stress redundancy — every multiplier in the system is uniquely
determined, matching the intuition that a generic/asymmetric framework is "isostatic"
(exactly enough constraints, no redundancy) on both the primal (coordinate/moduli) and
dual (stress) sides at once. The one *symmetric* configuration checked (the grid) has
**nonzero** self-stress redundancy (a real 4-dimensional space of zero-load
equilibria) — matching the classical structural-engineering fact that periodic/braced
grids are statically indeterminate, and matching `asymmetric-methods.md` §4's
independent argument (from a totally different direction — n-coverage of symmetric
families) that symmetric skeletons are a sparse, special stratum. Two independently
derived arguments (moduli-coverage in the existing doc; stress-redundancy here) point
the same direction.

**What was NOT derived:** a general closed-form Maxwell-type counting rule
(`self-stress - mechanism = edges - (2V - 3)`, the classical 2D bar-framework formula)
generalized to include this problem's T-junction reactions (which are not pin joints —
§1.1 showed they also load the host's two endpoints, a beam-contact not a bar) and its
face-pressure loads (not present in the classical formula at all). The three numeric
data points above are consistent with the qualitative content of Maxwell's duality
(genericity <-> uniqueness, symmetry <-> redundancy) but do not by themselves establish
the generalized formula; deriving and checking one against more cases (n=9 hexagon,
n=18/21 sub-polygon hubs from `asymmetric-methods.md` §1.3) is flagged **CONJECTURED
worth doing, not attempted here.**

## 7. Is this a slice of something 3-dimensional? (expanded scope, from the coordinator)

The question of whether 2D fence configurations are usefully read as sections/
projections of a 3D object is, per §5.1, literally the same question as "does this
framework carry a self-stress" — Maxwell-Cremona is exactly that lift theorem. §5
already answers the technical form of this question (yes for existence in the extended
zero-load sense of §5.1; no for producing an actual flat-faceted solid, §5.2's negative
result). This section adds the remaining specific sub-questions from the expanded brief.

### 7.1 What does the (attempted) lift look like for the known cases?

Only the n=12 grid lift was attempted (§5.2), and it **did not close** — there is no
lifted surface to describe for any case. **This sub-question has no positive answer to
report**; describing a shape for a lift that wasn't actually constructed would be
fabrication. The n=9 hexagon-with-spokes and the n=11 split-hub lifts were not attempted
(no reason to expect a different outcome than §5.2's grid result, given the same
tension+pressure structure applies to both, but this is an inference, not a check —
flagged **CONJECTURED (same failure mode expected), not verified**).

### 7.2 Does the area-<=1 cap mean anything upstairs (volume/height)?

**Not established, and no positive claim is made.** The natural guess — that a
per-face area bound becomes a height or volume bound on the lifted surface — was not
reachable, because no lift was successfully built to check it against (§5.2). Nothing
here confirms or refutes this guess; it is simply untested. Flagged **OPEN, not
CONJECTURED even**, since no partial evidence either way was produced.

### 7.3 Honest null result

Stated plainly, as the brief asked for: **the 3D-lift framing does not, in this
investigation, produce a working 3D object for the fences problem.** The reason is
specific and derived, not a shrug: this problem's force network mixes bar tension and
face pressure, and the classical Maxwell-Cremona lift (the thing that would make "slice
of a 3D solid" concrete) is a bar-only-framework theorem. The extension needed to
handle face pressure was not found or built here. The unit-length constraint *does* have
a clean counterpart upstairs in the sense that it's exactly what makes the multipliers
free real numbers rather than length itself being free (§2) — but that's a statement
about the *2D* problem's algebra, not about anything appearing three-dimensionally.

### 7.4 Secondary framings (mentioned only because the brief allowed it — not pursued)

The brief's two secondary framings (moduli spaces as fibers over `n` with augmentation
moves as inter-fiber maps; the full configuration set as a variety in `R^{4n}` with the
area cap carving out a feasible region whose extreme points are the records) were not
found to help resolve any of §§1-6's questions and are not developed further here —
per the brief's own instruction to mention them only if they turned out to help. Noting
their non-use rather than silently dropping them, since the brief asked for them to be
checked.

### 7.5 Kelvin problem / Weaire-Phelan (checked, analogy only, not a technical link)

Searched briefly. The Kelvin problem (minimal-surface-area partition of space into
equal-volume cells) is solved best-known not by the most symmetric candidate (Kelvin's
truncated-octahedron foam) but by the **less symmetric** two-cell-type Weaire-Phelan
structure, which beats it by about 0.3%. **This is a real structural parallel to
`asymmetric-methods.md` §4's finding** (symmetric wheel/polyomino skeletons are beaten
by asymmetric ones at the open n) — both are instances of "the most symmetric candidate
for an area/surface-minimization-under-constraint problem is not optimal." But this is
an **analogy at the level of phenomenon**, not a technical connection: no shared
theorem, no cross-dimensional reduction was found linking planar fence
arrangements to 3D foam partitioning specifically (they are different optimization
problems — surface-area-minimizing partition of 3-space vs. area-maximizing planar
arrangement under a per-cell cap). Reported as a suggestive parallel worth keeping in
mind, not a result to build on.

## 8. Summary

| # | Question | Verdict |
|---|---|---|
| KKT junction conditions | DERIVED (§1.1): fence tension along each edge, face pressure normal to local boundary chord, T-junction reaction normal-only at the foot **and** split between the host's two endpoints (beam-contact, not pin-joint) |
| Force balance at n=11 split-hub | VERIFIED — closes, residual 1.3e-8, correct KKT signs (all tensions, all active pressures positive) |
| Force balance at n=11 point-hub | VERIFIED — closes, residual 5.8e-8, same sign pattern |
| Force balance at n=12 grid | VERIFIED — closes under the symmetric ansatz, residual 4.4e-9; genuine 4-dim self-stress redundancy present (not a bug — confirmed via singular-value gap) |
| 120 degree rule | DERIVED — does not survive; length-multiplier freedom washes out any angle condition at a generic junction. What replaces it is a linear sign/existence condition on multipliers (self-stress), not a geometric law. Clean vacuous result, as anticipated. |
| Does the force network prune skeletons pre-coordinate-solve? | Mostly NO (§4) — active-face set isn't combinatorial data, so no clean pre-solve filter was found. One real, weaker signal: symmetric skeletons show self-stress redundancy, asymmetric ones don't, corroborating (not proving) the existing symmetric-is-sparse argument. Does not fix the crate's actual `random_growth` failure. |
| Maxwell-Cremona / reciprocal diagrams as a generator | NO — the lift itself doesn't close for this problem's tension+pressure mix (§5.2, genuine negative, not attempted-and-hidden). No generator follows. |
| Literature counterpart to this problem's specific constraints (unit length, T-junction, area cap) | NOT FOUND (§5.4) — reported as a gap |
| 3D-lift / slice framing, generally | Same theorem as Maxwell-Cremona (§7); does not close; no recognizable solid produced; explicit null result, not manufactured |
| Self-stress count vs. rigidity/moduli count | DERIVED + VERIFIED on 3 cases (§6): qualitative Maxwell duality holds (asymmetric = isostatic on both sides, symmetric = redundant on both sides); general counting formula for this problem's non-classical constraint mix not derived |
| Kelvin/Weaire-Phelan | Analogy only, no technical link found (§7.5) |
