# motif-fences: open threads

Durable handoff doc for the fences (Erich Friedman "fences" packing problem)
sidequest. Each item below should be pickup-able cold — no dependency on a
previous session's context beyond what's linked.

## 1. Correction needed: commit `d4aafa5` and §8.2/§8.3 of `docs/asymmetric-methods.md` state a stale, overturned conclusion

**Status: partially done.** A corrective note (§8.4) has already been added
to `docs/asymmetric-methods.md`, right after §8.3 — see that file. This item
just tracks the remaining bookkeeping.

**What was wrong:** commit `d4aafa5`'s message, and §8.2/§8.3 of
`docs/asymmetric-methods.md`, conclude that the published n=13 record
(Bram Cohen, 4.07361) uses "a genuinely different skeleton" than
`grid_wedge_n13` (`tests/records.rs`), because 13.gif's right-side cluster
was believed mistraced. That mistrace finding was itself later overturned by
a more careful pixel measurement pass (both halves of 13.gif measured
edge-by-edge; raw measurement scripts salvaged to
`crates/motif-fences/scratch/n13/`).

**Corrected conclusion (evidence-backed, now in §8.4):** `grid_wedge_n13` IS
topologically faithful to 13.gif — TL-TM/TM-TR/BR-BM/BM-BL/BL-LM/LM-TL are
unit fences, TM/BM/LM are true 3-way vertices, C is a genuine 4-way point,
and the right cluster (TR-Tip/Tip-BR unit fences, U-D chord T-junctioning on
both + RM T-junctioning on U-D) matches exactly. Given that faithful
topology, its valid ceiling (all fields ≤ 1, any coordinates) is
**4.0645952819**, below the published **4.07361**. The topology only reaches
the record by oversizing one pentagon to ~1.715 (a ~70% cap violation).
**Cohen's n=13 figure cannot validly enclose its own published area — the
figure↔number pair is inconsistent under the problem's rules.**

**What's still open:**
- `d4aafa5`'s commit message itself is not rewritten (per repo convention —
  no history rewriting). A future correction commit's message should link
  back to this item and to §8.4, so `git log` tells the honest story even
  though the old message still reads the superseded way.
- Whether this is a one-off or a pattern is exactly what item 2 (n=21) is
  for.

## 2. n=21 valid-ceiling solve — UNFINISHED, the key open item

n=21's skeleton (decagon boundary + irregular inner quad + 7 chords) is
confirmed topologically faithful to 21.gif: all 21 fences measured, 15
branch clusters matched, Euler check V=25 E=32 F=9. Full topology + a
partial numeric solve salvaged to `crates/motif-fences/scratch/n21/` (see
its `README.md`).

**What's already done** (found in `scratch/n21/valid_ceiling_log.txt`):
- Capped (all fields ≤ 1) multistart solve: best = **7.682823659**, short of
  the published record **7.69139** by 0.008567.
- Uncapped multistart solve: best = **7.694208843** (exceeds the record),
  needing one field at **1.1067** (~10.7% over cap) to get there.

**What's NOT done:**
- No write-up: these numbers exist only in scratch files as of this commit,
  not in `docs/asymmetric-methods.md` or as a `Skeleton`/`Configuration`-
  based Rust test (the way `grid_wedge_n13` encodes n=13 in
  `tests/records.rs`).
- The capped solve was only warm-started multistart from one prior solution,
  not the broader symmetric+asymmetric sweep §8.3 used for n=13 — so
  7.682823659 is a strong candidate ceiling, not a certified one.
- No cap-sweep (§8.2-style, `cap = 1+ε` for small ε) has decomposed the
  0.008567 gap into "cap-related" vs. "hard topological ceiling" the way
  n=13's 0.009015 gap was split 43%/57%.

**Why this is the key open item:** n=21 needing only ~10.7% oversizing
(vs. n=13's ~70%) to reach its record is a much smaller violation — worth
checking carefully whether it's still a real violation (i.e. still below the
record when capped) before concluding anything. If n=21's faithful figure
*also* can't validly hold its published number, that's two independent
Cohen records demonstrably inconsistent — a pattern, not a one-off. If
tightening the capped multistart pushes 7.682823659 up to meet 7.69139
(unlikely given how flat the trials plateaued, but not yet ruled out), the
conclusion is the opposite: n=21 is fine and n=13 was the anomaly.

## 3. n=7 → 2.0 within-model optimality

The enumerator found n=7 combinatorially exhaustive: 81 distinct topologies,
all annealed, max area ≈ 2.0. There's a clean face-count argument this is
optimal within the single-simple-boundary model: k=6 boundary fences + 1
interior fence = exactly 2 bounded faces, each capped at area ≤ 1, so total
≤ 2 — achieved.

**Open:** write this argument up explicitly (it's currently only implicit in
the enumeration results) and commit it as a stated theorem/verification,
analogous to how `docs/upper-bounds.md` documents the isoperimetric bound.
This would be the first *optimality* result beyond n=3/n=4 (those come from
the boundary bound A(n) ≤ (n/4)cot(π/n), tight there but not elsewhere).

## 4. Untried records: n=14, 16, 19, 23

Never seriously attempted (no trace-and-solve pass). n=13 and n=21 are the
only open Cohen records that have been investigated so far (see items 1-2).
Note: `interior_enumerate.rs` / `boundary_subdivision.rs` (the exhaustive
enumerator used for n=7 in item 3, and n=8) cannot exhaust these — n=8 alone
already has 8469 distinct topologies, and n≥13 is astronomically larger.
These would need the trace-from-image + skeleton + solve workflow used for
n=13/n=21, not enumeration.

## 5. Open conjecture: polyomino ceiling A(n) < A*(n)

Where `A*(n) = min{A : f(A) > n}`, `f(A) = 2A + ⌈2√A⌉`. Holds on all 22
table entries checked so far; unproven. Combined with the
(proven-for-trivial-steps) monotonicity of A(n), this would sandwich A(n) to
a width-one-integer window. Note the isoperimetric method
(`docs/upper-bounds.md`) provably *cannot* reach this bound on its own — its
leading constant tops out at 1/√π ≈ 0.5642, short of what's needed.

## 6. Tooling blocker for optimality proofs

The nix flake currently provides only rust + bun. Missing:
- **Julia + HomotopyContinuation.jl** — needed for per-topology
  global-optimization certificates (current annealing/SLSQP solves are
  heuristic upper bounds, not proofs of optimality).
- **Z3 / dReal / CAD** (cylindrical algebraic decomposition) — same need,
  different route.

Without these: n=8's 8469 enumerated topologies could in principle give a
within-model optimality result if *all* were annealed to convergence (large
compute, and still only heuristic without a certificate). n=8's exact area
is already a known root of a committed irreducible degree-24 polynomial
(see commit `d14a051` and the relevant `docs/` section); whether that root
is expressible in radicals is open — no Galois-group tool for degree > 6 is
available in-repo or in the flake.
