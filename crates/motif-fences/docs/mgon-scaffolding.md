# The m-gon-plus-scaffolding family: investigation and status

Scope: a candidate infinite family for the fences problem — take a regular unit-side
m-gon boundary (m unit fences) and add the *minimal* interior unit-length scaffolding
needed to bring every field under the area <= 1 cap, giving `n = m + s(m)`. Motivated by
`Area(m) = (m/4) cot(pi/m)` matching the closed-form record areas at n=9 (m=6) and n=18
(m=9) exactly, and undershooting the n=21 record by a small margin at m=10.

This document reports what this session established: **the family is much weaker than
the initial closed-form coincidences suggested.** Only the m=6 anchor is a confirmed,
constructed match. The m=9 anchor's natural construction is *proven infeasible* (by a
parallel session's independent work, cited below) even though the area numbers match.
The m=10 (n=21) sharp prediction is unresolved by the numeric search run here — not
confirmed, not refuted. This is reported as a negative/inconclusive result rather than a
validated family, per repo convention (speculative content stays labeled as such).

All numeric work here used the crate's existing `skeleton::hub_polygon` generator +
`anneal.rs` SA optimizer + `Configuration::validate` (the same machinery as the n=11
split-hub record), invoked via ad hoc scratch example binaries that were run, read, and
deleted (not committed — see git history for this commit's diff, which is docs-only).

## 1. s(m): what floor of it is establishable

`s(m)` = minimum unit-length interior fences needed to bring a unit-side regular m-gon's
single field (area `Area(m) = (m/4) cot(pi/m)`) under the area <= 1 cap, if such a
subdivision using only unit-length fences (each endpoint incident to another fence) even
exists at all for the *undeformed* regular m-gon.

**Area(m) and circumradius R(m) = 1/(2 sin(pi/m)), m=3..12** (awk, `cos/sin` from libm):

| m | Area(m) | R(m) | note |
|---|---|---|---|
| 3 | 0.43301 | — | already <= 1, s=0 |
| 4 | 1.00000 | — | already <= 1, s=0 |
| 5 | 1.72048 | 0.8507 | needs subdivision; R<1 (spoke-to-centre would overshoot unit length) |
| 6 | 2.59808 | 1.0000 | **s(6)=3, exact, VERIFIED** (repo: `hexagon_with_spokes`, n=9 test) |
| 7 | 3.63391 | 1.1524 | R>1: no single vertex-to-centre spoke is unit length |
| 8 | 4.82843 | 1.3066 | ditto |
| 9 | 6.18182 | 1.4619 | ditto; hub construction PROVEN infeasible, see §3 |
| 10 | 7.69421 | 1.6180 (= golden ratio phi) | ditto; see §2 |
| 11 | 9.36564 | 1.7747 | not investigated |
| 12 | 11.19615 | 1.9319 | not investigated |

**The one clean structural fact (already in `docs/asymmetric-methods.md` §1.3, restated
here as the load-bearing constraint on `s(m)`):** `R(m) <= 1` only for `m <= 6`
(equality at m=6 exactly). For `m >= 7`, no fence from any boundary vertex can reach the
centroid at unit length — a point-hub wheel is geometrically impossible, full stop, not
just "not yet found." Any scaffold for `m >= 7` must be either (a) an inner sub-polygon
plus spokes landing on its edges (the `hub_polygon` family, one bounded coincidence
region instead of one point — §1.3's "hub backs off to a small polygon" reading), or (b)
a non-hub topology entirely (chains, per `asymmetric-methods.md` §2.1). Neither shape is
guaranteed to admit a *unit-length* realization for a given `(m, inner-size,
spoke-count)` choice — that existence question is exactly what §2-3 below test, and it
is not automatic (contra the parent brief's framing of the m=9 lower bound as merely
"the crux" — it is the crux, and this session confirms it can and does fail).

**Face-count lower bound (the "easy" bound, restated precisely):** each interior fence
whose both endpoints already lie on the existing structure (ordinary corner or
T-junction — the only two ways an endpoint can be valid) splits exactly one existing
face into two, by the standard planar-graph face count `F = E - V + 1` for a connected
arrangement. So reaching `F >= ceil(Area(m))` faces from the m-gon's single starting
face needs at least `ceil(Area(m)) - 1` interior fences. This bound is **weak** in
practice: m=9's `ceil(6.18182)-1 = 6`, but the only concretely attempted construction
(3+6=9 interior fences) both matches the record's fence count *and* still fails to
realize (§3) — i.e. the record's actual `s(9)`, whatever it is, is not pinned down by
this bound at all; the bound says "at least 6," the candidate construction used 9 and
didn't work at that count either. **No tighter general lower bound was derived this
session** — the reachability argument above (R(m)>1 for m>=7) rules out one specific
shape (point wheel) but does not translate into a quantitative bound on `s(m)` for the
surviving shapes (hub-polygon, chain). This is reported as genuinely open, not glossed
over: `s(m)` for `m != 6` has no established value in this document, only failed or
undershooting attempts (§2-3).

## 2. The n=21 deformed-decagon test (task: sharp falsifiable prediction)

**Claim under test:** maximizing area over unit-sided decagons subject to admitting a
valid unit-length interior scaffold lands exactly on 7.69139 (the record), since the
regular decagon's own area (7.69421) exceeds it by only 0.00282 — small enough to
plausibly be exactly the deformation cost.

**What was run:** `skeleton::hub_polygon(10, 4, spokes)` (10-gon boundary + unit
square inner hub + 7 spokes = 21 fences, matching the record image's description of a
small central square per `asymmetric-methods.md`'s existing note on `21.gif`), annealed
with full coordinate freedom (no symmetry ansatz imposed — the boundary is free to
deform away from regular, exactly what the "deformation" hypothesis requires):

- Random spoke-target assignment, 172 attempts x 300k SA iterations: best valid area
  **6.1998**.
- Four hand-chosen structured (roughly-even) 7-spoke distributions across the 10
  outer vertices / 4 inner edges, 10 seeds x 400k iterations each: best valid area
  **7.3319** (the "even-ish-shift" pattern: outer vertices 0,2,3,5,6,8,9 to inner
  edges 0,0,1,1,2,2,3), reproducible across 4 of 10 seeds to within 0.005.

**Result: UNRESOLVED, not confirmed, not refuted.** The best found this session
(7.3319) is 0.36 below the target 7.69139 — a gap roughly 130x the claimed deformation
slack (0.00282), so this is not "so close it's probably rounding," it's a real,
substantial shortfall. Two explanations remain open and this session cannot distinguish
them:
1. The search (both random and the 4 hand-picked structured patterns) simply hasn't
   found the right combinatorial spoke assignment yet — `asymmetric-methods.md` §1.3's
   own n=11 case needed a specific, non-obvious split-hub assignment (3 of 4 chords
   sharing a point, the 4th landing separately) to hit the record; a wrong assignment
   there also undershoots. 7 spokes over 10x4 choices is a large discrete space and
   ~470 total anneal attempts across all patterns tried here is not exhaustive.
2. The record's actual n=21 construction is not a `hub_polygon`-shaped skeleton at all
   (single inner polygon + spokes) but something else — e.g. a boundary+chain topology
   (`asymmetric-methods.md` §2.1), which this session did not test for m=10.

**Sanity check against the corrected bounds:** 7.3319 and 6.1998 are both far under the
generic upper bound `n / sqrt(pi) approx 0.5642n` (11.85 for n=21) and under the
`A*(21) = 8` bound from the strengthened `A(n) < A*(n)` conjecture (largest integer A
with `f(A) <= 21` is A=7, so `A*(21)=8`; both results are comfortably below 8). Neither
result is a new record or a bound violation — both are below the existing 7.69139
record, so nothing here is committable as a construction, only as a documented
negative/inconclusive search result.

## 3. n=9 and n=18 reproduction

**n=9 (m=6): CONFIRMED, already in the repo.** `hexagon_with_spokes(&[0,2,4])`,
`tests/records.rs::hexagon_with_spokes_n9`, area exactly `3*sqrt(3)/2` — this is the one
member of the family that is a real, verified, exact-match construction (circumradius
equals side length exactly at m=6, no deformation needed).

**n=18 (m=9): the natural construction is PROVEN infeasible, not merely unsolved.** A
parallel session working this crate in the same window (commit `ecfd886`,
"§n=18 — the hub_polygon(9,3,6-spoke) reading of 18.gif is infeasible, not just
unsolved") traced `18.gif` to exactly the `hub_polygon(9,3, six-spoke)` skeleton
(mirror-symmetric ansatz: 9-gon boundary forced regular since the record's area equals
the unique area-maximizing equilateral 9-gon's area, small triangular hub, 6 spokes from
6 of 9 boundary vertices) and showed analytically that the window where all spoke
T-junctions are geometrically realizable is disjoint from the window where both
remaining problem faces satisfy the area cap (both faces exceed it by 30-55% wherever
the skeleton is even realizable at all). This is a closed negative result for that
specific skeleton, not a search-budget artifact.

This session's own numeric search (independent, done before finding that commit)
corroborates it from the other direction: annealing the *same* skeleton with full
coordinate freedom (no mirror-symmetry ansatz imposed, i.e. strictly more freedom than
the proof's ansatz) converged, robustly across 19 of 20 seeds, to a valid but strictly
smaller area of **6.028-6.030** — well short of 6.18182. That is consistent with the
proof: the unconstrained annealer found the best it could do by deforming the boundary
away from regular and shrinking the hub triangle/spokes' footprint, landing on a smaller
area, not the record's. (A separate random spoke-assignment search, 200 attempts, did
worse still — best 5.62 — reinforcing that structure beats randomness here, matching the
general finding elsewhere in `asymmetric-methods.md`.)

**Conclusion for n=18:** the closed-form area *coincidence* (`9cot(pi/9)/4 = 6.18182`
matching the record) does not, by itself, mean the record is "a regular 9-gon plus a
hub" in the naive sense the parent brief's preliminary arithmetic assumed. That specific
realization is now ruled out. Whether *some* skeleton reproduces 6.18182 exactly remains
open and is squarely the other agent's live work — not duplicated here.

## 4. Asymptotics

**Leading order (informal, not independently verified against real construction data —
CONJECTURED):** as `m -> infinity`, a regular unit-side m-gon approaches a circle of
circumference m, so `Area(m) ~ m^2/(4*pi)` (checked numerically: m=40 gives exact
127.06 vs the approximation's 127.32). If interior scaffold cost scales the same way
the polyomino grid's does (`s(m) ~ 2*Area(m)`, the grid's asymptotic area-per-fence ->
1/2), then `n = m + s(m) ~ m + m^2/(2*pi)`, matching the parent brief's asymptotic guess
by direct substitution — this is arithmetic consistency with the guess, not new
evidence for it; §1's finding that even `m=9`'s minimal case fails outright for the
one concretely tried skeleton is a reason to distrust `s(m) ~ 2*Area(m)` as a *tight*
estimate (it may be a lower bound only, if unit-length reachability forces overhead
beyond grid density — see §1's reachability discussion).

**Subleading-order comparison against the polyomino bound (CONJECTURED, algebra only):**
comparing to Harary-Harborth's `f(A) = 2A + ceil(2*sqrt(A))` (proved minimal *among
polyomino skeletons only* — per the corrected brief, not proved optimal overall) at
matching area `A = m^2/(4*pi)`:

```
f(A) ~ 2A + 2*sqrt(A) = m^2/(2*pi) + m/sqrt(pi)
family n ~ m + m^2/(2*pi)
family n - f(A) ~ m - m/sqrt(pi) = m * (1 - 1/sqrt(pi)) ~ 0.436 * m
```

This is positive and grows linearly in m: under this (unverified) heuristic, the family
needs *strictly more* total fences than a polyomino of the same area, by a margin that
widens with m — i.e. same leading-order ratio (1/2) but a worse subleading term, so if
the heuristic holds the family is beaten by the grid at every sufficiently large m, not
just "non-dominant in the limit." This refines rather than merely confirms the parent
brief's point 4. It is consistent with (does not test or strengthen) the corrected
`A(n) < A*(n)` conjecture from the coordinator's message — this session produced no
construction anywhere near that bound to check it against.

**What this does NOT establish:** an actual crossover n where the family stops beating
the grid (the brief's ask in point 4's second half). That requires real `s(m)`
values for several m, which §1-2 show are not yet in hand beyond m=6. Not attempted
further this session given the time already spent chasing §2's unresolved search.

## 5. Bottom line

- Confirmed: m=6/n=9 exact match (pre-existing, unchanged).
- Refuted (for the specific natural construction; area coincidence itself unexplained):
  m=9/n=18's hub-polygon realization.
- Unresolved (search insufficient to confirm or refute): m=10/n=21's deformed-decagon
  hypothesis — best found this session (7.3319) falls substantially short of the target
  (7.69139), gap far larger than the claimed deformation slack.
- Not established: a general `s(m)` formula, a lower bound tighter than face-counting,
  or any crossover-n calculation against the grid family.
- The family, as originally framed ("regular m-gon plus minimal unit scaffold, closed
  form area matches"), does not hold up as a clean generative rule under this session's
  scrutiny. It survives only as one confirmed point (m=6) plus two genuinely open
  questions (m=9's real construction, m=10's deformation optimum) — this should be read
  as a negative/inconclusive result on the family as stated, not as a disproof of any
  individual open n's record.
