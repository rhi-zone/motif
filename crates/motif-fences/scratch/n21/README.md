# n=21 skeleton salvage (unfinished solve)

Salvaged from `/tmp/fences-verify-n21/` before session end. That directory is
volatile scratch and will not survive; this is the durable copy. Goal: let a
future session resume the n=21 valid-ceiling solve without re-tracing
`21.gif` from scratch.

## Topology status: CONFIRMED faithful to 21.gif

All 21 fences measured against the record image; 15 branch clusters matched.
Euler check: V=25, E=32, F=9 (8 bounded faces + outer). Skeleton shape:
decagon outer boundary + an irregular inner quad + 7 chords connecting
boundary T-junction points to quad T-junction points, cutting the annular
region between boundary and quad into 7 wedge faces (the quad itself is the
8th bounded face).

## Files

- `model.json` — the combinatorial model, dumped from the original
  `model.pkl` (numpy/scipy object graph → plain JSON):
  - `boundary_names` (10): decagon boundary vertices, in cyclic order.
  - `quad_names` (4): inner quad vertices, in cyclic order.
  - `tj_info`: for each T-junction point, `[hostA, hostB, chordPartner]` —
    it sits on segment `hostA-hostB` and is the far end of a unit chord
    whose near end is `chordPartner`.
  - `idx`: maps each *free* vertex name (boundary + quad vertices, 14 of
    them) to its index into the flat coordinate vector `x` (`x[2*idx[name]:2*idx[name]+2]`
    gives its `(x, y)`).
  - `tidx`: maps each T-junction name to the index of its scalar
    interpolation parameter `t` in `x` (point = `(1-t)*hostA + t*hostB`).
  - `NPT` = 14 free vertices. Full `x` has `2*14 + 11 = 39` scalars (14 free
    points × 2 coords, 11 T-junction `t` params) — matches
    `solution_validceil.json` / `solution_uncapped.json` shapes.
- `traced_coords.json` — the raw pixel-derived coordinates from tracing
  `21.gif` directly (named `C1..C12`, `J0..J13` — a different, purely
  descriptive naming from `model.json`'s `boundary_names`/`quad_names`, kept
  for cross-checking the trace). Not gauge-fixed or unit-scaled; this is the
  pixel-measurement ground truth, not solver output.
- `edge_labels.json`, `segments.json` — the 21 traced fence segments as
  point pairs, matching `traced_coords.json`.
- `solution_validceil.json` — best solution found under the cap (all faces
  ≤ 1): **area = 7.682823659**, feasible, `x` is the full 39-scalar vector
  in `model.json`'s indexing.
- `solution_uncapped.json` — best solution found with the cap removed:
  **area = 7.694208843** (exceeds the published record 7.69139), with
  `max_face = 1.1067` — i.e. it needs one field ~10.7% over the unit cap to
  get there. (Contrast with n=13's `grid_wedge_n13`, which needs ~70%
  oversizing to reach its record — see `docs/asymmetric-methods.md` §8.3 and
  its corrective note.)
- `valid_ceiling_log.txt` — full console output of the capped + uncapped
  multistart runs that produced the two solutions above (40 capped trials,
  30 uncapped trials, both plateaued).
- `solve4.py`, `valid_ceiling.py` — the original Python (scipy
  `trust-constr`) solve scripts, lightly edited to load `model.json` /
  `solution_validceil.json` instead of the original `model.pkl` /
  `solution2.npy` (which were not salvaged verbatim — only the final
  solutions were). Run via the project's throwaway python env, e.g.:
  `nix shell --impure --expr 'with import <nixpkgs> {}; python3.withPackages (ps: with ps; [numpy scipy])' -c python3 valid_ceiling.py`
  from this directory. Not wired into `cargo test`; these are scratch
  reproduction aids, not part of the crate's Rust API.

## What's actually unfinished

The numeric solve above (capped 7.682823659, uncapped 7.694208843) already
happened — the numbers matching the partial-best cited in `TODO.md` come
from `valid_ceiling_log.txt`. What's *not* done:

1. These results aren't written up anywhere durable/citable (this file is
   the first time they're committed) — no doc section, no Rust test
   (`Skeleton`/`Configuration`-based, like `grid_wedge_n13` in
   `tests/records.rs`) encoding the n=21 skeleton and asserting the area.
2. The capped solve used only local warm-started multistart from one
   solution (`x0`), not the broader symmetric+asymmetric multistart
   approach used for n=13 in §8.3 — so 7.682823659 is a strong candidate
   ceiling, not a certified one. Worth more restarts from independent
   starting points before calling it final.
3. No cap-sweep (§8.2-style, `cap = 1+ε` for small ε) has been run to see
   how much of the `7.69139 - 7.682823 = 0.008567` gap is cap-adjacent vs.
   hard topological ceiling, the way n=13's gap was decomposed.

See `crates/motif-fences/TODO.md` item 2 for the full open-item writeup.
