# n=13 pixel-measurement provenance

Salvaged from `/tmp/fences-verify-n13-v3/` before session end. The
topology and final coordinates this measurement produced are already
committed as the `grid_wedge_n13` test in `tests/records.rs` — these two
files are the underlying pixel-measurement work that test's coordinates
were derived from, kept for audit/re-derivation purposes.

- `pixel_line_intersections.py` — fits straight lines to traced pixel
  segments of `13.gif` and intersects them to recover vertex pixel
  coordinates (`TL`, `TM`, `TR`, `U`, `Tip`, `D`, `BR`, `BM`, `BL`, `LM`,
  `RM`, `C`).
- `pixel_fit_solve.py` — takes those pixel coordinates (via a fixed
  `unit_px` scale factor), sets up the same edge-length + collinearity
  constraint system as `grid_wedge_n13`, and refines to a valid unit-fence
  configuration. This is the measurement pass that confirmed the topology
  now documented in `tests/records.rs`'s `grid_wedge_n13` doc comment and
  in `docs/asymmetric-methods.md` §8.3's corrective note (both halves
  measured edge-by-edge; TM/BM/LM are true 3-way vertices; C is a genuine
  4-way point; the right cluster's U-D chord T-junctions on both TR-Tip/
  Tip-BR and RM).

Not wired into `cargo test` — reference/provenance only.
