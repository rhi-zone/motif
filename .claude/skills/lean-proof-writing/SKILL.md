---
name: lean-proof-writing
description: Workflow guardrails for writing Lean 4 / Mathlib proofs in this repo (langlands/). Use whenever editing .lean files under langlands/, adding lemmas/tactics, or diagnosing a lake build failure. Encodes lemma-lookup-before-use, exact?/apply?-before-hand-guessing, and stop-on-repeated-error rules distilled from transcript analysis of past sessions.
---

# Lean proof writing (langlands/)

Four rules, each answering a concrete way past sessions burned build cycles.

## 1. Verify a lemma name exists before writing it

Never type a Mathlib identifier from memory and send it straight to `lake build`. Hallucinated names (e.g. `LocalField.compactSpace_absoluteGaloisGroup`, `Subgroup.eq_top_iff'.mpr`, `AdicValuation.valuedAdicCompletion_eq_valuation'`, `valued_coe`) look plausible and only surface as failures after a full build.

Lookup order:

1. **loogle first** — semantic/type-signature search, not string match. Confirmed reachable in this environment:
   ```
   curl -s -G "https://loogle.lean-lang.org/json" --data-urlencode "q=<pattern>"
   ```
   e.g. `q="Nat.succ_le_succ"` or a type-shaped query like `q="?a + 1 = 1 + ?a"`. Returns JSON with real declaration names — trust what it returns, not what it doesn't (empty result means keep searching, not "assume the name exists anyway").
   - `LeanSearchClient` is already a transitive dependency of this project (pulled in via mathlib, present in `.lake/packages/LeanSearchClient`) and provides in-editor `#loogle "..."` / `#leansearch "..."` commands usable directly inside a `.lean` file as command, term, or tactic. Prefer the `curl` form when working headless (no editor round-trip needed to read the result).
2. **grep fallback** — only if loogle is unreachable (curl fails/times out): `grep -rn '<identifier or partial name>' langlands/.lake/packages/mathlib`. This is a string match, not a type match — weaker, use only as fallback.

Do this *before* writing the lemma name into the proof, not after the compiler rejects it. A session grepping 11-18 times against 6 builds is the target ratio; grepping only after rejection is the failure pattern.

## 2. Try Lean's own lemma search tactics before hand-picking

Before manually assembling a proof term or guessing a lemma chain, try:
- `exact?` — closes the goal outright if a single matching lemma exists
- `apply?` — suggests lemmas that make progress on the goal head
- `rw [?]` / `simp?` where rewriting is the shape of the goal

None of these were used across the 44 analyzed sessions — every proof was closed by hand-guess + build-and-see. They're cheap (one tactic line, one build) relative to a wrong hand-written term.

## 3. Two identical errors in a row is a mandatory stop-and-diagnose signal

If the same error (same message shape, even if line/col shifts) recurs on consecutive builds, stop retrying nearby tactic variants. Instead:
- Read the goal state Lean already printed in the error output — it's usually sufficient to see why the tactic doesn't apply.
- For `failed to synthesize instance ...` errors specifically, run with `set_option trace.Meta.synthInstance true` to see the resolution search rather than guessing at instance arguments.
- Only after actually reading the diagnosis, make the next edit.

Retrying 3-9 times on a variant of the same failing tactic without reading the printed goal state is the failure pattern this replaces.

## 4. Don't edit forward while a flagged error is still open

Before touching a different line/section of the file, re-check that the previously-reported error (same line:col) is actually resolved in the next build's output. If it's still there, that error is still the active problem — fix it before making unrelated edits elsewhere, even if another part of the file also needs work. Compounding edits across an unresolved error multiplies wasted build cycles and makes it harder to tell which edit fixed (or didn't fix) which error.
