# CLAUDE.md

Behavioral rules for Claude Code in the motif repository.

## Project Overview

Structural exploration of mathematics

Part of the [rhi ecosystem](https://rhi.zone).

## Architecture

Rust types (Signature, Theory, Axiom, Translation) compile to egglog DSL programs via `.to_egglog()` methods. egglog handles equality saturation.

- `crates/motif/src/signature.rs` — `Op`, `Signature` (universal algebra operations + arities)
- `crates/motif/src/theory.rs` — `Axiom`, `Theory`, `SaturationConfig` (egglog integration)
- `crates/motif/src/theories/` — Concrete theories (group, ring)
- `crates/motif/src/translate.rs` — `Translation` (s-expression symbol renaming between theories)

**egglog caveats:**
- Reserved primitive names (cannot be used as constructors): f64 `neg`, `abs`, `min`, `max`, `to-f64`, `to-i64`, `to-string`; i64 `not-i64`, `log2`, `count-matches`; bool `not`, `and`, `or`, `xor`. Use `negate` for algebraic negation.
- Rewrite safety: all RHS variables must appear in LHS; bare variables on LHS cause `Ungrounded`; unbound RHS variables cause `Unbound`.
- Bidirectional rewrites only safe when both sides are constructor expressions with the same free variables. Identity laws (`f(x) = x`) and inverse laws are forward-only — reverse creates unbounded terms. Associativity is safe bidirectional.
- Seed nullary constructors: constants like `(zero)`, `(one)` must be added explicitly via `(let seed_X__ (X))` or axioms referencing them won't fire.
- Use `(ruleset name)` before any `(rule/rewrite ... :ruleset name)`; drive with `(run-schedule (repeat N (run ruleset)))`.
- iter_limit 5–10 is usually enough; 20+ with bidirectional rewrites + distributivity → blowup.

**Saturation incompleteness:** `Theory::equiv()` only proves equalities whose intermediate terms exist in the e-graph. Cross-theory comparisons must use enumeration-based checking (`discover_equiv_classes` in `explore.rs`) on both sides — `equiv()` produces false negatives (e.g. group vs abelian group). Expression count at depth 2 with 2+ vars can be 255+; prefer 1 var or depth 1.

**Discover module:** per-axiom decomposition keeps candidate products small; results joined via partial-assignment merging. Do NOT put many expressions in one e-graph with ring axioms (distributivity blows up) — use one e-graph per check (2 exprs each).

## Development

```bash
nix develop        # Enter dev shell
cargo test         # Run tests
cargo clippy       # Lint
cd docs && bun dev # Local docs
```

If a tool appears missing, you are outside `nix develop`. Do not assume the tool is unavailable to the project.

## Workflow

**Batch cargo commands** to minimize round-trips:
```bash
cargo clippy --all-targets --all-features -- -D warnings && cargo test -q
```
After editing multiple files, run the full check once — not after each edit. Formatting is handled automatically by the pre-commit hook (`cargo fmt`).

**Prefer `cargo test -q`** over `cargo test` — quiet mode only prints failures, significantly reducing output noise and context usage.

**When making the same change across multiple crates**, edit all files first, then build once.

**Minimize file churn.** When editing a file, read it once, plan all changes, and apply them in one pass. Avoid read-edit-build-fail-read-fix cycles by thinking through the complete change before starting.

**`normalize view` is available** for structural outlines of files and directories:
```bash
~/git/rhizone/normalize/target/debug/normalize view <file>    # outline with line numbers
~/git/rhizone/normalize/target/debug/normalize view <dir>     # directory structure
```

## Commit Convention

Use conventional commits: `type(scope): message`

Types: `feat`, `fix`, `refactor`, `docs`, `chore`, `test`. Scope is optional but recommended for multi-crate repos.

<!-- BEGIN ECOSYSTEM RULES -->

## Delegation

The main session is an orchestrator. Allowed actions: `Agent`/`Task*`/`AskUserQuestion`/plan-mode/`ScheduleWakeup`, and Bash limited to `git commit`, `git push`, `git status`, `git log --oneline`. Everything else delegates to a subagent. The hook is evidence of a prompting failure, not a behavioral guide. If a tool call hits the hook AT ALL, the prompt failed to prevent it. Delegate before the decision point, not after.

### Triggers

Before calling Read, Grep, Glob, or any Bash beyond the four git commands — stop. Dispatch an Agent instead.

Before editing any file — stop. Dispatch an Agent. This includes plan files in `~/.claude/plans/`: in plan mode, dispatch a subagent to write to the plan file; do not Write it yourself. The plan file's content must not enter main context.

When you need git context beyond status/log-oneline (a diff, a blame, a show) — dispatch an Agent.

When a tool call is denied by the hook — do not retry, do not narrate. Dispatch the equivalent Agent and continue.

When a code-modifying subagent returns — `git status`, then `git commit` before any user-facing reply.

Before dispatching an Agent that modifies code — scan your prompt for "do not commit" or "based on your findings". Delete them.

Before dispatching: if your prompt says "if you find", "based on your findings", or "as appropriate" — stop. Investigate first; dispatch with the decision made.

When you can't verify something — do not speculate or guess at file locations, names, or contents. Dispatch a Read subagent or ask. Confabulation is failure.

### Model Tiers

- Sonnet — exploration, lookup, mechanical multi-file edits, implementation, default.
- Opus — architectural judgment, design, subagents that themselves spawn subagents.

Always set `subagent_type` and `model` explicitly.

### Prompt Rules

- Never tell a subagent "do not commit." Code-modifying subagents commit their own work.
- Don't ask for a diff summary. After a code-modifying subagent, `git status` in main and dispatch a review Agent if you need to see the diff.
- Don't re-explain CLAUDE.md. Subagents inherit it.
- Cite locations by content ("the block that does X"), not line numbers — files shift between reads.
- Name files explicitly; don't outsource the grep.
- Match agent type to deliverable: `Explore` for lookup/search, `general-purpose` for reports and file-modifying work.
- On unsatisfying output, change something before retrying. Same prompt + same tier = same result.
- Dispatch independent subagents in parallel (multiple Agent blocks in one message).
- Pair `isolation: worktree` with `run_in_background: true`.
- Code-modifying subagents must verify their own changes before returning (re-read the diff, run tests, etc.). The orchestrator does not get a second pass with git diff — that's hook-blocked.

## Hard Constraints

- No Edit/Write/NotebookEdit in main. Plan files in `~/.claude/plans/` are written by subagents, not by main.
- No Read/Grep/Glob/NotebookRead in main. Delegate.
- No Bash in main beyond `git commit`, `git push`, `git status`, `git log --oneline`.
- No `--no-verify`. Fix the issue or fix the hook.
- No path dependencies in `Cargo.toml` — they couple repos and break independent publishing.
- No interactive git (no `git rebase -i`, no `git add -i`, no `--no-edit` on rebase).
- No suggesting project names. LLMs are bad at this; refine the conceptual space only.
- No tracking cross-project issues in conversation — they go in TODO.md in the affected repo.
- No ecosystem changes without checking all affected repos.
- No assuming a tool is missing without checking `nix develop`.
- Commit completed work in the same turn it finishes. Uncommitted work is lost work.

## Meta

- Something unexpected is a signal. Stop and find out why. Do not accept the anomaly and proceed.
- Corrections from the user are conversation, not material for new rules. Rules are added when a failure mode is observed repeatedly.

<!-- END ECOSYSTEM RULES -->
