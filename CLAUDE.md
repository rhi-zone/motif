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

## Core Rules

**Note things down immediately — no deferral:**
- Problems, tech debt, issues → TODO.md now, in the same response
- Design decisions, key insights → docs/ or CLAUDE.md
- Future/deferred scope → TODO.md **before** writing any code, not after
- **Every observed problem → TODO.md. No exceptions.** Code comments and conversation mentions are not tracked items. If you write a TODO comment in source, the next action is to open TODO.md and write the entry.

**Conversation is not memory.** Anything said in chat evaporates at session end. If it implies future behavior change, write it to CLAUDE.md or a memory file immediately — or it will not happen.

**Warning — these phrases mean something needs to be written down right now:**
- "I won't do X again" / "I'll remember to..." / "I've learned that..."
- "Next time I'll..." / "From now on I'll..."
- Any acknowledgement of a recurring error without a corresponding CLAUDE.md or memory edit

**Triggers:** User corrects you, 2+ failed attempts, "aha" moment, framework quirk discovered → document before proceeding.

**When the user corrects you:** Ask what rule would have prevented this, and write it before proceeding. **"The rule exists, I just didn't follow it" is never the diagnosis** — a rule that doesn't prevent the failure it describes is incomplete; fix the rule, not your behavior.

**Corrections are documentation lag, not model failure.** When the same mistake recurs, the fix is writing the invariant down — not repeating the correction. Every correction that doesn't produce a CLAUDE.md edit will happen again. Exception: during active design, corrections are the work itself — don't prematurely document a design that hasn't settled yet.

**Something unexpected is a signal, not noise.** Surprising output, anomalous numbers, files containing what they shouldn't — stop and ask why before continuing. Don't accept anomalies and move on.

**Do the work properly.** Don't leave workarounds or hacks undocumented. When asked to analyze X, actually read X — don't synthesize from conversation.

## Design Principles

**Unify, don't multiply.** One interface for multiple cases > separate interfaces. Plugin systems > hardcoded switches.

**Simplicity over cleverness.** HashMap > inventory crate. OnceLock > lazy_static. Functions > traits until you need the trait. Use ecosystem tooling over hand-rolling.

**Explicit over implicit.** Log when skipping. Show what's at stake before refusing.

**Separate niche from shared.** Don't bloat shared config with feature-specific data. Use separate files for specialized data.

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

## Context Management

**Use subagents to protect the main context window.** For broad exploration or mechanical multi-file work, delegate to an Explore or general-purpose subagent rather than running searches inline. The subagent returns a distilled summary; raw tool output stays out of the main context.

Rules of thumb:
- Research tasks (investigating a question, surveying patterns) → subagent; don't pollute main context with exploratory noise
- Searching >5 files or running >3 rounds of grep/read → use a subagent
- Codebase-wide analysis (architecture, patterns, cross-file survey) → always subagent
- Mechanical work across many files (applying the same change everywhere) → parallel subagents
- Single targeted lookup (one file, one symbol) → inline is fine

## Commit Convention

Use conventional commits: `type(scope): message`

Types:
- `feat` - New feature
- `fix` - Bug fix
- `refactor` - Code change that neither fixes a bug nor adds a feature
- `docs` - Documentation only
- `chore` - Maintenance (deps, CI, etc.)
- `test` - Adding or updating tests

Scope is optional but recommended for multi-crate repos.

**When a task is done and tests pass, commit immediately.** Do not wait to be asked.

## Negative Constraints

Do not:
- Announce actions ("I will now...") - just do them
- Leave work uncommitted - when tests pass, commit. Don't wait.
- Use interactive git commands (`git add -p`, `git add -i`, `git rebase -i`) — these block on stdin and hang in non-interactive shells; stage files by name instead
- Use path dependencies in Cargo.toml - causes clippy to stash changes across repos
- Use `--no-verify` - fix the issue or fix the hook
- Assume tools are missing - check if `nix develop` is available for the right environment
