# Prior Art: Kernel IRs for Mathematics

Survey of existing proof assistant kernels, what's structurally necessary vs.
ergonomic, and what this means for motif.

## Kernel Comparison

### Lean 4 (CIC variant)

**Minimal kernel** (Lean4Lean, formally verified): 6 constructors.

```
bvar   -- bound variable (de Bruijn index)
sort   -- Sort u (universes)
const  -- named constant + universe instantiation
app    -- application (curried)
lam    -- lambda abstraction
forallE -- dependent function type (Pi)
```

Additional kernel constructors (representable in terms of the above, but kept
for efficiency): `letE`, `lit`, `proj`, `fvar`, `mvar`, `mdata`.

**Structural choices:**
- Predicative `Type u` hierarchy + impredicative `Prop` (via `imax`)
- Recursors generated per inductive type (no `Fix` in kernel)
- `Quot` as kernel primitive with computational reduction rule
- Definitional proof irrelevance in `Prop`
- Cumulativity
- Eta for functions + structural eta for single-constructor types

**Universe levels:**
```
zero | succ l | max l1 l2 | imax l1 l2 | param name
```
`imax` is the impredicativity trick: `imax l1 0 = 0`, otherwise `max l1 l2`.

**Reduction rules:** beta, delta (unfold), zeta (let), iota (recursor on
constructor), eta, structural eta, proof irrelevance, quotient reduction,
nat/string literal unfolding, projection reduction.

**Axioms:** `propext` (propositional extensionality), `Quot.sound`,
`Classical.choice`. `funext` is derived from `Quot.sound`.

### Coq (pCIC)

**Kernel term constructors** (~16):
`Rel`, `Var`, `Sort`, `Prod`, `Lambda`, `LetIn`, `App`, `Const`, `Ind`,
`Construct`, `Case`, `Fix`, `CoFix`, `Proj`, `Int`, `Float`, `Array`.

(`Meta`, `Evar`, `Cast` exist in the term type but are elaboration artifacts.)

**Key structural differences from Lean:**
- `Fix` and `CoFix` are kernel primitives (Lean uses recursors instead)
- `Case` is a kernel primitive (flat pattern match, one level)
- Syntactic guard checker for termination (Lean elaborates via well-founded
  recursion)
- No computational quotients (axiomatic)
- `SProp` for definitional proof irrelevance (added later; regular `Prop` is
  irrelevant only at extraction)
- Separate `Set` sort (optionally impredicative)
- Universe constraint graph (algebraic expressions with `max`, `+1`)
- Full cumulative universe hierarchy with variance annotations for inductives

**Reduction rules:** beta, delta, iota (Case on constructor), zeta (let), eta,
fix (unfold when recursive arg is constructor), cofix (unfold when scrutinee of
Case), primitive (Int/Float/Array ops), projection.

### Agda (Predicative MLTT)

**Foundation:** Predicative intensional Martin-Lof Type Theory + induction-
recursion. No fixed specification — the type checker IS the specification.

**Core term constructors:**
`Var`, `Lam`, `Lit`, `Def`, `Con`, `Pi`, `Sort`, `Level`, `MetaV`.

Elimination is via `Elim = Apply Arg | Proj QName` (application or projection).

**Key structural differences:**
- **Pattern matching is primitive** — case trees are the internal
  representation, NOT compiled to eliminators. This is the biggest divergence
  from Lean/Coq.
- **No separate trusted kernel.** The entire type checker (~large Haskell
  codebase) is the TCB. No de Bruijn criterion (elaboration doesn't produce
  terms that a small kernel re-checks).
- **No cumulativity** — `Set 0 : Set 1` but NOT `Set 0 : Set 2`.
- **Predicative `Prop i`** (added Agda 2.6+) — not impredicative. Restricted
  elimination into `Set`.
- **Induction-recursion** supported natively (not in Lean/Coq).
- **Foetus-style termination** checker.

### Idris 2 (QTT)

**Foundation:** Quantitative Type Theory (Atkey 2018, McBride). Dependent type
theory where every binding carries a multiplicity from a semiring.

**Core term constructors:**
`Local`, `Ref`, `Meta`, `Bind`, `App`, `As`, `TDelayed`, `TDelay`, `TForce`,
`PrimVal`, `Erased`, `TType`.

**Binder types** carry `RigCount`:
`Lam`, `Let`, `Pi`, `PVar`, `PLet`, `PVTy` — each annotated with {0, 1, omega}.

**The multiplicity semiring {0, 1, omega}:**
- `0` — erased at runtime (type-level only). Replaces Prop.
- `1` — linear, used exactly once. Enables session types, safe resources.
- `omega` — unrestricted (default).

**Key structural differences:**
- **Every binding is annotated with a quantity.** The judgment form is
  fundamentally different: `rho_1 x_1 : A_1, ..., rho_n x_n : A_n |- t : B`.
- **No `Prop`.** Erasure handled by 0-multiplicity.
- **Native linearity** via 1-multiplicity.
- **Laziness is primitive** — `TDelayed`, `TDelay`, `TForce` in kernel.
- **Type formation uses 0** — variables in types don't count toward runtime
  usage.

### ATS (Applied Type System)

**Foundation:** Completely separates statics from dynamics. Programs cannot
appear in types. This is architecturally opposite to PTS/CIC.

**Two languages:**

```
STATICS (compile-time):
  Sorts: bool, int, char, addr, type, t@ype, prop, view, viewtype, viewt@ype
  Simply-typed lambda calculus over sorts.
  Types are static terms of sort `type`.

DYNAMICS (runtime):
  Call-by-value lambda calculus.
  lam, app, fix (general recursion), let, case.
  Proof terms (erased after checking).
```

**Key structural differences:**
- **Types and programs are separate languages.** Dependent types are restricted
  to static index terms (integers, booleans, addresses), not arbitrary programs.
  DML-style.
- **General recursion** allowed in programs. Only proof functions must terminate.
- **Native linear types** via view/viewtype sorts.
- **No universe hierarchy.** Sorts are flat.
- **Proofs fully erased** after type checking. Zero runtime cost.
- **Manual memory management** with type-safe correctness proofs.

## What's Structurally Universal

Every kernel has:

| Primitive | Description |
|---|---|
| Binding | Lambda / Pi (dependent function type) |
| Application | `f a` |
| Variables | De Bruijn indices |
| Sorts | Some universe structure |
| Constants | References to global definitions |
| Inductive definitions | Constructors + elimination |
| Conversion/equality | Some notion of definitional equality + reduction |

## What's Ergonomic (Drop Immediately)

All of this compiles away before any kernel sees it:

- Tactics, tactic frameworks, proof scripts
- Implicit argument resolution / unification
- Notation, macros, syntax sugar
- Pattern matching compilation (human-readable → eliminators)
- Type class / instance search
- Coercions (inserted as explicit applications)
- `do`-notation, `where` clauses, sections
- Named variables (kernel uses de Bruijn)
- `BinderInfo` markers (implicit/explicit — cosmetic)
- Error messages, source locations
- Universe inference

## Where Kernels Genuinely Disagree

These are structural forks, not ergonomic differences:

| Decision | Options | Who chose what |
|---|---|---|
| **Dependent types** | Full DTT vs. simple type theory vs. restricted (index-only) vs. none | Lean/Coq/Agda/Idris: full DTT. HOL: STT. ATS: index-only. Dafny: none. |
| **Proof objects** | Terms (checkable) vs. abstract type (LCF) vs. none (SMT decision) | Lean/Coq/Agda/Idris: terms. HOL: abstract thm. Dafny: none. |
| **Elimination** | Recursors vs. `Fix`+`Case` vs. case trees vs. definitional extension | Lean: recursors. Coq: Fix+Case. Agda: case trees. HOL: encoded. |
| **Termination** | WF recursion vs. guard checking vs. Foetus vs. SMT decreases vs. optional | Lean: WF. Coq: guard. Agda: Foetus. Dafny: SMT. ATS: proofs only. |
| **Linearity** | None vs. multiplicity semiring vs. linear sorts | Lean/Coq/Agda/HOL/Dafny: none. Idris: QTT. ATS: view/viewtype. |
| **Quotients** | Kernel primitive (computational) vs. axiom vs. N/A | Lean: primitive. Coq: axiom. Others: N/A. |
| **Proof irrelevance** | Definitional vs. extraction-only vs. 0-multiplicity vs. full erasure vs. N/A | Lean: definitional. Coq: extraction. Idris: 0-mult. ATS: erased. HOL/Dafny: N/A. |
| **Universes** | Cumulative hierarchy vs. non-cumulative vs. flat vs. none | Lean/Coq: cumulative. Agda: non-cumulative. ATS: flat. HOL/Dafny: none. |
| **Statics/dynamics** | Unified vs. separated vs. spec+code | DTT systems: unified. ATS: separated. Dafny: spec+code. |
| **Verification method** | Type checking vs. SMT decision vs. LCF inference | DTT: type checking. Dafny: SMT. HOL: LCF. |
| **Trusted base** | Small kernel vs. whole checker vs. large toolchain | Lean/Coq/HOL: small kernel. Agda/Idris: whole checker. Dafny: large toolchain. |
| **Interchangeable foundations** | Fixed vs. framework | All except Isabelle: fixed. Isabelle: logical framework (hosts HOL, ZF, FOL, CTT). |

### Dafny (SMT-backed verification)

**Foundation:** Not type-theoretic. Verification via SMT solving (Dafny →
Boogie → Z3). No proof terms — verification is a decision procedure.

**Pipeline:**
```
Dafny source
  → Boogie IVL (intermediate verification language)
    → first-order verification conditions (logical formulas)
      → Z3 (SAT/UNSAT on negated VC)
```

**Boogie's core primitives** (the actual IR):
- `assert E` — emit proof obligation
- `assume E` — constrain execution path
- `havoc x` — nondeterministic assignment
- `requires`/`ensures`/`modifies` — pre/post/frame conditions

Everything reduces to sequences of `assert`, `assume`, and `havoc`. A loop with
invariant `I` becomes: `assert I; havoc modified; assume I; ... assert I`. A
procedure call becomes: `assert pre; havoc modifies; assume post`.

**What Z3 receives:** Multi-sorted first-order logic with theories:
- Uninterpreted functions (primary mechanism — Dafny functions become UF symbols
  constrained by axioms)
- Integer/real arithmetic (linear + nonlinear)
- Array theory (extensional)
- Datatype theory (constructors, discriminators)
- Heavy use of universally quantified axioms, instantiated via E-matching with
  triggers

**Termination:** Decreases clauses — lexicographic tuples checked via SMT
arithmetic. Well-founded orderings predefined per type.

**Induction:** Syntactic heuristic. For a lemma `L(args)`, Dafny auto-inserts
`forall args' | pre(args') && metric(args') < metric(args) { L(args'); }` —
invoking the lemma on all smaller arguments. Recursive function bodies unfolded
to controlled depth ("fuel").

**Key structural differences from type-theoretic systems:**

| Aspect | Dafny/SMT | Type-theoretic (Lean/Coq) |
|---|---|---|
| **Proof representation** | None. SAT/UNSAT decision. | Full proof terms (CIC). |
| **Trusted base** | Large: Dafny + Boogie + Z3. No checkable certificates. | Small kernel. Proof terms independently checkable. |
| **Automation** | Default. User adds hints when it fails. | Manual-first. Automation opt-in. |
| **Expressiveness** | First-order + theories. No higher-order properties. | Full dependent types. Higher-order. |
| **Compositionality** | Proofs don't compose as objects. | Proofs are terms. Compose via application. |
| **Failure mode** | Timeout / "assertion might not hold." Minimal diagnostics. | Type error with structured information. |

**Limitations:**
- No proof objects — entire toolchain must be trusted
- E-matching is heuristic — false negatives, matching loops
- Proof instability ("butterfly effect") — renaming a variable can break
  verification
- Nonlinear arithmetic is undecidable
- Cannot express dependent types natively
- Axiom consistency of Boogie prelude is unverified

**Why it matters for motif:** Represents a fundamentally different "bottom" —
first-order logic + SMT theories, decided by automated procedures rather than
constructed as proof terms. A seventh point in the interchangeable-backends
design space.

### HOL Family (Simple Type Theory)

Three major systems sharing a foundation: HOL Light, HOL4, Isabelle/HOL.

**Foundation:** Church's Simple Type Theory (STT) — polymorphic lambda calculus
WITHOUT dependent types. Types cannot mention terms.

**Type language:**
```
type variables: 'a, 'b, ...
base types:     bool, ind (infinite type)
type former:    fun (σ → τ)
```

**Term language (all three systems):**
```
Var(name, type)     -- variable
Const(name, type)   -- constant (with type instantiation)
Comb(term, term)    -- application
Abs(term, term)     -- lambda abstraction
```

Four term constructors. That's it.

#### HOL Light

**10 inference rules:**
1. `REFL t` → `⊢ t = t`
2. `TRANS` → from `s = t` and `t = u`, get `s = u`
3. `MK_COMB` → from `f = g` and `x = y`, get `f x = g y`
4. `ABS` → from `s = t`, get `(λx.s) = (λx.t)`
5. `BETA` → `⊢ (λx.t) x = t`
6. `ASSUME p` → `{p} ⊢ p`
7. `EQ_MP` → from `p ⟺ q` and `p`, get `q`
8. `DEDUCT_ANTISYM_RULE` → bidirectional deduction
9. `INST` → instantiate term variables
10. `INST_TYPE` → instantiate type variables

**3 axioms:** INFINITY, ETA, SELECT (Hilbert choice).

**Entire kernel: ~400 lines of OCaml.**

The abstract type `thm` is private; only these 10 rules + 3 axioms can
construct values of type `thm` (LCF architecture).

#### HOL4

Same logical strength, slightly different rule set:
- Has `SUBST` (general substitution) instead of `MK_COMB`+`TRANS`
- Has `DISCH`/`MP` (implication intro/elim) instead of `DEDUCT_ANTISYM_RULE`
- Same 3 axioms in essence

#### Isabelle (Logical Framework)

Isabelle is fundamentally different — it's a **meta-logic** that hosts object
logics. This is the closest existing system to "interchangeable bottoms."

**Meta-logic (Pure) has 3 connectives:**
- `⟹` — meta-implication
- `⋀x. ...` — meta-universal quantification
- `≡` — meta-equality (definitional)

**~11 inference rules** for natural deduction over these three connectives.

**Object logics are layered on top:**

| Object Logic | What it is |
|---|---|
| Isabelle/HOL | Higher-order logic (~95% of ecosystem) |
| Isabelle/ZF | Zermelo-Fraenkel set theory |
| Isabelle/FOL | First-order logic (classical + intuitionistic) |
| Isabelle/CTT | Martin-Lof constructive type theory (historical) |

To host a new logic: declare types, declare a judgment constant
(`Trueprop :: obj_prop ⇒ prop`), assert axioms as meta-theorems.

**The practical lesson:** The framework architecture supports interchangeability.
The ecosystem creates lock-in (Isabelle/HOL gets ~95% of library/automation
investment). There is no automated translation between object logics.

#### STT vs. Dependent Type Theory

| Feature | STT (HOL) | DTT (Lean/Coq/Agda) |
|---|---|---|
| Types depend on terms | No | Yes |
| Propositions | `bool` (a type) | Types (Curry-Howard) |
| Proof terms | No — `thm` is abstract | Yes — proofs are terms |
| Universes | None | `Type 0 : Type 1 : ...` |
| Inductive types | Encoded via definitional extension | Kernel primitive |
| Kernel complexity | Trivially simple | Complex (conversion checking) |
| Expressiveness | All classical HOL. No dependent types. | Full dependency spectrum. |

**Important:** STT + set theory is equiconsistent with CIC for formalizing
mathematics. The difference is structural convenience, not logical strength.

#### The LCF Architecture

Trust mechanism for HOL systems:
1. `thm` is an abstract type — constructors not exported
2. Only kernel inference rules can create `thm` values
3. All tactics/automation are untrusted code that must call kernel primitives
4. Host language type system enforces soundness

Tradeoff vs. type-theoretic systems: tiny kernel but no portable proof objects.
Lean/Coq produce proof terms (data) that independent checkers can verify.
HOL systems produce `thm` values that exist only at runtime.

## E-Graphs as Exploration Engine

E-graphs represent equivalence classes of expressions without committing to a
canonical form. This aligns directly with the "diff modulo equivalences" idea.

### Core Concepts

- **E-node**: operator + children (which are e-class IDs, not terms)
- **E-class**: equivalence class — set of e-nodes proven equivalent
- **Congruence invariant**: same operator + same-class children → same class
- **Equality saturation**: apply rewrite rules to fixed point (non-destructive)

### Equality Saturation Loop

1. Initialize e-graph with input expression
2. Search: e-match rewrite rule patterns against the e-graph
3. Apply: add rewrite results, merge e-classes
4. Rebuild: restore congruence invariant
5. Repeat until saturation / budget
6. Extract: pull "best" expression via cost function

Key property: rewrites are non-destructive. Bidirectional rules are safe
(`a + b <=> b + a`) — both forms coexist. Eliminates phase ordering.

### Rust Ecosystem

| Crate | Description |
|---|---|
| `egg` | E-graph library for equality saturation |
| `egglog` | E-graphs + Datalog (next-gen, recommended for new work) |
| `symbolica` | High-performance CAS |
| `cc-lemma` | E-graph guided inductive equational proofs |
| `cyclegg` | Cyclic equational prover using e-graphs |

### Limitations

- **Memory explosion** from interacting rewrite rules
- **Extraction is NP-complete** (greedy heuristics in practice)
- **Binders are hard** — e-graphs are first-order; lambda/quantifiers need
  special encoding
- **No native induction** — requires external scaffolding
- **No native disequality/ordering** (recent research addresses this)

### E-Graphs + Dependent Types

Active research, few mature implementations:
- `lean-egg`: equality saturation tactic for Lean 4 (encoding is lossy but
  result is proof-checked, so remains sound)
- Fundamental tension: dependent types make types depend on values, so merging
  e-classes can change what's well-typed

## Implications for Motif

### No Single Bottom

The prior art confirms: there is no singular correct kernel IR. Seven production
systems chose seven different structural primitives. The differences are not
ergonomic — they reflect genuine disagreements about what's primitive.

| System | Foundation | Kernel size |
|---|---|---|
| Lean 4 | CIC variant (6 core constructors) | ~5-10k LOC C++ |
| Coq | pCIC (~16 term constructors) | ~10k LOC OCaml |
| Agda | MLTT + induction-recursion | Large (whole checker) |
| Idris 2 | QTT (multiplicities on every binder) | Large (whole checker) |
| ATS | Separated statics/dynamics | Type checker + constraint solver |
| Dafny | FOL + SMT theories (no proof terms) | Large (Dafny + Boogie + Z3) |
| HOL Light | Simple type theory (4 term constructors) | ~400 LOC OCaml |

What's invariant across ALL of them:
- Binding + application
- Some notion of types/sorts
- Some notion of equality/conversion/validity

What varies:
- Whether types can depend on terms (yes in DTT, no in STT, no in Dafny)
- Whether proofs exist as objects (yes in DTT, no in HOL, no in Dafny)
- How elimination works
- Whether linearity exists
- Whether types and programs share a language
- What equality means
- Universe structure (hierarchy vs. flat vs. none)
- Whether verification is constructive or decided by SMT
- Whether the kernel is small+trusted or the whole toolchain

The design space is wider than "which dependent type theory." It includes
systems with no dependent types (HOL), no proof terms (Dafny), no universe
hierarchy (ATS), and completely separated type/term languages (ATS).

Isabelle's logical framework architecture is the closest existing precedent
for interchangeable bottoms — but in practice, ecosystem lock-in to a single
object logic (HOL) limits the interchangeability.

### Proposed Architecture

```
structural primitives (composition, symmetry, duality...)  ← define first
───────────────────────────────────────────────────────────
equivalence engine (e-graph / egglog)                      ← core data structure
───────────────────────────────────────────────────────────
backend adapters                                           ← pluggable, not singular
  ├── DTT-style (CIC / MLTT / QTT variants)
  ├── STT-style (HOL)
  ├── SMT-style (FOL + theories)
  └── framework-style (Isabelle/Pure-like meta-logic)
```

Start from what's invariant across representations. Let bottoms be
interchangeable backends. The system's value is in the structural
middle layer and the translation machinery between backends.

The design space for backends is wider than "which type theory" — it includes
fundamentally different verification paradigms (constructive proof terms vs.
classical LCF inference vs. SMT decision procedures). Each makes different
things natural/hard and encodes different structural choices about what
equality, proof, and computation mean.
