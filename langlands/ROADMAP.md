# Roadmap: Formalizing the Langlands Program in Lean 4 / Mathlib

Scope: get to the point where the **core Langlands conjectures can be formally
stated** (local and global correspondence, functoriality, Artin's conjecture),
then prove whatever is in reach. Grounded against Mathlib as vendored at
`langlands/.lake/packages/mathlib` (tagged for Lean toolchain in this project,
"v4.32.1" per the task brief). All claims below are backed by `find`/`grep`
against that source tree, not memory — file paths are cited so they can be
re-checked.

---

## 1. What Mathlib already has

### 1.1 Algebraic number theory (number fields, rings of integers, completions, valuations)

**Strong.** `Mathlib/NumberTheory/NumberField/` is a large, actively developed
directory:
- `Basic.lean` — `NumberField` class, ring of integers `𝓞 K`.
- `InfinitePlace/{Basic,Embeddings,Ramification,TotallyRealComplex}.lean`,
  `InfinitePlace/Completion.lean` — archimedean places and their completions.
- `Completion/{FinitePlace,InfinitePlace,LiesOverInstances,Ramification}.lean`
  — completions at all places, uniform treatment.
- `FinitePlaces.lean`, `RamificationInertia.lean` (in `NumberTheory/`) —
  non-archimedean places, ramification/inertia degrees.
- `Ideal/{Basic,Asymptotics,KummerDedekind}.lean` — ideal theory,
  Kummer–Dedekind.
- `Discriminant/{Defs,Basic,Different}.lean`, `ClassNumber.lean`,
  `Units/{Basic,Regulator,DirichletTheorem}.lean` — discriminant, class group,
  unit group, Dirichlet's unit theorem.
- `CanonicalEmbedding/*`, `FractionalIdeal.lean`, `Norm.lean`,
  `ProductFormula.lean`, `CMField.lean`, `Cyclotomic/*`, `DedekindZeta.lean`.
- Valuations: `Mathlib/RingTheory/DedekindDomain/AdicValuation.lean` (used by
  the finite adèle ring), `Mathlib/RingTheory/Valuation/Discrete/Basic.lean`.
- `Mathlib/RingTheory/Frobenius.lean` (2025, Andrew Yang) — **arithmetic
  Frobenius elements** for a finite Galois extension, built on
  `Mathlib/RingTheory/Invariant/{Basic,Profinite}.lean`. This is a genuinely
  load-bearing result for Langlands (Frobenius conjugacy classes are exactly
  what a Galois representation is decorated with).

**Missing:** no notion of "Frobenius element well-defined up to conjugacy as a
function of the Galois representation", no Chebotarev density statement tying
Frobenius distribution to L-functions.

### 1.2 p-adic numbers and local fields

**Partial.** `Mathlib/NumberTheory/Padics/` has `PadicNumbers.lean`,
`PadicIntegers.lean`, `PadicNorm.lean`, `Hensel.lean`, `ProperSpace.lean`,
`ValuativeRel.lean`, `WithVal.lean`, `RingHoms.lean`, `HeightOneSpectrum.lean`,
`Complex.lean` (ℂ_p), `Measure/{Basic,Topology}.lean` (Haar measure on ℚ_p /
ℤ_p already exists via general Haar-measure machinery), `AddChar.lean`
(additive characters of ℚ_p — directly useful for Tate's thesis / local
L-factors).

`Mathlib/NumberTheory/LocalField/Basic.lean` exists but is thin (one file) —
general local fields (finite extensions of ℚ_p or 𝔽_q((t))) are not developed
as a first-class abstraction the way number fields are; what's available is
via `NumberField.Completion.FinitePlace`, i.e. completions of number fields
at finite places, rather than a standalone "local field" typeclass hierarchy
with local class field theory attached.

**Missing:** local class field theory (local Artin map), local
Langlands-relevant structure (no smooth/admissible representations of
`GL_n(local field)`, see §1.5).

### 1.3 Adeles and ideles

**Present, additive side only.**
- `Mathlib/RingTheory/DedekindDomain/FiniteAdeleRing.lean` (María Inés de
  Frutos-Fernández) — finite adèle ring of a Dedekind domain as a restricted
  product, built on `Mathlib/Topology/Algebra/RestrictedProduct/*`.
- `Mathlib/NumberTheory/NumberField/InfiniteAdeleRing.lean` — infinite adèle
  ring (product over archimedean completions).
- `Mathlib/NumberTheory/NumberField/AdeleRing.lean` — full adèle ring
  `AdeleRing (𝓞 K) K` = infinite × finite, with `principalSubgroup` (the
  diagonal embedding of `K`).
- Restricted-product infrastructure: `Topology/Algebra/RestrictedProduct/
  {Basic,TopologicalSpace,Units}.lean`, `Topology/Algebra/IsOpenUnits.lean`
  (needed to give the units of a restricted product, i.e. ideles, their
  correct topology).

**Missing, confirmed by grep:** no `IdeleGroup`/`IdeleClassGroup` definition
anywhere in the tree (only the raw `RestrictedProduct.Units` machinery that
would let one be built); no compactness of `𝔸ₖ/K` or of the norm-one idele
class group; no strong approximation theorem (`grep` for "strong
approximation" is empty); no self-dual Haar measure / Tate's thesis setup
beyond the raw `AddChar` and Haar-measure primitives.

### 1.4 Algebraic groups (linear, reductive, split, ...)

**Essentially absent as a theory.** What exists:
- Concrete classical groups over a ring/field: `Mathlib/LinearAlgebra/
  GeneralLinearGroup/`, `Matrix/GeneralLinearGroup/`, `SpecialLinearGroup.lean`,
  `Matrix/SpecialLinearGroup.lean`, `Matrix/ProjectiveSpecialLinearGroup.lean`.
  These give `GL_n`, `SL_n`, `PSL_n` as abstract/matrix groups (used already
  by the modular forms library for `SL(2,ℤ)`), but with no group-scheme
  structure, no functor-of-points perspective, no algebraicity/rationality
  theory attached.
- Root systems and Weyl groups exist as **combinatorial/Lie-theoretic**
  objects: `Mathlib/LinearAlgebra/RootSystem/{Base,Hom,WeylGroup,
  Finite/CanonicalBilinear,Finite/Nondegenerate,GeckConstruction/Basic}.lean`,
  `Mathlib/Algebra/Lie/Weights/RootSystem.lean`. This is exactly the
  combinatorial data (root datum) that classifies split reductive groups —
  genuinely reusable — but there is no bridge from "abstract root system" to
  "reductive group scheme with that root datum."
- Group schemes: `grep` for "group scheme" only turns up
  `Mathlib/AlgebraicGeometry/Group/{Abelian,Smooth}.lean` (about group objects
  in the category of schemes generically, e.g. abelian varieties/smooth
  group schemes) and `Mathlib/RingTheory/HopfAlgebra/MonoidAlgebra.lean`. No
  torus, no notion of split/quasi-split/reductive/semisimple group scheme, no
  Chevalley classification, no dual group (Langlands dual) construction.
- `Mathlib/Algebra/BrauerGroup/{Defs,...}` exists (relevant to inner forms of
  reductive groups and to local class field theory via `H^2`, but not
  connected to anything algebraic-group-shaped yet).

**This is the single largest gap for Langlands.** Even *stating* "let G be a
split reductive group over a number field, ^L G its Langlands dual" requires
a theory of reductive groups that does not exist in Mathlib today. The
closest reusable ingredient is the root-system/Weyl-group library plus the
raw matrix groups `GL_n`/`SL_n` for the archetypal case.

### 1.5 Representation theory (finite groups, topological groups, p-adic groups)

**Good for finite/general abstract groups, essentially absent for the
smooth/admissible p-adic representation theory Langlands actually needs.**
- `Mathlib/RepresentationTheory/` is rich: `Basic.lean`, `Character.lean`,
  `FDRep.lean`, `Rep/{Basic,Iso,Res}.lean`, `Semisimple.lean`,
  `Irreducible.lean`, `Induced.lean`, `Coinduced.lean`, `Intertwining.lean`,
  `Maschke.lean`, `Tannaka.lean`, `AlgebraRepresentation/Basic.lean`.
- `Mathlib/RepresentationTheory/Continuous/{Basic,TopRep}.lean` — continuous
  representations of topological groups exist as a category (`TopRep`). This
  is a real foothold: admissible/smooth representations of `GL_n(ℚ_p)` are a
  further specialization (locally constant vectors under compact open
  subgroups) that is not yet formalized but has a plausible landing spot.
- `Mathlib/RepresentationTheory/Homological/` — group cohomology
  (`GroupCohomology/{Basic,Functoriality,Shapiro,Hilbert90,
  LongExactSequence,LowDegree,FiniteCyclic}.lean`), group homology, **Tate
  cohomology** (`TateCohomology/Basic.lean`), and **continuous cohomology**
  (`ContCohomology/{Basic,LowDegree,Functoriality}.lean`) for profinite/
  topological-group coefficients. `Hilbert90.lean` is present and is a
  genuine class-field-theory-adjacent result already proved.

**Missing:** no smooth representations, no admissible representations, no
Jacquet modules, no parabolic induction, no supercuspidal
representations/support, no Bernstein decomposition — i.e. none of the
representation-theoretic vocabulary the local Langlands correspondence is
stated in.

### 1.6 Automorphic forms

**Absent for the general notion; present only for the classical GL_2/SL_2(ℤ)
special case under a different name (modular forms).** `grep -rli
"automorphic"` across all of Mathlib returns only incidental hits
(`Algebra/Quandle.lean`, `NumberTheory/HeckeRing/Defs.lean` use the word
informally, not as a defined concept). What *does* exist and is directly
reusable as the motivating example:
- `Mathlib/NumberTheory/ModularForms/` — a substantial library: `Basic.lean`,
  `SlashActions.lean`, `SlashInvariantForms.lean`, `CongruenceSubgroups.lean`,
  `ArithmeticSubgroups.lean`, `Cusps.lean`, `BoundedAtCusp.lean`,
  `QExpansion.lean`, `CuspFormSubmodule.lean`, `Petersson.lean` (inner
  product), `EisensteinSeries/*` (a full sub-library), `LevelOne/*`
  (dimension formulas), `JacobiTheta/*`, `Delta.lean`, `DedekindEta.lean`.
- `Mathlib/NumberTheory/HeckeRing/Defs.lean` — an abstract Hecke ring, but
  this is the double-coset-algebra formalism, not Hecke *operators* acting on
  a specific space of modular forms with eigenform theory attached (`grep`
  for Hecke-operator-specific names like `HeckeOperator`/`T_p` found nothing
  relevant).

**Missing:** automorphic forms/representations for a general reductive group
`G(𝔸_K)`, cusp forms in that generality, Hecke operators as an algebra acting
on automorphic forms (only the abstract ring, not the action), Satake
isomorphism, Langlands' automorphic representation ↔ classical modular form
dictionary (the modular-forms library never leaves the classical, concrete
`SL(2,ℤ)` picture).

### 1.7 L-functions (Dirichlet, Hecke, Artin, automorphic)

**Strong for Dirichlet/Riemann zeta, absent for Hecke/Artin/automorphic.**
`Mathlib/NumberTheory/LSeries/` is large: `Basic.lean`, `Convergence.lean`,
`Linearity.lean`, `Convolution.lean`, `Dirichlet.lean`,
`DirichletContinuation.lean`, `RiemannZeta.lean`, `ZetaZeros.lean`,
`HurwitzZeta{Even,Odd,Values}.lean`, `AbstractFuncEq.lean` (an abstract
functional-equation framework — potentially reusable scaffolding for other
L-functions), `Nonvanishing.lean`, `Positivity.lean`, `PrimesInAP.lean`,
`MellinEqDirichlet.lean`, `SumCoeff.lean`, `Deriv.lean`, `Injectivity.lean`,
`ZMod.lean`. Plus `Mathlib/NumberTheory/NumberField/DedekindZeta.lean`
(Dedekind zeta function of a number field) and
`Mathlib/NumberTheory/EulerProduct/DirichletLSeries.lean`.

**Missing:** Hecke L-functions (of a Hecke character on the idele class
group — blocked on §1.3's missing idele class group), Artin L-functions (of
a Galois representation — blocked on §1.8), automorphic L-functions (blocked
on §1.6). The `AbstractFuncEq.lean` framework is the most promising reusable
piece: it's plausible Artin/automorphic L-functions could eventually plug
into it once their Euler products/coefficients are defined.

### 1.8 Galois representations

**Absent as a defined concept.** `grep -rli "galois representation"` finds
nothing; the closest hit, `CategoryTheory/Galois/Decomposition.lean`, is
about Grothendieck's categorical Galois theory (fiber functors, decomposition
groups for the category-theoretic Galois formalism), not about
`ρ : Gal(K̄/K) → GL_n(F)`. Ingredients that *are* present and directly
prerequisite:
- `Mathlib/FieldTheory/AbsoluteGaloisGroup.lean` — the absolute Galois group
  itself.
- `Mathlib/FieldTheory/Galois/Profinite.lean`,
  `Mathlib/Topology/Algebra/Category/ProfiniteGrp/`,
  `Mathlib/Topology/Category/{Profinite,LightProfinite}/` — profinite-group
  category theory, needed since Galois groups are profinite and a
  representation must be continuous.
- `Mathlib/CategoryTheory/Galois/*` (`Basic`, `Action`, `Equivalence`,
  `EssSurj`, `Full`, `GaloisObjects`, `IsFundamentalgroup`,
  `Prorepresentability`, `Topology`) — Grothendieck's Galois theory, giving
  an abstract fiber-functor formalism that generalizes the classical
  Gal(L/K)-action; reusable as scaffolding.
- `RingTheory/Frobenius.lean` (§1.1) and `RepresentationTheory/Continuous/*`
  (§1.5) are exactly the two ingredients that would need to be combined:
  continuous representations + Frobenius elements = the statement "a Galois
  representation is unramified at p and sends Frob_p to [specified conjugacy
  class]."

**Missing:** the actual definition
`GaloisRepresentation := ContinuousRepresentation (Gal(K̄/K)) F V` (or
similar), unramifiedness, local Galois representations at each place,
compatible systems of ℓ-adic representations, the Weil group / Weil-Deligne
group (`grep` for "weil group"/"WeilGroup" found nothing at all — this is a
hard blocker for both local Langlands and for Artin/Weil L-functions at
ramified places).

### 1.9 Class field theory

**Not present as a theorem, but real prerequisite infrastructure exists.**
`grep -rli "class field theory\|artin reciprocity"` turns up nothing on
point. What is present and is a genuine down payment:
- `Mathlib/RepresentationTheory/Homological/GroupCohomology/Hilbert90.lean` —
  Hilbert's Theorem 90, a classical stepping stone to local CFT via
  cohomological methods.
- `Mathlib/Algebra/BrauerGroup/*` — the Brauer group, which is where local
  CFT's `H²(Gal(L/K), L^×) ≅ ℚ/ℤ` statement lives.
- `Mathlib/RingTheory/DedekindDomain/SelmerGroup.lean`.
- `RingTheory/Frobenius.lean` (Frobenius elements, §1.1) is precisely the
  input to the (global) Artin map on unramified primes.

**Missing:** the Artin reciprocity map itself
(`Idele class group → Gal(K^ab/K)`), local reciprocity, the existence
theorem, everything tying Brauer-group `H²` to an explicit reciprocity
isomorphism.

### 1.10 Modular forms and modularity

Covered in §1.6 — this is Mathlib's most mature "Langlands-adjacent" corner.
Notably absent: any formal statement or partial result toward the modularity
theorem (elliptic curve ↔ weight-2 newform) or the Serre conjecture (odd
irreducible 2-dim mod-p Galois reps ↔ mod-p modular forms) — both are
"blocked on Galois representations" (§1.8) plus an elliptic-curve L-function
side that does exist in some form (`Mathlib/NumberTheory/FLT/` directory
exists, worth checking separately for Fermat's Last Theorem groundwork, which
is adjacent but a different project).

### 1.11 Homological algebra (group cohomology, Galois cohomology)

**Good, and directly useful.** Beyond what's cited in §1.5/§1.9: this is
arguably Mathlib's *strongest* Langlands-adjacent area after number fields —
group cohomology, group homology, Tate cohomology, and continuous cohomology
of topological/profinite groups are all present with functoriality,
long-exact-sequence, Shapiro's lemma, and low-degree (H⁰/H¹/H²) computations.
Galois cohomology specifically (i.e. continuous cohomology specialized to
`Gal(L/K)`-modules) is not packaged as its own named theory but is a thin
wrapper away given `ContCohomology` + `AbsoluteGaloisGroup` +
`ProfiniteGrp`.

### 1.12 Category theory (derived categories, sheaves)

**Broad and mature**, though this is general-purpose Mathlib category theory
rather than anything Langlands-specific: `CategoryTheory/Sites/*` (sheaves,
`SheafCohomology/{Basic,Cech,MayerVietoris}`,
`NonabelianCohomology/H1.lean`), `AlgebraicGeometry/Sites/
ElladicCohomology.lean` (a stub/start on étale-style ℓ-adic cohomology —
worth a closer look if the geometric Langlands / étale-cohomology route is
ever pursued), derived-category and homological-algebra scaffolding under
`Algebra/Homology/*`. Not a near-term bottleneck for *stating* the arithmetic
Langlands conjectures, but will matter for any proof that goes through étale
cohomology of Shimura varieties.

---

## 2. Prerequisites to formally *state* the core conjectures

### 2.1 Local Langlands correspondence (for `GL_n`, then general reductive `G`)

To state "there is a bijection between (a) `L`-parameters
`Gal(K̄_v/K_v) → ^L G` (or Weil-Deligne group → `^L G`) up to conjugacy, and
(b) packets of irreducible admissible representations of `G(K_v)`" you need,
at minimum:
1. A local field `K_v` (§1.2 — partial: have completions, not a clean local-field abstraction).
2. The absolute Galois group / Weil group of `K_v`, continuous (§1.8 — Galois group yes, Weil group **missing entirely**).
3. A reductive group `G` over `K_v` and its Langlands dual `^L G` (§1.4 — **missing entirely**, hardest gap).
4. Admissible (or at least smooth) representations of `G(K_v)` (§1.5 — **missing**; have continuous reps, not smoothness/admissibility over a locally profinite group).
5. `L`-parameters as continuous, Frobenius-semisimple homomorphisms
   `W_{K_v} → ^L G(ℂ)` (needs 2 and 3).

For `GL_n` specifically, steps 3–4 simplify (dual group of `GL_n` is `GL_n`;
"reductive group" can be replaced by literal matrix group `GL_n` from
§1.4's classical-groups library), which is why `GL_n` is the right entry
point rather than general `G`.

### 2.2 Global Langlands correspondence (automorphic ↔ Galois)

Needs: number field `K` (have, §1.1); adele ring `𝔸_K` (have, §1.3); a
reductive group `G/K`; automorphic representations of `G(𝔸_K)` (§1.6 —
missing in general, have the `GL_2`/classical special case); a global Galois
representation or compatible system (§1.8 — missing); and the local
correspondence at every place to state compatibility. Strictly harder than
2.1 since it needs 2.1 at every place plus a global automorphic theory.

### 2.3 Functoriality

Needs a map of `L`-groups `^L H → ^L G` (needs §1.4's dual-group
construction) inducing a transfer of automorphic representations/L-parameters
— i.e. depends on everything in 2.1/2.2 already existing for *two* groups
`H`, `G` plus the dual-group functor being contravariant-composable.
Strictly the hardest to even state, since it quantifies over pairs of
reductive groups and a homomorphism of their duals.

### 2.4 Artin's conjecture (Artin L-functions are automorphic)

Needs: Artin L-function of a Galois representation (needs §1.8 Galois reps +
§1.7's L-function framework, specifically factoring in local factors at
ramified primes via the **Weil group**, currently missing entirely); and the
`n = 1` global Langlands correspondence for `GL_n` (§2.2) to state "is
automorphic." This is *more* tractable to fully state than 2.2/2.3 in one
respect — it only needs `GL_n` — but the Artin L-function side needs the
Weil group, which nothing in Mathlib currently touches.

**Cross-cutting observation:** all four conjectures bottleneck on the same
three missing primitives: **(a)** reductive groups + Langlands dual group,
**(b)** the Weil group / Weil–Deligne group, **(c)** smooth/admissible
representations of `p`-adic and adelic groups. Sequencing the roadmap around
building these three first, in the cheapest special case (`GL_n`) before the
general case, is the only path that avoids stalling on (a).

---

## 3. Dependency-ordered roadmap

### Phase 0 — Idele class group (extends existing adele infrastructure)
- **Build:** `IdeleGroup K := (AdeleRing (𝓞 K) K)ˣ` with its correct
  (restricted-product-of-units) topology, then `IdeleClassGroup K := IdeleGroup K ⧸ K^×`.
- **Depends on:** `NumberField.AdeleRing` (have),
  `Topology/Algebra/RestrictedProduct/Units.lean` (have),
  `IsOpenUnits.lean` (have).
- **Size:** small–medium. Mostly assembling existing pieces + topology instances.
- **Upstreamable:** yes, cleanly — natural next file in
  `Mathlib/NumberTheory/NumberField/`, same authors' territory
  (de Frutos-Fernández, Mercuri have prior art here).

### Phase 1 — Weil group and Weil–Deligne group
- **Build:** `WeilGroup K_v` for a local field (extension of
  `Gal(K̄_v/K_v)` by ℤ via the valuation/Frobenius), then the Weil–Deligne
  group `W_{K_v} × SL_2` (or the Weil–Deligne representation formalism
  directly: pairs `(ρ, N)` with `ρ` a rep of `W_{K_v}` and `N` nilpotent
  satisfying the intertwining relation).
- **Depends on:** absolute Galois group (have, `AbsoluteGaloisGroup.lean`),
  profinite group category (have, `ProfiniteGrp`), local field valuation
  (have, `Padics`/completions), Frobenius elements (have, `RingTheory/
  Frobenius.lean`).
- **Size:** medium. No Mathlib precedent to build on beyond the pieces
  above; this is new mathematical content, but bounded (one group
  construction + one representation-compatibility condition).
- **Upstreamable:** yes — this is a standalone, well-defined object useful
  far beyond Langlands (local class field theory, Artin L-functions,
  local epsilon factors).

### Phase 2 — Local class field theory: local Artin map
- **Build:** the local reciprocity map `K_v^× → Gal(K_v^ab/K_v)` (or its
  Weil-group refinement `K_v^× ≅ W_{K_v}^ab`).
- **Depends on:** Phase 1 (Weil group), `RingTheory/Frobenius.lean`,
  `Algebra/BrauerGroup/*` (have — this is where the `H²` computation that
  proves the existence theorem lives), `GroupCohomology/Hilbert90.lean`
  (have).
- **Size:** large. This is a genuine theorem (not just a definition) with a
  real proof burden (local existence theorem, norm groups, Brauer group
  computation over local fields).
- **Upstreamable:** yes, high-value — local CFT is a named, citable theorem
  many other projects would want.
- **Note:** not strictly required to *state* the four core conjectures (they
  can be stated with the Artin map as an assumed/axiomatized black box), but
  required to make any of Phase 3+ meaningful rather than vacuous.

### Phase 3 — Reductive groups over a field (the dual-group blocker)
- **Build, in order:**
  1. Algebraic tori (split first: `𝔾_m^n` with a Galois action for
     non-split), as group schemes or as functor-of-points objects.
  2. Root data: pair a torus with the existing `RootSystem` combinatorial
     library (`Mathlib/LinearAlgebra/RootSystem/*` — have) via cocharacter/
     character lattices.
  3. Split reductive groups classified by root data (Chevalley); construct
     `GL_n`, `SL_n`, `Sp_{2n}`, `SO_n` as the running examples on top of the
     existing concrete matrix groups (have, §1.4) to validate the
     abstraction against known cases.
  4. The Langlands dual group `^L G` as the reductive group with dual root
     datum (roots ↔ coroots swapped); for split `G`, `^L G` needs no Galois
     action, for quasi-split/general `G` the dual carries an action of
     `Gal(K̄/K)` on the based root datum (needs Phase 1's Galois group +
     pinnings/automorphisms of the root datum — new).
- **Depends on:** `LinearAlgebra/RootSystem/*` (have), `GeneralLinearGroup`/
  `SpecialLinearGroup` (have, as validation targets), `AbsoluteGaloisGroup`
  (have, for step 4), essentially nothing else in Mathlib — this is mostly
  new development on top of the root-system library.
- **Size:** huge. This is comparable in scope to formalizing a chapter of
  Springer's *Linear Algebraic Groups* or Conrad's reductive-groups notes.
  Plausibly the single biggest piece of the entire roadmap. Can be
  meaningfully de-scoped: build split reductive groups classified by root
  data first (skip general algebraic-group/scheme foundations, skip
  non-split forms), which is enough to state local/global Langlands for
  quasi-split groups — the case almost all conjecture *statements* (not
  proofs) are given in.
- **Upstreamable:** yes, extremely high-value — Mathlib has no reductive
  group theory at all; this would be a foundational new area, not a
  patch to an existing one. Also the piece most likely to already be
  wanted by other Mathlib contributors (algebraic geometry / Lie theory
  communities) — worth checking Mathlib's Zulip/roadmap for parallel effort
  before starting, since duplicating a large in-flight project would be
  the worst outcome here.

### Phase 4 — Smooth and admissible representations of `p`-adic / adelic groups
- **Build:** for a locally profinite group `H` (e.g. `G(K_v)` once Phase 3
  exists, or concretely `GL_n(K_v)` before Phase 3 lands), a smooth
  representation = a representation on which every vector is fixed by some
  compact open subgroup; admissible = smooth + finite-dimensional fixed
  spaces under every compact open subgroup.
- **Depends on:** `RepresentationTheory/Continuous/{Basic,TopRep}.lean`
  (have — specialize `TopRep` to locally profinite groups and add the
  smoothness condition), `ProfiniteGrp`/compact-open-subgroup topology
  (have, for `GL_n` over `Padics`, §1.2).
- **Size:** medium–large for the `GL_n`-only version (usable immediately,
  doesn't wait on Phase 3); large again for the general-`G` version once
  Phase 3 exists (parabolic induction, Jacquet modules, supercuspidal
  support, Bernstein decomposition needed for the *full* local Langlands
  statement with L-packets, though the bijection can be *stated* for
  `GL_n` without any of that extra machinery, since local Langlands for
  `GL_n` is a clean bijection with no packets).
- **Upstreamable:** yes — smooth/admissible representation theory of
  `p`-adic groups is foundational and wanted independently of Langlands.

### Phase 5 — Statement of local Langlands for `GL_n`
- **Build:** the conjecture-as-a-`Prop`: a bijection between (continuous,
  Frobenius-semisimple, Weil–Deligne) `n`-dimensional representations of
  `W_{K_v}` and irreducible admissible representations of `GL_n(K_v)`,
  compatible with L-functions and ε-factors on both sides (the compatibility
  clause can initially be omitted/stubbed to get the bare bijection
  statement first).
- **Depends on:** Phase 1 (Weil–Deligne group), Phase 4's `GL_n`-only track
  (admissible reps of `GL_n(K_v)`), existing `GeneralLinearGroup` (have).
  **Does not need Phase 3** — this is exactly why `GL_n` is the right first
  target: its own dual group is itself.
- **Size:** small, once Phases 1 and 4 (`GL_n` track) exist — this phase is
  "just" writing the `Prop`, which is the whole point of the task's goal.
- **Upstreamable:** yes, as a formalized *conjecture statement* (a `Prop`/
  axiom-free `def`, not a `sorry`-laden proof) — valuable in its own right
  as a landmark for the Mathlib number theory community, independent of any
  progress toward proving it.

### Phase 6 — Statement of Artin's conjecture
- **Build:** Artin `L`-function of an `n`-dimensional Galois representation
  `ρ : Gal(K̄/K) → GL_n(ℂ)` (Euler product over unramified primes using
  Frobenius eigenvalues from `RingTheory/Frobenius.lean`, plus local factors
  at ramified primes needing the **inertia-invariants** of `ρ` restricted to
  `W_{K_v}` — needs Phase 1); state "`L(s, ρ)` equals `L(s, π)` for some
  automorphic representation `π` of `GL_n(𝔸_K)`" (needs Phase 8's global
  automorphic-representation notion, or can be stated over `GL_1` alone
  first, which reduces to classical Hecke-character CFT and needs only
  Phase 0 + Phase 2).
- **Depends on:** Phase 1, Phase 2 (for the `n=1` reduction — Artin's
  conjecture for 1-dim reps is essentially class field theory, already a
  theorem, not a conjecture, once Phase 2 lands), `NumberTheory/LSeries/
  AbstractFuncEq.lean` (have, as a scaffold for the L-function's analytic
  side), Phase 8 for `n > 1`.
- **Size:** medium for `n=1` statement/proof (mostly repackaging Phase 0/2);
  large for general `n` statement (needs Phase 8).
- **Upstreamable:** yes — Artin `L`-functions are independently notable.

### Phase 7 — Galois cohomology packaging (parallel track, low risk)
- **Build:** name and package `Gal(L/K)`-module cohomology as "Galois
  cohomology" explicitly (thin wrapper over `ContCohomology` +
  `AbsoluteGaloisGroup`), including inflation-restriction, and connect
  `Hilbert90.lean` to the `H^1(Gal, GL_n)`-classifies-forms statement
  (relevant to inner forms / non-quasi-split reductive groups in Phase 3).
- **Depends on:** `RepresentationTheory/Homological/ContCohomology/*`
  (have), `AbsoluteGaloisGroup` (have), `GroupCohomology/Hilbert90.lean`
  (have).
- **Size:** small–medium. Can run **in parallel** with Phases 0–2; no
  dependency either direction except that Phase 3's non-split forms will
  eventually want it.
- **Upstreamable:** yes, cheap win — Mathlib already has all the pieces,
  just not the "Galois cohomology" framing/API surface.

### Phase 8 — Automorphic representations of `G(𝔸_K)` and statement of global Langlands
- **Build:** automorphic forms/representations for general reductive `G`
  (functions on `G(K)\G(𝔸_K)` satisfying finiteness/growth/smoothness
  conditions, decomposed into irreducible representations of `G(𝔸_K)`);
  reconcile with the classical modular-forms library (§1.6) for `G = GL_2`
  as the validating special case; state the global correspondence as a
  `Prop` relating automorphic representations to (compatible systems of)
  Galois representations, using local Langlands (Phase 5, generalized via
  Phase 3+4) at each place for compatibility.
- **Depends on:** Phase 0 (adeles/idele class group), Phase 3 (reductive
  groups, for general `G`; `GL_2` case can lean on existing modular forms
  instead), Phase 4 (admissible representations, adelic/restricted-tensor-
  product version — new content: an automorphic representation is a
  restricted tensor product of local admissible representations, which
  needs its own "almost all factors unramified" bookkeeping).
- **Size:** huge — the single most mathematically demanding phase, on par
  with or larger than Phase 3. Realistically this is where "prove what we
  can" gives way to "state what we can" for the foreseeable future.
- **Upstreamable:** yes, high-value, but high risk of drift/duplication
  with any parallel effort elsewhere (geometric Langlands formalization
  projects exist outside Mathlib, e.g. in other proof assistants and in
  active math research — worth a literature/community check before
  committing large effort here specifically).

### Phase 9 — Functoriality statement
- **Build:** given `L`-map `^L H → ^L G` (a homomorphism of dual groups from
  Phase 3), state functorial transfer of automorphic representations
  (Phase 8) and/or of L-parameters (Phase 5, generalized).
- **Depends on:** Phase 3 (dual groups + homs between them), Phase 5/8
  generalized to arbitrary reductive `G`.
- **Size:** small once Phases 3, 5 (generalized), and 8 exist — again,
  "just" the `Prop`, but it sits at the end of the longest dependency chain
  in the whole roadmap.
- **Upstreamable:** yes.

---

## 4. Roadmap dependency graph (summary)

```
Phase 0 (idele class group)  ──────────────────────────┐
   depends on: AdeleRing (have)                         │
                                                          ▼
Phase 1 (Weil/Weil–Deligne group)             Phase 2 (local CFT / Artin map)
   depends on: AbsoluteGaloisGroup (have),        depends on: Phase 1, BrauerGroup (have),
   ProfiniteGrp (have), Frobenius (have)          Hilbert90 (have)
        │                                                │
        ├──────────────┬─────────────────────────────────┘
        ▼              ▼
Phase 5 (state local    Phase 6 (state Artin conj., n=1 track
Langlands for GL_n)      reduces to Phase 0+2; n>1 needs Phase 8)
        ▲
        │
Phase 4 (smooth/admissible reps; GL_n track needs no Phase 3)
        ▲
        │
Phase 3 (reductive groups + dual group)  ◄── HARDEST, LARGEST, most upstream-contested
   depends on: RootSystem (have), GeneralLinearGroup (have), AbsoluteGaloisGroup (have)
        │
        ▼
Phase 4 (general-G track)  ──►  Phase 8 (automorphic reps, global Langlands)  ──►  Phase 9 (functoriality)
                                        ▲
                                        │
                                 Phase 0 (idele class group)

Phase 7 (Galois cohomology packaging) — parallel, low-risk, feeds Phase 3's non-split-forms case only.
```

Everything downstream of Phase 3 for **general `G`** is gated on Phase 3.
Everything needed to state local/global Langlands **for `GL_n` specifically**
(Phases 0, 1, 2, 4-GL_n-track, 5, 6-n=1-track) can proceed without ever
touching Phase 3 — this is the practical route to "formally state the core
conjectures" fastest, deferring the huge, contested Phase 3 (general
reductive groups) and Phase 8 (general automorphic representations) until
later or indefinitely, while still landing a real, citable formal statement
of local Langlands for `GL_n` and (via Phase 2) a fully *proved* class field
theory.

---

## 5. The first move

**Define the idele class group of a number field (Phase 0).**

Concretely: in `Mathlib/NumberTheory/NumberField/` (or a new file
`IdeleRing.lean` alongside the existing `AdeleRing.lean`), define
`NumberField.IdeleGroup K := (NumberField.AdeleRing (𝓞 K) K)ˣ`, give it the
subspace/units topology already supported by
`Topology/Algebra/RestrictedProduct/Units.lean` and
`Topology/Algebra/IsOpenUnits.lean`, then define
`NumberField.IdeleClassGroup K := IdeleGroup K ⧸ (algebraMap K _).range`
(mirroring the existing `AdeleRing.principalSubgroup`, but for units instead
of the additive group).

This is the correct first move because:
- It is **small and concrete** — every ingredient it needs
  (`AdeleRing`, `RestrictedProduct.Units`, `IsOpenUnits`) already exists and
  is directly importable; no new mathematics needs to be invented, only
  assembled.
- It is **on the critical path for the fastest route to a stated
  conjecture** — Phase 0 is a direct prerequisite for Phase 2 (local/global
  CFT, needed for the `n=1` case of Artin's conjecture and for grounding the
  Weil group's abelianization) and for Phase 8 (adelic automorphic
  representations), without which nothing past "define adeles" moves.
- It is **independently upstreamable** — the existing `AdeleRing.lean` was
  clearly building toward exactly this (it already defines
  `principalSubgroup`, the additive analogue of what the idele class group
  needs); a PR adding the multiplicative/units version is a natural,
  reviewable next commit in the same file family, by the same reasoning the
  existing authors (de Frutos-Fernández, Mercuri) used.
- It **surfaces the next real blocker early**: getting compactness of the
  norm-one idele class group (needed for finiteness-of-class-number /
  Dirichlet-unit-theorem-style global results, and eventually for
  automorphic form growth conditions) will immediately require checking
  whether Mathlib's restricted-product topology machinery is strong enough,
  which is useful information to have before committing to Phase 8's much
  larger investment.
