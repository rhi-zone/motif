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

**Update — built in this project (Phase 0, now complete):** `IdeleGroup` and
`IdeleClassGroup` are defined in `Langlands/IdeleGroup.lean` (this repo, not
upstreamed to Mathlib), with `toClassGroup` and its kernel computed,
sorry-free. This closes the gap noted originally against Mathlib itself
(Mathlib upstream still has no such definition). Also landed this project:
the local norm map at finite places (`Langlands/NormMap.lean`, via
`HeightOneSpectrum`) and at archimedean places (`NumberField.InfinitePlace`),
plus the full idele-group norm map.

**Still missing:** no compactness of `𝔸ₖ/K` or of the norm-one idele class
group; no strong approximation theorem (`grep` for "strong approximation" is
empty); no self-dual Haar measure / Tate's thesis setup beyond the raw
`AddChar` and Haar-measure primitives.

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
compatible systems of ℓ-adic representations.

**Update — Weil group and Weil–Deligne group both now built in this project
(Phase 1, complete):** `grep` for "weil group"/"WeilGroup" still finds
nothing in Mathlib itself, but this project's own `Langlands/WeilGroup.lean`
fully constructs `W_K` as the preimage of ℤ in ℤ̂ under `toZhatHom`, with the
decomposition subgroup (everything), the inertia subgroup, the arithmetic
Frobenius, and `Gal(k̄/𝓀[K]) ≅ ℤ̂` sending Frobenius to 1. On top of that,
`Langlands/WeilDeligneRepresentation.lean` lands
`LocalField.WeilDeligneRepresentation K V`: a structure bundling a
representation `ρ : Representation ℂ (WeilGroup K) V`, a nilpotent
`N : V →ₗ[ℂ] V`, and the intertwining relation
`ρ w ∘ₗ N ∘ₗ ρ w⁻¹ = weilNormChar K w • N`, plus `ofRepresentation`/`trivial`
constructors — all sorry-free. This closes the hard blocker for local
Langlands and for Artin/Weil L-functions at ramified places.

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
2. The absolute Galois group / Weil group of `K_v`, continuous (§1.8 — Galois group yes; Weil group and Weil-Deligne group both now built in this project's `Langlands/WeilGroup.lean` and `Langlands/WeilDeligneRepresentation.lean`, Phase 1, complete).
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
ramified primes via the **Weil-Deligne group** — now built in this project,
§1.8, `Langlands/WeilDeligneRepresentation.lean`); and the
`n = 1` global Langlands correspondence for `GL_n` (§2.2) to state "is
automorphic." This is *more* tractable to fully state than 2.2/2.3 in one
respect — it only needs `GL_n` — and the Artin L-function side's Weil-Deligne
prerequisite is now in place in this project (nothing in Mathlib upstream
touches it yet).

**Cross-cutting observation:** all four conjectures bottleneck on the same
three missing primitives: **(a)** reductive groups + Langlands dual group,
**(b)** the Weil–Deligne group (now built in this project — both
`Langlands/WeilGroup.lean` and `Langlands/WeilDeligneRepresentation.lean`,
Phase 1 complete), **(c)** smooth/admissible representations of `p`-adic and
adelic groups. Sequencing the roadmap around building these three first, in
the cheapest special case (`GL_n`) before the general case, is the only path
that avoids stalling on (a).

---

## 3. Dependency-ordered roadmap

### Phase 0 — Idele class group (extends existing adele infrastructure) — **COMPLETE**
- **Status:** done, sorry-free. `IdeleGroup K := (AdeleRing (𝓞 K) K)ˣ` and
  `IdeleClassGroup K := IdeleGroup K ⧸ K^×` are built in
  `Langlands/IdeleGroup.lean`, with `toClassGroup` and its kernel computed.
  Also landed alongside it: the local norm map at finite places
  (`Langlands/NormMap.lean`, via `HeightOneSpectrum`) and at archimedean
  places (`NumberField.InfinitePlace`), the full idele-group norm map, the
  Kedlaya–Sutherland unramified-extension correspondence
  (`Langlands/UnramifiedExtension.lean`), and rank-one valuation
  compatibility (`Langlands/HenselianValuation.lean`).
- **Depended on:** `NumberField.AdeleRing` (have),
  `Topology/Algebra/RestrictedProduct/Units.lean` (have),
  `IsOpenUnits.lean` (have).
- **Not yet done:** not upstreamed to Mathlib; compactness of the norm-one
  idele class group and strong approximation remain open (§1.3).
- **Upstreamable:** yes, cleanly — natural next file in
  `Mathlib/NumberTheory/NumberField/`, same authors' territory
  (de Frutos-Fernández, Mercuri have prior art here).

### Phase 1 — Weil group and Weil–Deligne group — **COMPLETE**
- **Status:** done, sorry-free. The plain Weil group is built in
  `Langlands/WeilGroup.lean`: `W_K` as the preimage of ℤ in ℤ̂ under
  `toZhatHom`, the decomposition subgroup (everything), the inertia
  subgroup, the arithmetic Frobenius, and
  `Gal(k̄/𝓀[K]) ≅ ℤ̂` sending Frobenius to 1. On top of that,
  `Langlands/WeilDeligneRepresentation.lean` lands
  `LocalField.WeilDeligneRepresentation K V`: a structure bundling a
  representation `ρ : Representation ℂ (WeilGroup K) V`, a nilpotent
  `N : V →ₗ[ℂ] V`, and the intertwining relation
  `ρ w ∘ₗ N ∘ₗ ρ w⁻¹ = weilNormChar K w • N`, with `ofRepresentation`/
  `trivial` constructors. This matches the phase's original description
  (extension of `Gal(K̄_v/K_v)` by ℤ via valuation/Frobenius, plus the
  `(ρ, N)` pair formalism with nilpotent-intertwining condition, chosen
  over the `W_K × SL_2` alternative).
- **Depended on:** absolute Galois group (have, `AbsoluteGaloisGroup.lean`),
  profinite group category (have, `ProfiniteGrp`, plus a new
  universe-bridging instance landed this session), local field valuation
  (have, `Padics`/completions, plus new rank-one valuation compatibility in
  `Langlands/HenselianValuation.lean`), Frobenius elements (have,
  `RingTheory/Frobenius.lean`). Also newly available as general-purpose
  infrastructure: cyclic-subgroup-by-divisor classification,
  ℤ-subgroup-by-index classification.
- **Not yet done:** not upstreamed to Mathlib.
- **Upstreamable:** yes — this is a standalone, well-defined object useful
  far beyond Langlands (local class field theory, Artin L-functions,
  local epsilon factors).

### Phase 2 — Local class field theory: local Artin map
- **Build:** the local reciprocity map `K_v^× → Gal(K_v^ab/K_v)` (or its
  Weil-group refinement `K_v^× ≅ W_{K_v}^ab`).
- **Depends on:** Phase 1 (Weil group — **now complete**), `RingTheory/
  Frobenius.lean`, `Algebra/BrauerGroup/*` (have — this is where the `H²`
  computation that proves the existence theorem lives),
  `GroupCohomology/Hilbert90.lean` (have).
- **Size:** large. This is a genuine theorem (not just a definition) with a
  real proof burden (local existence theorem, norm groups, Brauer group
  computation over local fields).
- **Scope correction (review):** "`BrauerGroup + Hilbert90`" in the
  dependency list above is the route marker, not the distance covered. The
  local Artin map is not just an isomorphism `K_v^× ≅ W_{K_v}^ab` — it needs
  to be *characterized*: norm functoriality (the map is compatible with norm
  maps for finite extensions), Frobenius compatibility (uniformizers map to
  Frobenius lifts on unramified extensions), and the existence theorem
  (open subgroups of finite index in `K_v^×` correspond to abelian
  extensions). Getting from the raw Brauer-group `H²` computation to an
  Artin map *with these characterizing properties* is the bulk of Serre's
  *Local Fields*, chapters VIII–XIII — this is comparable in size to
  everything else in Phase 2 combined, not a footnote to it.
- **New prerequisites now available (this project):** the local norm map at
  finite places (`Langlands/NormMap.lean`) and archimedean places, the full
  idele-group norm map, and the Kedlaya–Sutherland unramified-extension
  correspondence (`Langlands/UnramifiedExtension.lean`) — these are direct
  down payments on the "norm functoriality" and "Frobenius compatibility on
  unramified extensions" characterizing properties described above, though
  the reciprocity map itself and the existence theorem are still not
  started.
- **Upstreamable:** yes, high-value — local CFT is a named, citable theorem
  many other projects would want.
- **Note:** not strictly required to *state* the four core conjectures (they
  can be stated with the Artin map as an assumed/axiomatized black box), but
  required to make any of Phase 3+ meaningful rather than vacuous.
- **Before building: check for prior formalization.** Of every phase in this
  roadmap, Phase 2 is the likeliest to already exist in some form elsewhere
  — local/global class field theory is a natural target for other
  formalization efforts (e.g. community CFT work adjacent to the
  Mathlib `FLT` project, `Mathlib/NumberTheory/FLT/`, §1.10). Check that
  effort, and any Zulip/roadmap discussion around it, before writing new CFT
  proofs in-repo — duplicating an in-flight class field theory formalization
  would be the single most wasteful outcome in this whole plan.

### Phase 2.5 — Satake isomorphism for unramified `GL_n` (new milestone, review addition)
- **Build:** the unramified Hecke algebra `H(GL_n(K_v), GL_n(𝒪_v))` (the
  double-coset convolution algebra of `GL_n(K_v)` relative to the maximal
  compact `GL_n(𝒪_v)`) and the Satake isomorphism identifying it with the
  ring of symmetric polynomials in `n` variables (equivalently, with
  representations of the dual torus/Weyl-invariant functions on it — for
  `GL_n` the dual group is again `GL_n`, so this needs none of Phase 3).
- **Why it goes here:** this is the best value-per-effort item in the whole
  roadmap. It is **self-contained** — needs only `GL_n(K_v)`'s double-coset
  structure, the existing `HeckeRing/Defs.lean` abstract Hecke-ring formalism
  (have, §1.6), and Mathlib's polynomial-ring/symmetric-function library
  (not audited above but standard Mathlib territory) — and it **yields a
  provable theorem**, not just a stated conjecture: the unramified local
  Langlands correspondence (Satake parameters ↔ unramified irreducible
  admissible representations) drops out of the Satake isomorphism directly,
  giving the roadmap its first genuine, non-vacuous local Langlands result
  well before the general Phase 5 statement is reachable.
- **Depends on:** `NumberTheory/HeckeRing/Defs.lean` (have), Phase 4's
  `GL_n`-track admissible representations (for the unramified-representations
  side of the correspondence), `GeneralLinearGroup` (have). Does **not**
  depend on Phase 3.
- **Feeds:** the unramified case of Phase 5's local Langlands statement
  (directly, as a proved special case rather than a stated conjecture), and
  Phase 8's restricted tensor products (an automorphic representation is
  unramified — i.e. has a fixed vector under the maximal compact — at almost
  all places, and the Satake isomorphism is exactly what controls the local
  factor at those places).
- **Size:** medium. Bounded, classical, and well-documented in standard
  references (Bump's *Automorphic Forms*, Gelbart's `GL_2` notes generalize
  cleanly to `GL_n`).
- **Upstreamable:** yes — the Satake isomorphism is a named, citable result
  independent of the rest of Langlands.

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
- **Reframing (review):** this is not a project phase in the same sense as
  the others in this roadmap — it is a **Mathlib-core campaign**. The dual
  group `^L G` needs Chevalley existence/uniqueness for reductive groups
  built from root data, and that is Mathlib's largest relevant crater: as of
  this writing there is no settled maintainer consensus even on the base
  definitions (what a "reductive group" *is* as a Mathlib structure — scheme-
  theoretic vs. functor-of-points vs. combinatorial-root-datum-first — is an
  open design question upstream, not just an unfilled gap). Treating Phase 3
  as a phase this project completes on its own timeline is the wrong frame;
  treating it as an upstream Mathlib contribution this project seeds and
  budgets for indefinite duration is the right one.
  - **Mitigation (a) — decouple the Galois layer from group existence.**
    Define `^L G` *combinatorially* now: a dual root datum, built directly on
    the existing `RootSystem` API (have, §1.4), with the Galois action on it
    given by an action on the abstract based root datum (needed anyway for
    step 4 above). This lets everything downstream that only needs `^L G` as
    a group *with a root datum* (L-parameters, functoriality maps between
    dual sides) proceed without waiting on Chevalley's theorem — i.e. without
    waiting on `G` itself existing as a bona fide reductive group object.
    Only the "transfer of representations of `G(K_v)` itself" side of local
    Langlands needs `G`, not `^L G`, to exist as a group scheme.
  - **Mitigation (b) — budget, don't schedule.** Treat full Phase 3 (Chevalley
    existence + uniqueness for general reductive groups) as an upstream
    Mathlib contribution with its own review cycle and timeline, not a task
    this roadmap can complete unilaterally. Phase 7 (Galois cohomology
    packaging) correctly feeds only the non-split-forms case of Phase 3 and
    can lag indefinitely without blocking anything else in this roadmap.

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

### Phase 4.5 — Local L-factors and ε-factors (review addition — vacuity fix for Phase 5)
- **Why this phase exists:** a bare bijection between `L`-parameters and
  irreducible admissible representations of `GL_n(K_v)`, with no further
  structure, is **vacuously true by cardinality** — both sides are countably
  infinite sets, so *some* bijection trivially exists with no mathematical
  content. The actual content of local Langlands for `GL_n` (this is
  Henniart's uniqueness theorem territory) lives in the correspondence being
  the *unique* bijection compatible with: twisting by characters, duality
  (contragredient ↔ dual representation), central characters
  (determinant ↔ central character under class field theory), and
  **preservation of L-factors and ε-factors of pairs** under the
  correspondence. Without this phase, Phase 5 cannot distinguish a genuine
  statement of local Langlands from a cardinality triviality.
- **Build:** local L-factors `L(s, ρ)` and Deligne–Langlands ε-factors
  `ε(s, ρ, ψ)` for Weil–Deligne representations `ρ`, and their representation-
  theoretic counterparts (Rankin–Selberg / Godement–Jacquet local factors)
  for admissible representations of `GL_n(K_v)` and `GL_n(K_v) × GL_m(K_v)`
  pairs.
- **New prerequisites, confirmed missing:** additive characters of `K_v`
  (have for `K_v = ℚ_p` via `Padics/AddChar.lean`, §1.2, but not for general
  local fields), a Haar measure normalization convention (Tate's thesis
  requires a self-dual measure with respect to the chosen additive
  character — flagged as missing in §1.3), and the local functional equation
  relating `L(s, ρ)` to `L(1-s, ρ^∨)` via the ε-factor.
- **Convention hazard, flagged for whoever picks this up:** Tate's original
  thesis normalization and Deligne's later ε-factor formalism (*Les
  constantes des équations fonctionnelles des fonctions L*, Antwerp II)
  diverge in bookkeeping conventions (choice of additive character, measure
  normalization, and sign/exponent conventions on the local root number) —
  this is a well-known source of errors in the literature, so the Lean
  definitions must pin down *which* convention is being formalized and state
  it explicitly rather than silently inheriting one source's choices.
- **Depends on:** Phase 1 (Weil–Deligne group, for the Galois side), Phase 4
  (admissible representations of `GL_n(K_v)`, for the automorphic side),
  `Padics/AddChar.lean` and `Padics/Measure/*` (have, for `ℚ_p`; need
  extending to general local fields), `NumberTheory/LSeries/
  AbstractFuncEq.lean` (have, potential scaffold for the functional
  equation).
- **Size:** large — this is a full local-constants theory, comparable in
  scope to a chapter of Bushnell–Henniart's *The Local Langlands Conjecture
  for GL(2)* or Tate's Corvallis article.
- **Upstreamable:** yes — local L- and ε-factors are foundational and wanted
  independently (Tate's thesis itself is a natural, self-contained Mathlib
  target).

### Phase 5 — Statement of local Langlands for `GL_n`
- **Build:** the conjecture-as-a-`Prop`: a bijection between (continuous,
  Frobenius-semisimple, Weil–Deligne) `n`-dimensional representations of
  `W_{K_v}` and irreducible admissible representations of `GL_n(K_v)`,
  compatible with L-functions and ε-factors on both sides (the compatibility
  clause can initially be omitted/stubbed to get the bare bijection
  statement first).
- **Vacuity caveat (review) — acceptance test:** per Phase 4.5 above, a bare
  bijection is **not an acceptable formalization goal on its own** — both
  sides are countably infinite, so a bijection exists trivially by
  cardinality with zero mathematical content. Two ways to avoid shipping a
  vacuous statement:
  1. Do the full version: require Phase 4.5's L-factor/ε-factor compatibility
     clauses (plus twisting, duality, central-character compatibility) as
     part of the `Prop`, so the bijection is characterized, not just
     asserted. This is Henniart's uniqueness theorem and is the
     mathematically honest statement of local Langlands for `GL_n`.
  2. Or explicitly scope Phase 5 as "the bijection statement up to
     characterization" — i.e. keep the bare bijection as an intentionally
     weaker placeholder, but **label it as such in the `Prop`'s
     documentation** (e.g. a doc-comment noting "this statement, absent the
     compatibility clauses of Phase 4.5, is a cardinality triviality and
     should not be cited as a formalization of local Langlands without
     them"), so nobody downstream mistakes the placeholder for the theorem.
  Either path is acceptable; shipping the bare bijection *without* one of
  these two markers is not — that is exactly the failure mode this
  correction targets.
- **Depends on:** Phase 1 (Weil–Deligne group), Phase 4's `GL_n`-only track
  (admissible reps of `GL_n(K_v)`), Phase 4.5 (L-/ε-factors, for the
  non-vacuous version), existing `GeneralLinearGroup` (have).
  **Does not need Phase 3** — this is exactly why `GL_n` is the right first
  target: its own dual group is itself.
- **Size:** small, once Phases 1 and 4 (`GL_n` track) exist, *for the bare
  bijection*; the non-vacuous version additionally needs Phase 4.5, which is
  large. This phase is "just" writing the `Prop` only in the weak sense —
  writing the `Prop` that is actually worth writing is gated on Phase 4.5.
- **Upstreamable:** yes, as a formalized *conjecture statement* (a `Prop`/
  axiom-free `def`, not a `sorry`-laden proof) — valuable in its own right
  as a landmark for the Mathlib number theory community, independent of any
  progress toward proving it, **provided** the vacuity caveat above is
  respected.

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
- **Acceptance criteria (review) — vacuity test:** "automorphic
  representations" defined as a bare restricted tensor product of local
  admissible representations, with no further structure, is a definition
  with no theorem in it — it says nothing about which restricted tensor
  products actually arise from genuine automorphic forms. The content that
  must be present before this phase counts as done:
  - **Cuspidality:** the subspace of cusp forms (vanishing constant terms
    along all proper parabolics) must be identified, since the cuspidal
    spectrum is where the representation theory is discrete and where local
    Langlands packets are meant to land; without it, "automorphic
    representation" has no home for the actual correspondence.
  - **Multiplicity:** the multiplicity of an irreducible representation in
    the (cuspidal) automorphic spectrum must be at least stated as a
    quantity (finite for cuspidal, by a Gelfand-pair/discrete-spectrum
    argument), even if multiplicity-one (known for `GL_n`, false in general)
    is deferred as a separate theorem.
  - **L² structure:** the decomposition of `L²(G(K)\G(𝔸_K))` (or its
    central-character-twisted variant) into a direct sum/integral of
    irreducibles — discrete spectrum (cuspidal + residual) plus continuous
    (Eisenstein) spectrum — needs to be at least stated, since "automorphic
    representation" without reference to this decomposition is just "some
    representation of `G(𝔸_K))`," not the object Langlands' conjectures are
    about.
  Absent these three, Phase 8 produces a restricted tensor product with no
  theorem attached to it — a definition that type-checks but proves nothing
  and characterizes nothing. These three items should be treated as the
  minimum bar for calling Phase 8 "done" rather than "stated."
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
Phase 0 (idele class group) — COMPLETE ────────────────┐
   built: IdeleGroup/IdeleClassGroup, norm maps          │
   (finite + archimedean places), unramified-ext.        │
   correspondence, Henselian valuation compat.           ▼
Phase 1 (Weil/Weil–Deligne group) — COMPLETE            Phase 2 (local CFT / Artin map)
   built: WeilGroup, WeilDeligneRepresentation             depends on: Phase 1 (done), BrauerGroup
   depends on: AbsoluteGaloisGroup (have),        (have), Hilbert90 (have) — scope: also norm
   ProfiniteGrp (have), Frobenius (have)          functoriality + Frobenius compat (Serre
        │                                          Local Fields VIII–XIII); norm maps +
        │                                          unramified-ext. correspondence now available
        │                                          (Phase 0) as down payment; check FLT-adjacent
        │                                          CFT formalization before building
        │                                                │
        │                                                ▼
        │                                       Phase 2.5 (Satake isomorphism for
        │                                       unramified GL_n — new, self-contained,
        │                                       first PROVABLE unramified LLC)
        ├──────────────┬─────────────────────────────────┘
        ▼              ▼
Phase 4.5 (local L-/ε-factors — new, fixes  Phase 6 (state Artin conj., n=1 track
Phase 5 vacuity; needs additive characters,   reduces to Phase 0+2; n>1 needs Phase 8)
Haar normalization, functional equation;
Tate-vs-Deligne convention hazard flagged)
        │
        ▼
Phase 5 (state local Langlands for GL_n —
bare bijection is VACUOUS by cardinality;
needs Phase 4.5's compatibility clauses or
an explicit "up to characterization" label)
        ▲
        │
Phase 4 (smooth/admissible reps; GL_n track needs no Phase 3)
        ▲
        │
Phase 3 (reductive groups + dual group)  ◄── Mathlib-CORE CAMPAIGN, not a project
   depends on: RootSystem (have), GeneralLinearGroup (have), AbsoluteGaloisGroup (have)   phase: Chevalley existence/uniqueness has
        │                                                                                  no settled upstream maintainer consensus.
        ▼                                                                                  Mitigation: define ^L G combinatorially now
Phase 4 (general-G track)  ──►  Phase 8 (automorphic reps, global Langlands —              via dual root datum (decouples from Chevalley);
acceptance test: needs cuspidality,           ──►  Phase 9 (functoriality)                 budget rest as upstream PR, not in-repo work.
multiplicity, L² structure — bare restricted
tensor product has no theorem in it)
                                        ▲
                                        │
                                 Phase 0 (idele class group)

Phase 7 (Galois cohomology packaging) — parallel, low-risk, feeds Phase 3's non-split-forms case only, can lag indefinitely.
```

Everything downstream of Phase 3 for **general `G`** is gated on Phase 3.
Everything needed to state local/global Langlands **for `GL_n` specifically**
(Phases 0, 1, 2, 2.5, 4-GL_n-track, 4.5, 5, 6-n=1-track) can proceed without
ever touching Phase 3 — this is the practical route to "formally state the
core conjectures" fastest, deferring the huge, contested Phase 3 (general
reductive groups, reframed above as a Mathlib-core campaign rather than a
project phase) and Phase 8 (general automorphic representations) until later
or indefinitely, while still landing a real, citable formal statement of
local Langlands for `GL_n` and (via Phase 2) a fully *proved* class field
theory. Phase 2.5 (Satake for unramified `GL_n`) is flagged separately as
the single best value-per-effort item in the graph: self-contained, needs no
Phase 3, and yields an actually-provable theorem rather than another stated
conjecture.

---

## 5. The first move

**Status update: Phase 0 (idele class group) and Phase 1 (Weil group /
Weil–Deligne group) are both done.** `IdeleGroup`/`IdeleClassGroup` are
built in `Langlands/IdeleGroup.lean`, sorry-free, along with local norm maps
at finite and archimedean places, the idele-group norm map, the
Kedlaya–Sutherland unramified-extension correspondence, and rank-one
valuation compatibility. The Weil group is built in `Langlands/WeilGroup.lean`,
and the Weil–Deligne representation formalism — `LocalField.
WeilDeligneRepresentation K V`, bundling `ρ`, nilpotent `N`, and the
intertwining relation — is built in `Langlands/WeilDeligneRepresentation.lean`.
Both are sorry-free (see Phase 0 and Phase 1 status above).

**Next move: begin Phase 2 (local class field theory / the local Artin
map).**

Concretely: build the local reciprocity map `K_v^× → Gal(K_v^ab/K_v)` (or
its Weil-group refinement `K_v^× ≅ W_{K_v}^ab`), on top of the now-complete
`WeilGroup`, drawing on this project's norm-map and unramified-extension
infrastructure (`Langlands/NormMap.lean`, `Langlands/UnramifiedExtension.lean`)
as a down payment on the norm-functoriality and Frobenius-compatibility
characterizing properties the map needs (see Phase 2's scope correction
above). Before writing new proofs, check for prior formalization of local/
global CFT elsewhere (e.g. around the Mathlib `FLT` project) — duplicating
an in-flight effort would be the most wasteful outcome available here.

This is the correct next move because:
- It is **the only remaining prerequisite gate before Phase 3+ becomes
  meaningful** — every phase in this roadmap can already be *stated* with
  the Artin map axiomatized, but Phase 2 is required to make any of it
  *proved* rather than vacuous (see Phase 2's note above).
- It has **more prerequisites in place than any point so far** — Phase 1
  (Weil group), the Brauer group, and Hilbert's Theorem 90 are all
  available in Mathlib, and this project's own norm-map and
  unramified-extension infrastructure is a direct down payment on Phase 2's
  hardest characterizing properties.
- It is **independently upstreamable and high-value** — local class field
  theory is a named, citable theorem many other formalization efforts would
  want, the same way the Weil group, Weil–Deligne representation, and idele
  class group already are.
- It carries a **real risk of duplicated effort** that's cheap to check for
  up front but expensive to discover after building — hence checking for
  prior/in-flight CFT formalization is the first concrete step, not an
  afterthought.
