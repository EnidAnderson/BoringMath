# Depth audit, round 1 (2026-10-25)

Toolchain-side answers to the six work items of the foundation audit
(`docs/AUDITS/2026-10-25-foundation-audit.md`), all evidence gathered at
the pinned revision `v4.35.0-rc3` (checkout commit `c55e6e78`, dated
2026-09-24) with `rg` and file reads (GOLD), plus GitHub API queries for
upstream state (marked as such). Supersedes nothing yet: these are the
first depth grades. Protocol: `docs/AUDITS/README.md`.

## Item 1 — F7 triangulated categories: regrade PARTIAL → PARTIAL-MATURE

Evidence GOLD (directory read, key declarations read). Far more than
bare-bones; the shoulders for motive/weight work already exist:

- `Mathlib/CategoryTheory/Triangulated/` — 17 files: `Pretriangulated.lean`
  (`class Pretriangulated`, line 65), `Triangulated.lean`
  (`class IsTriangulated : Prop`, line 299 — the octahedral axiom is a
  Prop layered on `Pretriangulated`, not a separate class), `Rotate`,
  `TriangleShift`, `Adjunction` (triangulated adjunctions), `Functor`
  (triangulated functors + `mapTriangle` compatibilities), `Generators`,
  `HomologicalFunctor`, `SpectralObject`, `WeakKernels`, `Yoneda`,
  `Subcategory`, `LocalizingSubcategory.lean`.
- **t-structures are IN**: `TStructure/` subdirectory with `structure
  TStructure` (`TStructure/Basic.lean:55`), `class IsLE`/`IsGE` (lines
  160/165), `t.minus`/`t.plus`/`t.bounded`, `Heart`, truncation
  (`TruncLEGT`, `TruncLTGE`, `ETrunc`), `TExact`. This is exactly the
  standing infrastructure the monodromy/weight line needs.
- **Verdier quotients: NOT built.** `LocalizingSubcategory.lean` has
  `class IsVerdierLeftLocalizing`/`IsVerdierRightLocalizing` (lines
  45/56) and `triangulatedLocalizerMorphism` (line 161) whose docstrings
  *refer to* Verdier quotient functors, but `rg VerdierQuotient` = 0
  hits; the quotient construction for triangulated categories is absent.
  (The general `CategoryTheory/Localization` machinery exists and is the
  likely substrate.)

Regrade: F7 PARTIAL-MATURE (usable APIs: pretriangulated + triangulated,
rotation, functors, adjunctions, t-structures, localizing subcategories;
missing: Verdier quotients, generators theory depth unverified).

## Item 2 — F5 algebraic cycles: grade BARE (with usable pushforward)

Evidence GOLD (file read in full, 131 lines). `Mathlib/AlgebraicGeometry/
AlgebraicCycle/Basic.lean`: `abbrev AlgebraicCycle (X : Scheme) (R)`
(locally-finitely-supported functions on integral subsets — formal sums),
`mapCoeff`/`map` (pushforward along quasi-compact morphisms),
`IsWeilDivisor`, `weilDivisors` subgroup. No intersection products, no
rational equivalence, no correspondences. The cycle layer of the
correspondence module builds directly on this abbrev.

## Item 3 — F8/F9 model categories and quasicategories vs the spectra needs

Evidence GOLD (directory listings + key declarations).

- F8: `class ModelCategory` (`ModelCategory/Basic.lean:43`), 20 files:
  left/right homotopy, cylinder/path objects, cofibrant/fibrant object
  homotopy categories, `DerivabilityStructure{Cofibrant,Fibrant}`,
  `JoyalTrick`, `BrownLemma`, `Transport`. Grade: PARTIAL — a real
  homotopy-theory API for object-level arguments.
- F9: 7 quasicategory files (`Basic`, `InnerFibration`, `Nerve`,
  `StrictBicategory`, `StrictSegal`, two 2-truncated files). Grade: BARE —
  no marked simplicial sets, no straightening, no cocartesian fibrations,
  no join/slice theory.
- **F10 verdict: the deep hole is confirmed at the missing rung, not the
  bottom.** Sequential spectra need: (a) a Quillen-equivalent homotopy
  theory on simplicial sets (absent), (b) model structures on diagram/
  level categories (absent), (c) Bousfield localization (absent). The
  staging advice of the foundation audit stands: no spectra shards yet.

## Item 4 — F11 rigid/closed monoidal: grade MATURE (confirmed)

Evidence GOLD. `Monoidal/Rigid/Basic.lean`: `class ExactPairing` (line
77), `class HasRightDual`/`HasLeftDual` (236/242), with `Braided`,
`Functor`, `FunctorCategory`, `OfEquivalence` transports.
`Monoidal/Closed/Basic.lean`: `class MonoidalClosed` (line 46) + rich
periphery (Braided, Cartesian, Enrichment, Functor, Types, Zero, Ideal).
Game-semantics base (F12) can be built directly on this.

## Item 5 — F13 combinatorial game theory: the boundary is a saga (MAJOR REFINEMENT)

Evidence GOLD at the pin + GOLD via GitHub API upstream. The full history:

- **2024-12 → 2025-03**: a complete Conway layer was merged into mathlib
  (53 PRs with `SetTheory/Game` in title; files `Basic, Birthday,
  Domineering, Impartial, Nim, Ordinal, Short, State` under
  `Mathlib/SetTheory/Game/`; the trove's "mathlib already has the Conway
  layer" was TRUE then).
- **2025-08-07**: mathlib4 #28063 deprecated all of it, with the stated
  rationale: the material had been *downstreamed to a dedicated repo*
  — **`vihdzp/combinatorial-games`** — which had "expanded substantially",
  and the mathlib copy was unused elsewhere and "very unlikely to ever
  be" used.
- **2026-02-20**: mathlib4 #35550 removed the deprecated modules.
- **At the pin** (2026-09-24): `rg -l "PGame"` over the whole tree = 0
  hits; `Mathlib/SetTheory` contains only Cardinal, Descriptive, Lists,
  Ordinal, ZFC. ABSENT, GOLD.
- **At upstream master** (2026-10-25): same listing via the contents API.
  ABSENT, GOLD. (The earlier `Game`-only "fork contamination" story is
  resolved: the ground was not merely fork-land — it was upstream, and
  was moved out by upstream's own decision.)

**The external library (`vihdzp/combinatorial-games`, Apache-2.0,
113 stars, active — pushed 2026-10-25)** now holds, per its tree
(SILVER; GOLD reading pending): `Game/` (Basic, Birthday, Canonical,
Classes, Confusion, Functor, Graph, IGame, Order, Ordinal, Player,
Small, Special, Stops; `Impartial/Grundy`, `Loopy/{Basic,IGame,Outcome,
StoppingTime}`, `Specific/{Domineering,Nim,Poset}`), `Nimber/` (Basic,
Field, Nat, Omega, SimplestExtension, SmallDegree), `Surreal/` (Basic,
Birthday, Cut, Division, Dyadic, HahnSeries, Leading, Multiplication,
Omnific, Ordinal, Pow, Real), `SignExpansion/`, `NatOrdinal/`, tactics,
counterexamples.

**Probe of our program's gaps against that tree: no thermography, no
cooling, no temperature, no misère theory** (rg over the tree paths:
`therm|cool|misere|temperature|mean` = 0). Caveat (SILVER only):
`Game/Classes.lean`, `Game/Confusion.lean`, `Game/Stops.lean`, and
`Game/Special.lean` may already contain outcome-class and
stops/mean-value material — GOLD reading of those four files is
required before staking the outcome-class and thermography module names.

**Strategic consequence for F13.** Do not rebuild the Conway layer.
The program's CGT line should: (a) depend on (or vendor-with-care)
`combinatorial-games` as the base; (b) build our layers — thermography,
cooling, misère quotients, and the motivic dictionary — as new modules
on top; (c) keep the naming compatible with that library (its API names
are the de-facto standard for the Lean CGT ecosystem). Licensing: it is
Apache-2.0; depending on it is unproblematic for our HML repositories;
contributing a module there (if ever actually done) would be Apache
there, exactly like the mathlib case recorded in `docs/PR-WORKFLOW.md`.

Also recorded: `Mathlib/Order/GameAdd.lean` exists at the pin and at
master — it is an order-theoretic recursion gadget on `Sym2`, unrelated
to combinatorial game theory (name-collision awareness only).

## Item 6 — F14 algebraicity/transcendence: sharpened boundary (REFINED)

Evidence GOLD except where noted.

- **Where the transcendence-basis API lives**: NOT in `FieldTheory` — in
  `Mathlib/RingTheory/AlgebraicIndependent/TranscendenceBasis.lean`:
  `IsTranscendenceBasis`, `exists_isTranscendenceBasis`,
  `trdeg_eq_iSup_cardinalMk_isTranscendenceBasis`, the
  `AlgebraicIndependent.isTranscendenceBasis_iff` family, and the
  `IsTranscendenceBasis.mvPolynomial` pair (the universal-property
  statements — the nuts-and-bolts foundation for any certificate line).
  Grade: MATURE.
- **Lindemann**: `Mathlib/NumberTheory/Transcendental/Lindemann/
  AnalyticalPart.lean` (Yuyang Zhao, 2022; based on Jacobson, *Basic
  Algebra I*, 4.12) contains the analytic skeleton only:
  `hasDerivAt_cexp_mul_sumIDeriv`, `integral_exp_mul_eval`, `P`,
  `P_eq_integral_exp_mul_eval`, `P_algebraMap`, `P_le`. **The main
  Lindemann–Weierstrass theorem is NOT assembled** (`rg LindemannWeierstrass`
  finds only the namespace). So: analytical scaffolding PRESENT,
  theorem ABSENT. (Upstream in-flight check for an assembling PR: not yet
  done — cheap work item for round 2.)
- **Liouville**: `NumberTheory/Transcendental/Liouville/` — five files
  (Basic, LiouvilleNumber, LiouvilleWith, Measure, Residual). Substantial.
- **Gelfond–Schneider, Baker, Siegel–Shidlovsky, six exponentials: ABSENT**
  (rg over the whole tree; the lone `Lindemann`/`Schneider` hits are
  unrelated author attributions). The certificate line (Apéry weight-3)
  has a genuine green field above the `IsTranscendenceBasis` + Lindemann
  analytical layers.

## New finding (not in the round-1 map) — derived categories are IN-TREE

Evidence GOLD. `Mathlib/Algebra/Homology/DerivedCategory/` — 16 files:
`Basic` (`def DerivedCategory C := HomologicalComplexUpToQuasiIso C
(ComplexShape.up ℤ)`, the localization `Q`, `singleFunctors`),
`Ext/`, `KInjective`, `KProjective`, `Plus`, `RightDerivedFunctorPlus`,
`TStructure`, `HomologySequence`, `ShortExact`, `FullyFaithful`,
`Fractions`, `SmallShiftedHom`, `Linear`, derivability structures via
injectives. Plus `Mathlib/CategoryTheory/Functor/Derived/` — left/right
derived functors, pointwise variants, triangulated compatibilities.
This upgrades the trove's "derived categories: external paper" to:
**in-tree, substantial, at the pin**. Consequence for F10: the
derived-category-of-an-abelian-category layer is available as the
triangulated substrate today; what remains ABSENT is the stable/∞-level
(spectra, stable model structures, six functors). This shifts the
program's near-term motive constructions toward the in-tree
derived-category layer rather than the (absent) stable layer.

## Round-2 work items (small)

1. GOLD-read `CombinatorialGames/Game/{Classes,Confusion,Stops,Special}.
   lean` from the external library before staking outcome-class or
   thermography module names.
2. Check upstream for in-flight PRs assembling Lindemann–Weierstrass from
   `AnalyticalPart`.
3. Depth-read `CategoryTheory/Localization` + `Triangulated/
   LocalizingSubcategory` for the quotient-construction substrate.
