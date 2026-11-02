# RETRO.0 — graded nonconstructivity inventory of `main` (2026-10-31)

Ticket: RETRO.0 (#114), gating RETRO.1 (#115) / RETRO.2 (#116) scoping.
Scope: every module under `BoringMath/` and `probes/` on `main`
(`cad7cd1` at survey time; branch `feat/formal-periods-axiom-lint` adds the
P-line and Sites layer surveyed below). Method: grep battery
(`noncomputable`, `Classical.`, `by_cases`, `by_contra`, `sorry`) plus
`#print axioms` / `#lint_axioms` probes run at the pin
`leanprover/lean4:v4.35.0-rc3`, mathlib `v4.35.0-rc3` (checkout `c55e6e78`).
Evidence grades per `docs/AUDITS/README.md`: GOLD = probed/read at the pin
today; the grep battery itself is GOLD (run on the working tree at the
surveyed commits).

## A. `noncomputable` declarations, one entry each

### A.1 AlgebraicGeometry line (pre-existing on main)

| Declaration | File | Forcing nonconstructivity | Choice-reached mathlib constant | Retro route | Ticket |
|---|---|---|---|---|---|
| `AlgebraicCycle.fiberCycle` | `AlgebraicCycle/FiberCycle.lean:48` | chosen fiber enumeration | `Set.Finite.toFinset`-grade extraction | explicit-data re-parameterization | new RETRO.3 |
| `AlgebraicCycle.genericPointsFinset` | `AlgebraicCycle/FundamentalCycle.lean:38` | `Set.Finite.toFinset` on generic points | `Set.Finite.toFinset` | explicit generic-point data | new RETRO.4 |
| `AlgebraicCycle.fundamentalCycle` | `AlgebraicCycle/FundamentalCycle.lean:52` | generic-points finset extraction | via `genericPointsFinset` | explicit-data re-parameterization | new RETRO.4 |
| `AlgebraicCycle.localDegree` | `AlgebraicCycle/Zero.lean:137` | `Hom.residueDegree = Module.finrank` | `Module.finrank` → `Module.Free.chooseBasis` (CHOICE-TAINTED, GOLD pin-run 2026-10-30) | basis-as-structure (P.1) | RETRO.1 #115 |
| `AlgebraicCycle.degree` | `AlgebraicCycle/Zero.lean:186` | same, summed | same | basis-as-structure (P.1) | RETRO.1 #115 |
| `AlgebraicCycle.pushforward` | `AlgebraicCycle/Pushforward.lean:48` | chosen fiber sums | `Set.Finite.toFinset`-grade | explicit-data | new RETRO.3 |
| `AlgebraicCycle.pushforwardHom` | `AlgebraicCycle/Pushforward.lean:155` | same | same | explicit-data | new RETRO.3 |
| `AlgebraicCycle.mapHom` | `AlgebraicCycle/Map.lean:203` | chosen pullback/fiber data | `Limits.pullback` family (CHOICE-TAINTED, GOLD) | explicit pullback data | RETRO.2 #116 |
| `graph` | `Correspondence/Graph.lean:39` | chosen pullback | `Limits.pullback` | explicit-data decree | RETRO.2 #116 |
| `graphCorrespondence` | `Correspondence/Graph.lean:68` | chosen pullback | `Limits.pullback` | explicit-data decree | RETRO.2 #116 |
| `graphComposite` | `Correspondence/Graph.lean:106` | chosen pullback | `Limits.pullback` | explicit-data decree | RETRO.2 #116 |
| `graphCompositeMap` | `Correspondence/Graph.lean:157` | chosen pullback | `Limits.pullback` | explicit-data decree | RETRO.2 #116 |
| `graphCorrespondenceComposite` | `Correspondence/Graph.lean:249` | chosen pullback | `Limits.pullback` | explicit-data decree | RETRO.2 #116 |
| `fiberBaseChange` | `Fiber/BaseChange.lean:46` | `IsPullback.isoPullback` chosen data | `Limits.pullback` | square-base-change explicit data | RETRO.2 #116 (conformance check) |
| `fiberBaseChangeIso` | `Fiber/BaseChange.lean:91` | same | same | same | RETRO.2 #116 |
| `flat_fiberBaseChange` (instance) | `Fiber/BaseChange.lean:107` | same | same | same | RETRO.2 #116 |
| `fiberComposite` | `Fiber/Composite.lean:40` | limit data | `Limits.pullback` | explicit-data | new RETRO.5 |
| `fiberCompositeIso` | `Fiber/Composite.lean:89` | limit data | `Limits.pullback` | explicit-data | new RETRO.5 |
| `residueFieldAlgebra` (instance) | `ResidueField/Tower.lean:46` | chosen residue-field maps | field-of-fractions / choice-backed algebra instance | explicit residue field structure | new RETRO.6 |
| `residueFieldAlgebra_comp` (instance) | `ResidueField/Tower.lean:56` | same | same | same | new RETRO.6 |

### A.2 CategoryTheory/Sites line (added on `feat/formal-periods-axiom-lint`)

These are the [mathlib]-mirror line: sheafification and chosen limits in
`Sheaf J C` are choice-backed at the pin (GOLD, pin-run 2026-10-30:
`HasLimit`/`HasColimit`/`limit`/`pullback` all `[propext, Classical.choice,
Quot.sound]`). They are flagged `noncomputable` inline per STYLE §2.3 and are
explicitly OUT of the P-line's choice-free law; the P-line never imports
them.

| Declaration | File | Forcing choice |
|---|---|---|
| `pullbackCommuteConstant`, `pushforwardCommuteConstant` | `Sites/ConstantSheafCommute.lean:82,102` | choice-backed sheafification |
| `Sheaf.ΓNatIsoSectionsFunctorPoly`, `Sheaf.ΓNatIsoCoyonedaPoly` | `Sites/GlobalSectionsPoly.lean:85,98` | chosen terminal/limit data |
| `prodWith`, `sheafProdIsoTensor`, `sheafHomCurryTensor`, `sheafHomCurrySection`, `sheafHomCurryVal`, `sheafHomCurry`, `sheafHomUncurry`, `sheafHomProdHomEquiv`, `sheafHomAdjunction`, `sheafTypesMonoidalClosed`, `prodWithIsoTensorLeft`, `sheafHom_iso_internalHom` | `Sites/SheafHomBifunctor.lean` | chosen binary products / chosen sheafification |
| `sheafInternalHom`, `sheafInternalHom_underlying_iso`, `tensorLeft_adj_sheafInternalHom` | `Sites/SheafMonoidalClosed.lean` | chosen sheafification |
| `openCoverSquare` | `Sites/ZariskiMayerVietoris.lean:67` | `Limits.pullback` in `Scheme` |

### A.3 FormalPeriods line (the constructive line)

ZERO `noncomputable` declarations (GOLD grep). Every declaration lints CLEAN
under `#lint_axioms` (see `2026-10-30-axiom-lint-pin-run.md` and the
per-module `#lint_axioms` trailer lines in each module).

## B. Classical-axiom uses in proof terms (grep battery, GOLD)

- `AlgebraicCycle/Map.lean`: `map_single`, `mapCoeff_comp`, `map_comp` —
  `Classical.em` / `open scoped Classical` on point equalities (`decEq` is
  shadowed by `Classical.decEq` under full Mathlib import,
  `Mathlib/Basic/Logic/Basic.lean:785`). Flagged in
  `2026-10-30-choice-audit-own-code.md`; decidable-fixable follow-up.
- `AlgebraicCycle/FiberCycle.lean:126`, `FundamentalCycle.lean:96`,
  `Pushforward.lean:179`: `rcases Classical.em` on point equality.
- Quarantined probes: `probes/AxiomLintProbes.lean` (outside the build glob).
- No `Classical.*` / `by_cases` / `by_contra` in code (only doc comments) in
  any `FormalPeriods/` module, including the in-flight P.2/P.3 modules.

## C. mathlib constants the tree transitively reaches that are CHOICE-TAINTED at the pin (GOLD pin-run, 2026-10-30, plus today's probes)

- Limits family: `HasLimit`, `HasColimit`, `limit`, `colimit`, `kernel`,
  `cokernel`, `HasKernels`, `HasPullbacks`, `pullback`, `HasEqualizers`,
  `equalizer`, `HasFiniteLimits` — `[propext, Classical.choice, Quot.sound]`.
- Basis/finrank: `Module.Free.chooseBasis`, `Module.Free.exists_basis`,
  `Module.Free.of_divisionRing`, and through them `Module.finrank`.
- Linear-algebra import paths: `LinearMap.range`, `Submodule.Quotient.mk`,
  `Finsupp.single`, `DirectSum.of`, `DFinsupp.sum`.
- `Fintype.decidablePiFintype`.
- NEW (probed 2026-10-31, GOLD): `Rat.instField`, `Rat.instDiv`,
  `Rat.div`, `Rat.mul`, `Rat.add` all depend on
  `[propext, Classical.choice, Quot.sound]`; **`Rat.inv` is CLEAN**
  (`[propext, Quot.sound]`), and `Rat.instDecidableLt` depends on no axioms.
  Consequence: the P-line must take division/inversion as explicit data
  (already done: P.2.1's `invK`/`hinv`), and must not call `Rat.add` /
  `Rat.mul` / `Rat.div` by name — the `+`/`*`/`/` instance operations route
  through separate instance constants (probe in flight at survey time;
  the P-line modules lint CLEAN, so whatever they use is clean at the pin).
  Candidate follow-up ticket: a fully constructive `Field ℚ` instance
  replacement (narrow, over `Rat.inv` + instance-level ops).

## D. Sorry inventory (real sorries, comment mentions excluded)

- In-flight on `feat/formal-periods-axiom-lint`: `FormalPeriods/
  ExplicitLimits.lean` (P.3, #95), `DecidableSubspace.lean` (P.2.3, #110),
  `KernelImage.lean` (P.2.2, #109) — grep at survey time shows 0 real sorries
  in all three; verification builds pending.
- On `main` at survey time: 0 real sorries outside the branch (the H.7 and
  P.2.1 sorries were peeled on the branch; see git log).

## E. Retro tickets spawned (acceptance criterion 2)

Entries above with no existing ticket spawn: RETRO.3 (fiber sums /
fiberCycle / pushforward), RETRO.4 (fundamentalCycle generic-point finset),
RETRO.5 (fiber composite/base-change conformance), RETRO.6 (residue-field
tower), RETRO.7 (constructive `Field ℚ` instance over `Rat.inv`), RETRO.8
(`Classical.em` point-equality fixes in AlgebraicCycle). RETRO.1 (#115) and
RETRO.2 (#116) already exist.
