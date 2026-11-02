# Own-code audit: noncomputable / classical-axiom / sorry inventory (2026-10-30)

Scope: everything under `BoringMath/` and `probes/` on branch
`feat/formal-periods-axiom-lint`, grepped 2026-10-30, cross-checked with
`#lint_axioms` where relevant. The P-line (FormalPeriods) is held to the
choice-free law (2026-10-30 ruling); the [mathlib]-mirror line carries
flagged `noncomputable` only where the content forces it (STYLE §2.3).

## 1. `Classical.em` / `open scoped Classical` in proof terms

Attempted this session, reverted after investigation: `Map.lean`'s
`map_single` (`z = f.base x`) and `mapCoeff_comp` (`wx x = wz ((g ≫ h).base x)`)
use `Classical.em` on decidable-by-hypothesis propositions. Replacing them
with `decEq` fails in this file because `decEq` is shadowed by
`Classical.decEq` (`Mathlib/Basic/Logic/Basic.lean:785`) under the full
Mathlib import. Left as-is (flagged); the tree-wide extension of the
choice-free law is a human call.

Still present (flagged, not silently edited):

- `AlgebraicGeometry/AlgebraicCycle/Map.lean` — `map_single`,
  `mapCoeff_comp`, `map_comp` (the last needs `open scoped Classical` for
  fiber filters; adding `[DecidableEq ↥Y]` would weaken the statement)
- `AlgebraicGeometry/AlgebraicCycle/FiberCycle.lean:126`
- `AlgebraicGeometry/AlgebraicCycle/FundamentalCycle.lean:96`
- `AlgebraicGeometry/AlgebraicCycle/Pushforward.lean:179`

Each is a `rcases Classical.em` on a point-equality; all three sit under
`[DecidableEq]`-bearing hypotheses in spirit (point equality of the fiber
finsets) and look decidable-fixable the same way as the Map.lean fixes —
recommend a follow-up ticket.

Deliberate and quarantined: `probes/AxiomLintProbes.lean` (`probeClassicalEm`,
`probeAxiom`) — outside the build glob, exist only to be linted.

## 2. `noncomputable` inventory

All carry inline comments naming the forcing choice (STYLE §2.3). None in
`BoringMath/FormalPeriods/` (the constructive line is fully computable):

- AlgebraicCycle: `fiberCycle`, `fundamentalCycle`/`genericPointsFinset`,
  `localDegree`, `degree`, `pushforward`, `pushforwardHom`, `mapHom` —
  choice-backed fiber sums / point enumeration.
- Correspondence/Graph: `graph`, `graphCorrespondence`, `graphComposite`,
  `graphCompositeMap`, `graphCorrespondenceComposite` — chosen pullback.
- Fiber: `fiberBaseChange`, `fiberBaseChangeIso`, `flat_fiberBaseChange`,
  `fiberComposite`, `fiberCompositeIso` — limit data.
- ResidueField/Tower: `residueFieldAlgebra`, `residueFieldAlgebra_comp`.
- Sites/SheafHomBifunctor (this branch): `prodWith`, `sheafHomAdjunction`,
  `sheafTypesMonoidalClosed`, `sheafHom_iso_internalHom` — chosen products
  / chosen sheafification.
- Sites/ZariskiMayerVietoris (this branch): `openCoverSquare` —
  `Limits.pullback` in `Scheme` is choice-backed (confirmed by lint).

## 3. Sorry inventory (real sorries, not comment mentions)

- `CategoryTheory/Sites/SheafHomBifunctor.lean` — 14, each with a PEELING
  PLAN (H.7, #41); a dedicated peel is in progress.
- `FormalPeriods/RowReduction.lean` — 1 (`rrefState_step_pivot`, plan
  inlined; P.2.1, #108); a dedicated peel is in progress.
- `probes/AxiomLintProbes.lean` — 1 deliberate probe sorry (quarantined).

## 4. Pin findings recorded this session

- `Rat.instField` is CHOICE-TAINTED at v4.35.0-rc3 (P.1.2 smoke work).
- The `Field` `⁻¹` path (`CommGroupWithZero.toDivisionCommMonoid`) reaches
  `Classical.choice` (P.2.1); inversion taken as explicit data there.
- `Fintype.decidablePiFintype` and `Finsupp.single` are CHOICE-TAINTED;
  both were rebuilt constructively in FormalPeriods.
- `native_decide` mints per-declaration axioms `<decl>._native.native_decide.ax_…`
  — auto-banned by the lint's non-builtin-axiom rule.
- mathlib chosen-limits family (`HasLimit`/`pullback`/`equalizer`/
  `HasFiniteLimits`/`kernel`/`cokernel`) and `Module.Free.chooseBasis` are
  CHOICE-TAINTED — see `2026-10-30-axiom-lint-pin-run.md`.
