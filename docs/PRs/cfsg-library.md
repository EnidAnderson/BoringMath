# Candidate PR note: the CFSG library (`BoringMath/GroupTheory/CFSG/`)

Tracking: #236 (CFSG.LIB), roadmap `docs/CFSG-ROADMAP.md`, bibliography
`docs/CFSG-BIBLIOGRAPHY.md`.

## What it is
The modular group-theory library supporting the classification of finite
simple groups (and, via the consumption map #260, the simple-mixed-motives
classification). Each module is mathlib-shaped: targeted imports, license
header, `Reference:` lines, boring style, no sorries except sanctioned ones
with peeling plans.

## Modules landed (branch feat/formal-periods-axiom-lint)
- `Quasisimple.lean` — `IsQuasisimpleGroup`; `IsPerfect.of_surjective` (proved);
  `alternatingGroup_isPerfect` (consumed).
- `Signalizer.lean` — `SignalizerFunctor` structure (4 axioms).
- `ThompsonSubgroup.lean` — `IsMaximalAbelian`, `thompsonSubgroup J(P)`,
  `thompsonSubgroup_le`, `IsMaximalAbelian.map`, `map_thompsonSubgroup` (all proved).
- `Fusion.lean` — `IsConjHom` + injectivity (proved).
- `FusionSystem.lean` — `fusionHom` + id/comp closure (proved).
- `ThreeTransposition.lean` — `ThreeTranspositionGroup` + order-2 lemma (proved).
- `AlmostSimple.lean` — `IsAlmostSimpleGroup` + nontrivial (proved).
- `PCore.lean` — `oCore` (`O_p(G)`); normal + `le_oCore` proved;
  `oCore_isPGroup` sanctioned sorry with peeling plan.
- `StronglyClosed.lean` — `StronglyClosed` + self lemma (proved).
- `Local.lean` — `localSubgroup` (= normalizer) + `le_localSubgroup` (proved).
- `Centralizer.lean` — `centralizer_anti` (proved).
- Plus `Simple/Classification.lean` (sectors + PSL cardinality + exceptions) and
  `Simple/LieAlgebraBridge.lean`, `Simple/SmallOrders.lean`.

## Where it would live in mathlib
`Mathlib/GroupTheory/` — e.g. `Mathlib/GroupTheory/Quasisimple.lean`,
`Mathlib/GroupTheory/Signalizer.lean`, `Mathlib/GroupTheory/FusionSystem.lean`,
`Mathlib/GroupTheory/ThompsonSubgroup.lean`, `Mathlib/GroupTheory/PCore.lean`,
etc. (none of these exist at the pin).

## Status
Full `lake build` green (3812 jobs, EXIT=0); check-style 0 violations; only
sanctioned sorries remain. Not submitted anywhere (per repo rules).
