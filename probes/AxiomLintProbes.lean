/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
-- Quarantined taint probes for the axiom lint (ticket P.0.2). This file is
-- NOT part of the library build (it lives outside the `BoringMath.+` glob);
-- it is run by hand with `lake env lean probes/AxiomLintProbes.lean` after
-- `lake build BoringMath.FormalPeriods.AxiomLint`.
import BoringMath.FormalPeriods.AxiomLint

/-!
# Taint probes

Three deliberate probes, one per non-clean grade plus the ban check, and one
clean control. Expected lint output:

* `probeSorry` — SORRY-TAINTED (`sorryAx`);
* `probeClassicalEm` — CHOICE-TAINTED, with `Classical.choice` visible in
  the axiom set (the Diaconescu routing: `Classical.em` is proved from
  `Classical.choice`, so the one lint enforces both bans);
* `probeAxiom` — BANNED (a user-declared `axiom`), and `#lint_axioms` raises
  an error on it;
* `probeClean` — CLEAN, and the lint's own declarations lint clean.

## References
* R. Diaconescu, *Axiom of Choice and Complementation*, Proc. Amer. Math.
  Soc. 51 (1975), 176–178.
* Program notes §§169–172 (the three-grade lint, 2026-10-30).
-/

-- Reference: program notes §169.1b (the sorry grade; `sorryAx` dependency).
/-- Probe (a): a deliberate `sorry` must lint SORRY-TAINTED. -/
theorem probeSorry : 1 = 1 := by
  -- TEMPORARY SORRY: deliberate taint probe, never part of a real proof.
  -- PEELING PLAN: none — the probe exists only to be linted.
  sorry

-- Reference: Diaconescu 1975 (choice ⟹ excluded middle routing).
/-- Probe (b): `Classical.em` must lint CHOICE-TAINTED, with
`Classical.choice` visible in the collected axiom set. -/
theorem probeClassicalEm (p : Prop) : p ∨ ¬p :=
  Classical.em p

-- Reference: program notes §169 (minted witnesses are banned outright).
/-- Probe (c): a user-declared axiom must be BANNED by the lint. -/
axiom probeAxiom : True

-- Reference: control probe — a definitional proof must lint CLEAN.
/-- Probe (d): the clean control. -/
theorem probeClean : 1 + 1 = 2 := rfl

#lint_axioms probeSorry
#lint_axioms probeClassicalEm
#lint_axioms probeAxiom
#lint_axioms probeClean
#lint_axioms BoringMath.AxiomGrade.ofAxioms
#lint_axioms BoringMath.lintAxioms
