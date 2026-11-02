/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Init
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
# The axiom lint: a three-grade decision on top of `#print axioms`

This module is the core of the choice-free proof lint (ticket P.0.1, leaf
of P.0): for one named declaration it collects the axioms its proof term
depends on (`Lean.collectAxioms`, the engine behind `#print axioms`) and
returns a single grade:

* `AxiomGrade.cleanGrade` — the axiom set is contained in `{propext, Quot.sound}`;
* `AxiomGrade.sorryTainted` — the proof term reaches `sorryAx`
  (conjecture-dependent, honest);
* `AxiomGrade.choiceTainted` — the proof term reaches `Classical.choice`
  (classical contamination; by Diaconescu's theorem one lint on
  `Classical.choice` also enforces the ban on `Classical.em`/LEM);
* `AxiomGrade.banned` — the proof term reaches `Lean.ofReduceBool`
  (`native_decide`, banned outright for kernel soundness) or a
  user-declared `axiom` (a minted witness).

Grades are assigned with the precedence `banned` > `sorryTainted` >
`choiceTainted` > `cleanGrade`: a declaration is only as strong as its worst
grade. The command `#lint_axioms <name>` prints the grade and the axiom
set, and raises an error on `banned` declarations so the lint is usable as
a gate.

## References
* R. Diaconescu, *Axiom of Choice and Complementation*, Proc. Amer. Math.
  Soc. 51 (1975), 176–178 — the routing `Classical.choice ⟹ Classical.em`
  that makes the single choice-lint enforce both bans.
* The `#print axioms` implementation, `Lean.Elab.Print` (Lean 4 core), for
  `Lean.collectAxioms`.
* Mathlib's `Mathlib/Util/AssertNoSorry.lean` — the `assert_no_sorry`
  command this lint generalizes.
-/

namespace BoringMath

open Lean Elab Command

-- Reference: the axioms of Lean's kernel (`propext`, `Quot.sound`,
-- `Classical.choice`); at the pin v4.35.0-rc3 `native_decide` additionally
-- mints a per-declaration axiom `<decl>._native.native_decide.ax_…`.
/-- The axioms built into Lean itself: the two proof-irrelevant/quotient
axioms and the classical choice axiom. Any other axiom — `sorryAx`
(handled separately by the grader), a `native_decide` minted axiom, or a
user-declared `axiom` — is not built in. -/
def builtinAxioms : Array Name :=
  #[``propext, ``Quot.sound, ``Classical.choice]

-- Reference: program notes §§169–172 (the choice-free / LEM-free law,
-- 2026-10-30) and Diaconescu 1975 (choice ⟹ LEM routing).
/-- The grade of a declaration under the axiom lint: `cleanGrade` (only
`propext`/`Quot.sound`), `sorryTainted` (reaches `sorryAx`),
`choiceTainted` (reaches `Classical.choice`), or `banned` (reaches
`Lean.ofReduceBool` or a user-declared axiom). -/
inductive AxiomGrade
  | cleanGrade
  | sorryTainted
  | choiceTainted
  | banned
  deriving DecidableEq

-- Reference: program notes §§169–172 (the three-grade decision, 2026-10-30).
/-- The three-grade decision on an axiom set, with precedence
`banned` > `sorryTainted` > `choiceTainted` > `cleanGrade`: any non-builtin axiom
other than `sorryAx` (a `native_decide` minted axiom or a user-declared
`axiom`) bans the declaration outright; otherwise `sorryAx` taints it as
conjecture-dependent; otherwise `Classical.choice` taints it as
classically contaminated; otherwise the declaration is clean. -/
def AxiomGrade.ofAxioms (axioms : Array Name) : AxiomGrade :=
  if axioms.any (fun a => a != ``sorryAx && !builtinAxioms.contains a) then .banned
  else if axioms.contains ``sorryAx then .sorryTainted
  else if axioms.contains ``Classical.choice then .choiceTainted
  else .cleanGrade

-- Reference: `Lean.Elab.Print`'s `#print axioms` (Lean 4 core).
/-- Lint one declaration: collect the axioms its proof term depends on and
grade them. -/
def lintAxioms (n : Name) : CoreM AxiomGrade := do
  return AxiomGrade.ofAxioms (← Lean.collectAxioms n)

-- Reference: Mathlib's `assert_no_sorry` command (`Mathlib/Util/AssertNoSorry.lean`),
-- generalized to the three grades of program notes §§169–172.
/-- `#lint_axioms foo` prints the axiom grade of `foo` together with its
axiom set, and raises an error if the grade is `banned`. -/
elab "#lint_axioms " n:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo n
  let axioms ← Lean.collectAxioms name
  let grade := AxiomGrade.ofAxioms axioms
  let gradeStr := match grade with
    | .cleanGrade => "CLEAN"
    | .sorryTainted => "sorryTainted"
    | .choiceTainted => "choiceTainted"
    | .banned => "banned"
  logInfo m!"{n} : {gradeStr}
axioms: {axioms.map toString}"
  if grade == .banned then
    throwError "{n} is BANNED: reaches a minted native-decision axiom or a user-declared axiom"

end BoringMath
