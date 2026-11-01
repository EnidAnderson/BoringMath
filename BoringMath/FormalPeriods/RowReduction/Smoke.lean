/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Init
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Field.Rat
import Mathlib.Data.Fin.Basic
import BoringMath.FormalPeriods.AxiomLint
import BoringMath.FormalPeriods.RowReduction.RowOps
import BoringMath.FormalPeriods.RowReduction.PivotSearch
import BoringMath.FormalPeriods.RowReduction.Loop
import BoringMath.FormalPeriods.RowReduction.Predicates
import BoringMath.FormalPeriods.RowReduction.Invariant
import BoringMath.FormalPeriods.RowReduction.StepPivot
import BoringMath.FormalPeriods.RowReduction.Correctness

/-!
# Smoke test and axiom lint (P.2.1, part 8)

Part 8 of `BoringMath.FormalPeriods.RowReduction`: the concrete 3×3
`#eval` smoke test over `ℚ` and the `#lint_axioms` block.
-/

universe u

namespace BoringMath

variable {K : Type u} [Field K] {m n : ℕ}

/-! ## Smoke test on a concrete 3×3 matrix over `ℚ` -/

-- Reference: smoke test for the P.2.1 acceptance criterion (issue #108).
/-- A concrete 3×3 matrix over `ℚ`: rows `(2,4,6)`, `(1,3,5)`, `(0,1,4)`. -/
def smokeMat : Fin 3 → Fin 3 → ℚ := fun i j =>
  match i.val, j.val with
  | 0, 0 => (2 : ℚ) | 0, 1 => (4 : ℚ) | 0, 2 => (6 : ℚ)
  | 1, 0 => (1 : ℚ) | 1, 1 => (3 : ℚ) | 1, 2 => (5 : ℚ)
  | 2, 0 => (0 : ℚ) | 2, 1 => (1 : ℚ) | 2, 2 => (4 : ℚ)
  | _, _ => (0 : ℚ)

-- Reference: display helper for the smoke test (issue #108).
/-- The rows of a matrix as lists, for `#eval`/`rfl` display. -/
def matToLists (A : FreeMatrix K m n) : List (List K) :=
  (List.finRange m).map (fun i => (List.finRange n).map (fun j => A i j))

#eval matToLists smokeMat
#eval matToLists (rref (K := ℚ) (fun a => a⁻¹) smokeMat)

-- Reference: smoke test for the P.2.1 acceptance criterion (issue #108):
-- `decide`-evaluable means the term computes. The `decide` *tactic* is
-- banned by style, so the computation is demonstrated by the two `#eval`
-- displays above: the input `[[2, 4, 6], [1, 3, 5], [0, 1, 4]]` and its
-- reduced row-echelon normal form `[[1, 0, 0], [0, 1, 0], [0, 0, 1]]`.
-- (A kernel `rfl` cannot fire on `ℚ` arithmetic only because Lean core
-- marks `Rat.mul`/`Rat.inv` `@[irreducible]` — not because of this module.)

/-! ## Axiom lint -/

#lint_axioms BoringMath.FreeMatrix
#lint_axioms BoringMath.matRowSwap
#lint_axioms BoringMath.matRowScale
#lint_axioms BoringMath.matRowElim
#lint_axioms BoringMath.matRowSwap_apply
#lint_axioms BoringMath.matRowSwap_left
#lint_axioms BoringMath.matRowSwap_right
#lint_axioms BoringMath.matRowSwap_other
#lint_axioms BoringMath.matRowSwap_diag
#lint_axioms BoringMath.matRowScale_self
#lint_axioms BoringMath.matRowScale_other
#lint_axioms BoringMath.matRowElim_self
#lint_axioms BoringMath.matRowElim_other
#lint_axioms BoringMath.matRowElim_pivot_zero
#lint_axioms BoringMath.rrefStep_pivot_one
#lint_axioms BoringMath.findPivotRow
#lint_axioms BoringMath.findPivotRow_zero
#lint_axioms BoringMath.findPivotRow_succ
#lint_axioms BoringMath.findPivotRow_some_spec
#lint_axioms BoringMath.findPivotRow_none_spec
#lint_axioms BoringMath.findPivotRow_eq_none_of
#lint_axioms BoringMath.colMeasure
#lint_axioms BoringMath.colMeasure_step
#lint_axioms BoringMath.rrefAux
#lint_axioms BoringMath.rrefAux_fuel_zero
#lint_axioms BoringMath.rrefAux_fuel_succ
#lint_axioms BoringMath.rrefAux_of_column_done
#lint_axioms BoringMath.rref
#lint_axioms BoringMath.matRowZero
#lint_axioms BoringMath.matLeadingCol
#lint_axioms BoringMath.matLeadingCol_eq_of_rowZero
#lint_axioms BoringMath.IsRref
#lint_axioms BoringMath.RrefState
#lint_axioms BoringMath.rrefState_zero
#lint_axioms BoringMath.rrefState_isRref_of_done
#lint_axioms BoringMath.pivotBool_true
#lint_axioms BoringMath.pivotBool_false
#lint_axioms BoringMath.ne_zero_of_pivotBool
#lint_axioms BoringMath.eq_zero_of_pivotBool
#lint_axioms BoringMath.rrefAux_pivot_some
#lint_axioms BoringMath.rrefAux_pivot_none
#lint_axioms BoringMath.rrefState_step_none
#lint_axioms BoringMath.findPivotRow_eq_some_of_first
#lint_axioms BoringMath.findPivotRow_congr_before
#lint_axioms BoringMath.matLeadingCol_eq_some
#lint_axioms BoringMath.matLeadingCol_eq_none
#lint_axioms BoringMath.matLeadingCol_some_of_lt
#lint_axioms BoringMath.matLeadingCol_eq_of_agree_before
#lint_axioms BoringMath.matLeadingCol_eq_of_zero_before
#lint_axioms BoringMath.rrefStep_swap_scale_self
#lint_axioms BoringMath.rrefStepMat_pivot_row_before
#lint_axioms BoringMath.rrefStepMat_pivot_row_at
#lint_axioms BoringMath.rrefStepMat_off_pivot_before
#lint_axioms BoringMath.rrefState_step_pivot
#lint_axioms BoringMath.rrefAux_state
#lint_axioms BoringMath.rref_isRref
#lint_axioms BoringMath.smokeMat
#lint_axioms BoringMath.matToLists

end BoringMath
