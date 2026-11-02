/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Group.Action.Defs
import BoringMath.FormalPeriods.FreeMod
import BoringMath.FormalPeriods.RowReduction
import BoringMath.FormalPeriods.AxiomLint
import BoringMath.FormalPeriods.KernelImage.Basic
import BoringMath.FormalPeriods.KernelImage.ListSum
import BoringMath.FormalPeriods.KernelImage.MatVec
import BoringMath.FormalPeriods.KernelImage.RowSwap
import BoringMath.FormalPeriods.KernelImage.RowScale
import BoringMath.FormalPeriods.KernelImage.RowElim
import BoringMath.FormalPeriods.KernelImage.Pivots

/-!
# The elimination loop and the RREF preserve `applyMat _ x = 0` (P.2.2, part 8)

Piece 8 of `BoringMath.FormalPeriods.KernelImage`: each `rrefAux` step
preserves the annihilation predicate, hence so do `rrefAux` and `rref`,
and `f x = 0 ↔ applyMat (rref invK (freeModHomMat f)) x = 0`; ends with
the `#lint_axioms` block.
-/

universe u

namespace BoringMath

variable {K : Type u} [Field K] {m n : ℕ}
variable (invK : K → K)

/-! ## The elimination loop preserves the annihilation predicate -/

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6 (one pivot step —
-- swap, scale, eliminate — preserves the solution set); assembled from the
-- three row-operation preservation lemmas and `rrefAux_pivot_some`; same
-- anchor as `rrefAux_applyMat_eq_zero_iff`.
/-- One pivot step of the elimination loop preserves `applyMat _ x = 0`. -/
theorem rrefAux_step_pivot [DecidableEq K]
    (hinv : ∀ a : K, a ≠ 0 → invK a * a = 1) (fuel : ℕ)
    (A : FreeMatrix K n m) (x : FreeMod K m)
    (ih : ∀ (r j : ℕ) (A : FreeMatrix K n m) (x : FreeMod K m),
      applyMat (rrefAux invK fuel r j A) x = 0 ↔ applyMat A x = 0)
    (r j : ℕ) (hr : r < n) (hj : j < m) (i : Fin n)
    (hfp : findPivotRow
        (fun k => Nat.ble r k.val && (if A k ⟨j, hj⟩ ≠ 0 then true else false))
          n r = some i) :
    applyMat (rrefAux invK fuel (r+1) (j+1)
        (matRowElim
          (matRowScale (matRowSwap A ⟨r, hr⟩ i) ⟨r, hr⟩ (invK (A i ⟨j, hj⟩)))
          ⟨r, hr⟩ ⟨j, hj⟩)) x = 0 ↔ applyMat A x = 0 :=
  (ih (r+1) (j+1)
      (matRowElim
        (matRowScale (matRowSwap A ⟨r, hr⟩ i) ⟨r, hr⟩ (invK (A i ⟨j, hj⟩)))
        ⟨r, hr⟩ ⟨j, hj⟩) x).trans
    ((applyMat_rowElim_eq_zero_iff
        (matRowScale (matRowSwap A ⟨r, hr⟩ i) ⟨r, hr⟩ (invK (A i ⟨j, hj⟩)))
        ⟨r, hr⟩ ⟨j, hj⟩ x).trans
      ((applyMat_rowScale_eq_zero_iff invK hinv (matRowSwap A ⟨r, hr⟩ i) ⟨r, hr⟩
          (invK (A i ⟨j, hj⟩)) x
          (invK_ne_zero invK hinv (rrefAux_pivot_some hfp).2)).trans
        (applyMat_rowSwap_eq_zero_iff A ⟨r, hr⟩ i x)))

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6 (the pivot search
-- in a column: either no pivot and the loop advances, or a pivot and one
-- step is taken); same anchor as `rrefAux_applyMat_eq_zero_iff`.
/-- The pivot search at column `j` of the unrolled loop preserves
`applyMat _ x = 0`. -/
theorem rrefAux_step_pivotmatch [DecidableEq K]
    (hinv : ∀ a : K, a ≠ 0 → invK a * a = 1) (fuel : ℕ)
    (ih : ∀ (r j : ℕ) (A : FreeMatrix K n m) (x : FreeMod K m),
      applyMat (rrefAux invK fuel r j A) x = 0 ↔ applyMat A x = 0)
    (r j : ℕ) (hr : r < n) (hj : j < m) (A : FreeMatrix K n m) (x : FreeMod K m) :
    applyMat (match findPivotRow
        (fun k => Nat.ble r k.val && (if A k ⟨j, hj⟩ ≠ 0 then true else false)) n r with
      | none => rrefAux invK fuel r (j+1) A
      | some i =>
          rrefAux invK fuel (r+1) (j+1)
            (matRowElim
              (matRowScale (matRowSwap A ⟨r, hr⟩ i) ⟨r, hr⟩ (invK (A i ⟨j, hj⟩)))
              ⟨r, hr⟩ ⟨j, hj⟩)) x = 0 ↔ applyMat A x = 0 := by
  cases hfp : findPivotRow
      (fun k => Nat.ble r k.val && (if A k ⟨j, hj⟩ ≠ 0 then true else false)) n r with
  | none => exact ih r (j+1) A x
  | some i => exact rrefAux_step_pivot invK hinv fuel A x ih r j hr hj i hfp

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6 (advancing past a
-- column: either the row index is in range and the pivot search runs, or it
-- is out of range and the loop advances); same anchor as
-- `rrefAux_applyMat_eq_zero_iff`.
/-- The inner `dite` of one unrolling of the loop preserves
`applyMat _ x = 0`. -/
theorem rrefAux_step_row [DecidableEq K]
    (hinv : ∀ a : K, a ≠ 0 → invK a * a = 1) (fuel : ℕ)
    (ih : ∀ (r j : ℕ) (A : FreeMatrix K n m) (x : FreeMod K m),
      applyMat (rrefAux invK fuel r j A) x = 0 ↔ applyMat A x = 0)
    (r j : ℕ) (hj : j < m) (A : FreeMatrix K n m) (x : FreeMod K m) :
    applyMat (if hr : r < n then
        match findPivotRow
            (fun k => Nat.ble r k.val && (if A k ⟨j, hj⟩ ≠ 0 then true else false)) n r with
        | none => rrefAux invK fuel r (j+1) A
        | some i =>
            rrefAux invK fuel (r+1) (j+1)
              (matRowElim
                (matRowScale (matRowSwap A ⟨r, hr⟩ i) ⟨r, hr⟩ (invK (A i ⟨j, hj⟩)))
                ⟨r, hr⟩ ⟨j, hj⟩)
      else rrefAux invK fuel r (j+1) A) x = 0 ↔ applyMat A x = 0 := by
  rcases Nat.lt_or_ge r n with hr | hr
  · exact Eq.mpr (congrArg (fun M => applyMat M x = 0 ↔ applyMat A x = 0) (dite_eq_left hr))
      (rrefAux_step_pivotmatch invK hinv fuel ih r j hr hj A x)
  · exact Eq.mpr (congrArg (fun M => applyMat M x = 0 ↔ applyMat A x = 0)
        (dite_eq_right (not_lt.mpr hr))) (ih r (j+1) A x)

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6 (advancing past a
-- column with `j` in range); same anchor as `rrefAux_applyMat_eq_zero_iff`.
/-- One unrolling of the loop at a column `j < m` preserves
`applyMat _ x = 0`. -/
theorem rrefAux_step_col [DecidableEq K]
    (hinv : ∀ a : K, a ≠ 0 → invK a * a = 1) (fuel : ℕ)
    (ih : ∀ (r j : ℕ) (A : FreeMatrix K n m) (x : FreeMod K m),
      applyMat (rrefAux invK fuel r j A) x = 0 ↔ applyMat A x = 0)
    (r j : ℕ) (hj : j < m) (A : FreeMatrix K n m) (x : FreeMod K m) :
    applyMat (rrefAux invK (fuel+1) r j A) x = 0 ↔ applyMat A x = 0 :=
  Eq.mpr (congrArg (fun M => applyMat M x = 0 ↔ applyMat A x = 0)
      ((rrefAux_fuel_succ invK A fuel r j).trans (dite_eq_left hj)))
    (rrefAux_step_row invK hinv fuel ih r j hj A x)

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6 (once the column
-- index has passed the last column the loop returns `A`); same anchor as
-- `rrefAux_applyMat_eq_zero_iff`.
/-- One unrolling of the loop past the last column preserves
`applyMat _ x = 0`. -/
theorem rrefAux_step_done [DecidableEq K] (fuel : ℕ)
    (r j : ℕ) (hj : m ≤ j) (A : FreeMatrix K n m) (x : FreeMod K m) :
    applyMat (rrefAux invK (fuel+1) r j A) x = 0 ↔ applyMat A x = 0 :=
  Eq.mpr (congrArg (fun M => applyMat M x = 0 ↔ applyMat A x = 0)
      ((rrefAux_fuel_succ invK A fuel r j).trans (dite_eq_right (not_lt.mpr hj))))
    (Iff.refl _)

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6 (the elimination
-- loop preserves the solution set); induction on the fuel, using the three
-- row-operation preservation lemmas above and `rrefAux_pivot_some`.
/-- The elimination loop preserves `applyMat _ x = 0`. -/
theorem rrefAux_applyMat_eq_zero_iff [DecidableEq K]
    (hinv : ∀ a : K, a ≠ 0 → invK a * a = 1) (fuel : ℕ) :
    ∀ (r j : ℕ) (A : FreeMatrix K n m) (x : FreeMod K m),
      applyMat (rrefAux invK fuel r j A) x = 0 ↔ applyMat A x = 0 := by
  induction fuel with
  | zero =>
      intro r j A x
      exact Eq.mpr (congrArg (fun M => applyMat M x = 0 ↔ applyMat A x = 0)
        (rrefAux_fuel_zero invK A r j)) (Iff.refl _)
  | succ fuel ih =>
      intro r j A x
      rcases Nat.lt_or_ge j m with hj | hj
      · exact rrefAux_step_col invK hinv fuel ih r j hj A x
      · exact rrefAux_step_done invK fuel r j hj A x

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6 (Gaussian
-- elimination preserves the solution set of `A x = 0`).
/-- The RREF of `A` has the same solutions as `A`. -/
theorem rref_applyMat_eq_zero_iff [DecidableEq K]
    (hinv : ∀ a : K, a ≠ 0 → invK a * a = 1) (A : FreeMatrix K n m) (x : FreeMod K m) :
    applyMat (rref invK A) x = 0 ↔ applyMat A x = 0 :=
  rrefAux_applyMat_eq_zero_iff invK hinv (m+1) 0 0 A x

-- Reference: issue #109 (kernel membership iff annihilation), assembled
-- from `freeModHom_apply_eq_applyMat` and `rref_applyMat_eq_zero_iff`.
/-- Annihilation by `f` is the same as annihilation by the RREF of its
matrix. -/
theorem freeModHom_apply_eq_zero_iff [DecidableEq K]
    (hinv : ∀ a : K, a ≠ 0 → invK a * a = 1) (f : FreeModHom K m n) (x : FreeMod K m) :
    f.toFun x = 0 ↔ applyMat (rref invK (freeModHomMat f)) x = 0 :=
  ⟨fun h => (rref_applyMat_eq_zero_iff invK hinv (freeModHomMat f) x).mpr
      (Eq.trans (freeModHom_apply_eq_applyMat f x).symm h),
    fun h => Eq.trans (freeModHom_apply_eq_applyMat f x)
      ((rref_applyMat_eq_zero_iff invK hinv (freeModHomMat f) x).mp h)⟩

/-! ## Axiom lint -/

#lint_axioms BoringMath.stdBasisVec
#lint_axioms BoringMath.stdBasisVec_apply
#lint_axioms BoringMath.stdBasisVec_self
#lint_axioms BoringMath.stdBasisVec_ne
#lint_axioms BoringMath.freeModHomMat
#lint_axioms BoringMath.applyMat
#lint_axioms BoringMath.applyMat_apply
#lint_axioms BoringMath.applyMat_eq_listSum
#lint_axioms BoringMath.rowIsZeroBool
#lint_axioms BoringMath.pivotRowOfCol
#lint_axioms BoringMath.pivotColBool
#lint_axioms BoringMath.kernelVec
#lint_axioms BoringMath.kernelVec_self
#lint_axioms BoringMath.kernelVec_pivot
#lint_axioms BoringMath.kernelVec_other
#lint_axioms BoringMath.pivotCols
#lint_axioms BoringMath.nonPivotCols
#lint_axioms BoringMath.kernelBasis
#lint_axioms BoringMath.imageBasis
#lint_axioms BoringMath.rankOf
#lint_axioms BoringMath.nullityOf
#lint_axioms BoringMath.list_sum_map_add
#lint_axioms BoringMath.list_sum_map_neg
#lint_axioms BoringMath.list_sum_map_mul_left
#lint_axioms BoringMath.list_sum_map_sub
#lint_axioms BoringMath.list_sum_map_apply
#lint_axioms BoringMath.list_sum_map_congr_mem
#lint_axioms BoringMath.list_sum_eq_zero_of_forall_mem
#lint_axioms BoringMath.list_sum_ite_eq_zero_of_not_mem
#lint_axioms BoringMath.list_sum_ite_eq_of_mem_nodup
#lint_axioms BoringMath.eq_masked_of_mem_of_not_mem
#lint_axioms BoringMath.list_sum_split
#lint_axioms BoringMath.freeModHom_map_zero
#lint_axioms BoringMath.freeModHom_map_listSum
#lint_axioms BoringMath.smul_stdBasisVec_apply_eq
#lint_axioms BoringMath.smul_stdBasisVec_apply_ne
#lint_axioms BoringMath.smul_stdBasisVec_apply
#lint_axioms BoringMath.eq_listSum_stdBasisVec
#lint_axioms BoringMath.freeModHom_smul_stdBasisVec_apply
#lint_axioms BoringMath.freeModHom_apply_eq_applyMat
#lint_axioms BoringMath.applyMat_rowSwap_apply
#lint_axioms BoringMath.applyMat_eq_zero_of_rowSwap_eq_zero_r
#lint_axioms BoringMath.applyMat_eq_zero_of_rowSwap_eq_zero_i
#lint_axioms BoringMath.applyMat_eq_zero_of_rowSwap_eq_zero_other
#lint_axioms BoringMath.applyMat_eq_zero_of_rowSwap_eq_zero_at
#lint_axioms BoringMath.applyMat_eq_zero_of_rowSwap_eq_zero
#lint_axioms BoringMath.applyMat_rowSwap_eq_zero_at
#lint_axioms BoringMath.applyMat_rowSwap_eq_zero_of_eq_zero
#lint_axioms BoringMath.applyMat_rowSwap_eq_zero_iff
#lint_axioms BoringMath.applyMat_rowScale_apply
#lint_axioms BoringMath.eq_zero_of_mul_eq_zero_of_ne_zero
#lint_axioms BoringMath.applyMat_eq_zero_of_rowScale_eq_zero_r
#lint_axioms BoringMath.applyMat_eq_zero_of_rowScale_eq_zero_other
#lint_axioms BoringMath.applyMat_eq_zero_of_rowScale_eq_zero_at
#lint_axioms BoringMath.applyMat_eq_zero_of_rowScale_eq_zero
#lint_axioms BoringMath.applyMat_rowScale_eq_zero_of_eq_zero
#lint_axioms BoringMath.applyMat_rowScale_eq_zero_iff
#lint_axioms BoringMath.applyMat_rowElim_self
#lint_axioms BoringMath.matRowElim_mul_apply
#lint_axioms BoringMath.applyMat_rowElim_other
#lint_axioms BoringMath.applyMat_eq_zero_of_rowElim_eq_zero
#lint_axioms BoringMath.applyMat_rowElim_eq_zero_of_eq_zero
#lint_axioms BoringMath.applyMat_rowElim_eq_zero_iff
#lint_axioms BoringMath.invK_ne_zero
#lint_axioms BoringMath.rrefAux_step_pivot
#lint_axioms BoringMath.rrefAux_step_pivotmatch
#lint_axioms BoringMath.rrefAux_step_row
#lint_axioms BoringMath.rrefAux_step_col
#lint_axioms BoringMath.rrefAux_step_done
#lint_axioms BoringMath.rrefAux_applyMat_eq_zero_iff
#lint_axioms BoringMath.rref_applyMat_eq_zero_iff
#lint_axioms BoringMath.freeModHom_apply_eq_zero_iff

end BoringMath
