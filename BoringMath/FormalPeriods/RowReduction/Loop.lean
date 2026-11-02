/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Init
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Fin.Basic
import BoringMath.FormalPeriods.RowReduction.RowOps
import BoringMath.FormalPeriods.RowReduction.PivotSearch

/-!
# The elimination loop and its termination measure (P.2.1, part 3)

Part 3 of `BoringMath.FormalPeriods.RowReduction`: the fuel-indexed
Gaussian-elimination loop `rrefAux`, its termination measure
`colMeasure`, and the entry point `rref`.
-/

universe u

namespace BoringMath

variable {K : Type u} [Field K] {m n : ℕ}
variable (invK : K → K)
variable [DecidableEq K]

/-! ## The elimination loop and its termination measure -/

-- Reference: Mines–Richman–Ruitenburg 2008, Pt. II Ch. 6 (the measure for
-- termination of Gaussian elimination: columns remaining).
/-- The termination measure of the elimination loop: the number of columns
strictly right of the current column `j`. Each recursive call decreases it
by exactly one (`colMeasure_step`), so `n + 1` units of fuel suffice. -/
def colMeasure (n j : ℕ) : ℕ := n - j

-- Reference: core `Nat.sub_succ_lt_self`; the measure peel.
/-- One loop step decreases the measure. -/
theorem colMeasure_step {n j : ℕ} (h : j < n) :
    colMeasure n (j+1) < colMeasure n j :=
  Nat.sub_succ_lt_self n j h

-- Reference: Mines–Richman–Ruitenburg 2008, Pt. II Ch. 6 (Gaussian
-- elimination, left to right by columns).
/-- One pass of Gaussian elimination, structurally recursive on the fuel
`fuel`: at state `(r, j, A)`, with `r` the next free row and `j` the
current column, find a pivot in column `j` at or below row `r`; if there
is one, swap it into row `r`, scale the pivot to `1`, clear the column,
and continue at `(r+1, j+1)`; otherwise just advance to column `j+1`.
Each recursive call consumes one column (`colMeasure_step`), so fuel
`n+1` always suffices. -/
def rrefAux (invK : K → K) : ℕ → ℕ → ℕ → FreeMatrix K m n → FreeMatrix K m n
  | 0, _, _, A => A
  | fuel+1, r, j, A =>
      if hj : j < n then
        if hr : r < m then
          match findPivotRow
              (fun i => Nat.ble r i.val && (if A i ⟨j, hj⟩ ≠ 0 then true else false)) m r with
          | none => rrefAux invK fuel r (j+1) A
          | some i =>
              rrefAux invK fuel (r+1) (j+1)
                (matRowElim
                  (matRowScale (matRowSwap A ⟨r, hr⟩ i) ⟨r, hr⟩ (invK (A i ⟨j, hj⟩)))
                  ⟨r, hr⟩ ⟨j, hj⟩)
        else rrefAux invK fuel r (j+1) A
      else A

-- Reference: definitional peel of `rrefAux` at fuel `0`.
/-- With no fuel left, the loop stops. -/
theorem rrefAux_fuel_zero (A : FreeMatrix K m n) (r j : ℕ) :
    rrefAux invK 0 r j A = A :=
  rfl

-- Reference: definitional peel of `rrefAux` at fuel `fuel+1`.
/-- One unrolling of the elimination loop. -/
theorem rrefAux_fuel_succ (A : FreeMatrix K m n) (fuel r j : ℕ) :
    rrefAux invK (fuel+1) r j A =
      (if hj : j < n then
        if hr : r < m then
          match findPivotRow
              (fun i => Nat.ble r i.val && (if A i ⟨j, hj⟩ ≠ 0 then true else false)) m r with
          | none => rrefAux invK fuel r (j+1) A
          | some i =>
              rrefAux invK fuel (r+1) (j+1)
                (matRowElim
                  (matRowScale (matRowSwap A ⟨r, hr⟩ i) ⟨r, hr⟩ (invK (A i ⟨j, hj⟩)))
                  ⟨r, hr⟩ ⟨j, hj⟩)
        else rrefAux invK fuel r (j+1) A
      else A) :=
  rfl

-- Reference: Mines–Richman–Ruitenburg 2008, Pt. II Ch. 6.
/-- Once the column index has passed the last column, the loop returns the
matrix unchanged. -/
theorem rrefAux_of_column_done (A : FreeMatrix K m n) (fuel r j : ℕ) (h : n ≤ j) :
    rrefAux invK fuel r j A = A := by
  induction fuel with
  | zero => exact rrefAux_fuel_zero invK A r j
  | succ fuel ih =>
      -- `rrefAux invK (fuel+1) r j A` is definitionally the `dite` below.
      change (if hj : j < n then _ else A) = A
      exact dite_eq_right (Nat.not_lt.mpr h)

-- Reference: Mines–Richman–Ruitenburg 2008, Pt. II Ch. 6.
/-- Gaussian elimination: the reduced row-echelon normal form of `A`,
computed with `n+1` units of fuel (enough by `colMeasure_step`). -/
def rref (invK : K → K) (A : FreeMatrix K m n) : FreeMatrix K m n :=
  rrefAux invK (n+1) 0 0 A

