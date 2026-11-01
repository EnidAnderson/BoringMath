/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Init
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Fin.Basic
import BoringMath.FormalPeriods.RowReduction.Loop
import BoringMath.FormalPeriods.RowReduction.Predicates
import BoringMath.FormalPeriods.RowReduction.Invariant
import BoringMath.FormalPeriods.RowReduction.StepPivot

/-!
# Correctness of Gaussian elimination (P.2.1, part 7)

Part 7 of `BoringMath.FormalPeriods.RowReduction`: the invariant
induction `rrefAux_state` and the correctness theorem `rref_isRref`.
-/

universe u

namespace BoringMath

variable {K : Type u} [Field K] {m n : ℕ}
variable (invK : K → K)
variable [DecidableEq K]

-- Reference: Mines–Richman–Ruitenburg 2008, Pt. II Ch. 6 (the induction on
-- the loop); Hörmann arXiv:2106.03803 Remark 3.3 (program context).
/-- The main invariant induction of the elimination loop: from a state
`(r, j, A)` satisfying `RrefState`, with enough fuel, the loop output is
in reduced row-echelon form. -/
theorem rrefAux_state (hinv : ∀ a : K, a ≠ 0 → invK a * a = 1) {fuel r j : ℕ}
    {A : FreeMatrix K m n} (hs : RrefState r j A)
    (hr : r ≤ m) (hfuel : n ≤ j + fuel) :
    IsRref (rrefAux invK fuel r j A) := by
  induction fuel generalizing r j A with
  | zero => exact rrefState_isRref_of_done hfuel hs
  | succ fuel ih =>
      -- Former rw [rrefAux_fuel_succ]: Eq.subst on the goal with the named peel
      -- `rrefAux_fuel_succ invK A fuel r j` (sym.); the unique
      -- `rrefAux invK (fuel+1) r j A` is the `IsRref` argument of the goal.
      refine Eq.subst (motive := fun M => IsRref M)
        (rrefAux_fuel_succ invK A fuel r j).symm ?_
      rcases Nat.lt_or_ge j n with hj | hj
      · -- Former rw [dite_eq_left hj]: Eq.subst on the goal with the named rule
        -- `dite_eq_left hj` (sym.); `j < n` holds and the `dite` occurs once.
        refine Eq.subst (motive := fun M => IsRref M) (dite_eq_left hj).symm ?_
        rcases Nat.lt_or_ge r m with hrm | hrm
        · -- Former rw [dite_eq_left hrm]: Eq.subst on the goal with the named
          -- rule `dite_eq_left hrm` (sym.); `r < m` holds, single `dite`.
          refine Eq.subst (motive := fun M => IsRref M) (dite_eq_left hrm).symm ?_
          cases hfp : findPivotRow
              (fun i => Nat.ble r i.val && (if A i ⟨j, hj⟩ ≠ 0 then true else false)) m r with
          | none =>
              have hcol : ∀ a : Fin m, r ≤ a.val → A a ⟨j, hj⟩ = 0 :=
                fun a ha => rrefAux_pivot_none hfp a ha
              have h2 : j+(fuel+1) = j+1+fuel := Nat.add_right_comm j fuel 1
              -- Former rw [h2] at hfuel: Eq.subst with the named rule `h2`
              -- acting on `hfuel`; fully instantiated; the unique `j+(fuel+1)`
              -- is the RHS of `hfuel`'s `≤` (motive `fun v => n ≤ v`).
              have hfuel' : n ≤ j+1+fuel :=
                Eq.subst (motive := fun v => n ≤ v) h2 hfuel
              exact ih (rrefState_step_none hj hs hcol) hr hfuel'
          | some i =>
              have hpi := rrefAux_pivot_some hfp
              have h2 : j+(fuel+1) = j+1+fuel := Nat.add_right_comm j fuel 1
              -- Former rw [h2] at hfuel: Eq.subst with the named rule `h2`
              -- acting on `hfuel`; fully instantiated; unique occurrence.
              have hfuel' : n ≤ j+1+fuel :=
                Eq.subst (motive := fun v => n ≤ v) h2 hfuel
              exact ih (rrefState_step_pivot invK hinv hs hrm hj i hpi.1 hpi.2)
                (Nat.succ_le_of_lt hrm) hfuel'
        · -- `m ≤ r`: no row is at or below `r`, so column `j` is vacuously zero there.
          -- Former rw [dite_eq_right (Nat.not_lt.mpr hrm)]: Eq.subst on the
          -- goal with the named rule (sym.); `¬ r < m`, single `dite`.
          refine Eq.subst (motive := fun M => IsRref M)
            (dite_eq_right (Nat.not_lt.mpr hrm)).symm ?_
          have hcol : ∀ a : Fin m, r ≤ a.val → A a ⟨j, hj⟩ = 0 :=
            fun a ha => absurd
              (Nat.lt_of_le_of_lt ha (Nat.lt_of_lt_of_le a.isLt hrm)) (Nat.lt_irrefl r)
          have h2 : j+(fuel+1) = j+1+fuel := Nat.add_right_comm j fuel 1
          -- Former rw [h2] at hfuel: Eq.subst with the named rule `h2` acting
          -- on `hfuel`; fully instantiated; unique occurrence in `hfuel`.
          have hfuel' : n ≤ j+1+fuel :=
            Eq.subst (motive := fun v => n ≤ v) h2 hfuel
          exact ih (rrefState_step_none hj hs hcol) hr hfuel'
      · -- `n ≤ j`: all columns processed; the loop returns `A` unchanged.
        -- Former rw [dite_eq_right (Nat.not_lt.mpr hj)]: Eq.subst on the goal
        -- with the named rule (sym.); `n ≤ j`, single `dite` occurrence.
        refine Eq.subst (motive := fun M => IsRref M)
          (dite_eq_right (Nat.not_lt.mpr hj)).symm ?_
        exact rrefState_isRref_of_done hj hs


-- Reference: Mines–Richman–Ruitenburg 2008, Pt. II Ch. 6; issue #108
-- (correctness of the elimination procedure).
/-- Correctness of Gaussian elimination: the output is in reduced
row-echelon form. -/
theorem rref_isRref (hinv : ∀ a : K, a ≠ 0 → invK a * a = 1) (A : FreeMatrix K m n) :
    IsRref (rref invK A) :=
  rrefAux_state invK hinv (rrefState_zero A) (Nat.zero_le m)
    ((Nat.le_succ n).trans (Nat.le_of_eq (Nat.zero_add (n+1)).symm))

