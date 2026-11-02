/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Init
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Fin.Basic

/-!
# The pivot search (P.2.1, part 2)

Part 2 of `BoringMath.FormalPeriods.RowReduction`: the explicit finite
search `findPivotRow` and its soundness/completeness specs.
-/

namespace BoringMath

/-! ## The pivot search -/

-- Reference: Mines–Richman–Ruitenburg 2008, Pt. II Ch. 6 (choosing a pivot
-- row in a discrete field is a finite, explicit search).
/-- Search the rows `lo, lo+1, …, lo+t-1` (stopping at the row count `m`)
for the first row with `p i = true`; structural recursion on the fuel
`t`, hence total and computable. -/
def findPivotRow {m : ℕ} (p : Fin m → Bool) : ℕ → ℕ → Option (Fin m)
  | 0, _ => none
  | t+1, lo =>
      if h : lo < m then
        if p ⟨lo, h⟩ then some ⟨lo, h⟩ else findPivotRow p t (lo+1)
      else none

-- Reference: definitional peel of `findPivotRow` at fuel `0`.
/-- With no fuel left, the search finds nothing. -/
theorem findPivotRow_zero {m : ℕ} (p : Fin m → Bool) (lo : ℕ) :
    findPivotRow p 0 lo = none :=
  rfl

-- Reference: definitional peel of `findPivotRow` at fuel `t+1`.
/-- One search step: test row `lo`, then continue from `lo+1`. -/
theorem findPivotRow_succ {m : ℕ} (p : Fin m → Bool) (t lo : ℕ) :
    findPivotRow p (t+1) lo =
      (if h : lo < m then
        (if p ⟨lo, h⟩ then some ⟨lo, h⟩ else findPivotRow p t (lo+1))
      else none) :=
  rfl

-- Reference: Mines–Richman–Ruitenburg 2008, Pt. II Ch. 6 (soundness of the
-- pivot search).
/-- If the search returns a row, it is in the searched range and satisfies
the predicate. -/
theorem findPivotRow_some_spec {m : ℕ} {p : Fin m → Bool} {t lo : ℕ} {i : Fin m}
    (h : findPivotRow p t lo = some i) :
    lo ≤ i.val ∧ i.val < lo + t ∧ p i = true := by
  induction t generalizing lo with
  | zero =>
      -- Eq.subst instance for `findPivotRow_zero p lo` acting on `h`:
      -- fully instantiated, unique occurrence of `findPivotRow p 0 lo` in `h`.
      have h0 : none = some i :=
        Eq.subst (motive := fun z => z = some i) (findPivotRow_zero p lo) h
      cases h0
  | succ t ih =>
      -- Eq.subst instance for `findPivotRow_succ p t lo` acting on `h`:
      -- fully instantiated, unique occurrence in `h`.
      have h1 : (if h : lo < m then
          (if p ⟨lo, h⟩ then some ⟨lo, h⟩ else findPivotRow p t (lo+1))
        else none) = some i :=
        Eq.subst (motive := fun z => z = some i) (findPivotRow_succ p t lo) h
      rcases Nat.lt_or_ge lo m with hlt | hge
      · -- Eq.mp (congrArg (· = some i) (dite_eq_left hlt)) h1: `lo < m` holds;
        -- single `dite` occurrence in `h1`.
        have h2 : (if p ⟨lo, hlt⟩ then some ⟨lo, hlt⟩ else findPivotRow p t (lo+1))
            = some i :=
          Eq.mp (congrArg (· = some i) (dite_eq_left hlt)) h1
        cases (inferInstance : Decidable (p ⟨lo, hlt⟩ = true)) with
        | isTrue hp =>
          -- Eq.mp (congrArg (· = some i) (ite_eq_left hp)) h2:
          -- `p ⟨lo, hlt⟩ = true`; single `ite` occurrence in `h2`.
          have h3 : some ⟨lo, hlt⟩ = some i :=
            Eq.mp (congrArg (· = some i) (ite_eq_left hp)) h2
          injection h3 with hval
          subst hval
          exact ⟨Nat.le_refl lo, Nat.lt_add_of_pos_right (Nat.succ_pos t), hp⟩
        | isFalse hp =>
          -- Eq.mp (congrArg (· = some i) (ite_eq_right hp)) h2:
          -- `p ⟨lo, hlt⟩ ≠ true`; single `ite` occurrence in `h2`.
          have h4 : findPivotRow p t (lo+1) = some i :=
            Eq.mp (congrArg (· = some i) (ite_eq_right hp)) h2
          have ihh := ih (lo := lo+1) h4
          -- `lo+1+t = lo+(t+1)`: both sides count the searched rows.
          have h5 : lo+1+t = lo+(t+1) := Nat.add_right_comm lo 1 t
          -- Eq.subst instance for `h5` acting on `ihh`: fully instantiated,
          -- unique `lo+1+t` occurrence inside `ihh`.
          have ihh' : lo+1 ≤ i.val ∧ i.val < lo+(t+1) ∧ p i = true :=
            Eq.subst (motive := fun z => lo+1 ≤ i.val ∧ i.val < z ∧ p i = true) h5 ihh
          exact ⟨Nat.le_trans (Nat.le_succ lo) ihh'.1, ihh'.2.1, ihh'.2.2⟩
      · -- Eq.mp (congrArg (· = some i) (dite_eq_right ...)) h1: `m ≤ lo`;
        -- single `dite` occurrence in `h1`.
        have h6 : none = some i :=
          Eq.mp (congrArg (· = some i) (dite_eq_right (Nat.not_lt.mpr hge))) h1
        cases h6

-- Reference: Mines–Richman–Ruitenburg 2008, Pt. II Ch. 6 (completeness of
-- the pivot search).
/-- If the search returns nothing, no row in the searched range satisfies
the predicate. -/
theorem findPivotRow_none_spec {m : ℕ} {p : Fin m → Bool} {t lo : ℕ}
    (h : findPivotRow p t lo = none) (i : Fin m) (hle : lo ≤ i.val)
    (hib : i.val < lo + t) :
    p i = false := by
  induction t generalizing lo with
  | zero => exact absurd (Nat.lt_of_le_of_lt hle hib) (Nat.lt_irrefl lo)
  | succ t ih =>
      -- Eq.subst instance for `findPivotRow_succ p t lo` acting on `h`:
      -- fully instantiated, unique occurrence in `h`.
      have h1 : (if h : lo < m then
          (if p ⟨lo, h⟩ then some ⟨lo, h⟩ else findPivotRow p t (lo+1))
        else none) = none :=
        Eq.subst (motive := fun z => z = none) (findPivotRow_succ p t lo) h
      rcases Nat.lt_or_ge lo m with hlt | hge
      · -- Eq.mp (congrArg (· = none) (dite_eq_left hlt)) h1: single occurrence.
        have h2 : (if p ⟨lo, hlt⟩ then some ⟨lo, hlt⟩ else findPivotRow p t (lo+1))
            = none :=
          Eq.mp (congrArg (· = none) (dite_eq_left hlt)) h1
        cases (inferInstance : Decidable (p ⟨lo, hlt⟩ = true)) with
        | isTrue hp =>
          -- Eq.mp (congrArg (· = none) (ite_eq_left hp)) h2: single occurrence;
          -- `some _ = none` is absurd.
          have h3 : some (⟨lo, hlt⟩ : Fin m) = none :=
            Eq.mp (congrArg (· = none) (ite_eq_left hp)) h2
          cases h3
        | isFalse hp =>
          -- Eq.mp (congrArg (· = none) (ite_eq_right hp)) h2:
          -- `p ⟨lo, hlt⟩ ≠ true`; single occurrence.
          have h4 : findPivotRow p t (lo+1) = none :=
            Eq.mp (congrArg (· = none) (ite_eq_right hp)) h2
          rcases Nat.lt_trichotomy i.val lo with hlt3 | heq | hlt3
          · exact absurd (Nat.lt_of_le_of_lt hle hlt3) (Nat.lt_irrefl lo)
          · -- `i.val = lo`, hence `i = ⟨lo, hlt⟩`.
            have hi : i = ⟨lo, hlt⟩ := Fin.eq_of_val_eq heq
            -- Eq.mpr (congrArg (fun z => p z = false) hi): rule
            -- `i = ⟨lo, hlt⟩`, fully instantiated; unique `i` in the goal.
            exact Eq.mpr (congrArg (fun z => p z = false) hi)
              (Bool.eq_false_iff.mpr hp)
          · have h5 : lo+(t+1) = (lo+1)+t := Nat.add_right_comm lo t 1
            -- Eq.subst instance for `h5` acting on `hib`: fully instantiated,
            -- unique `lo+(t+1)` occurrence inside `hib`.
            have hib' : i.val < (lo+1)+t :=
              Eq.subst (motive := fun z => i.val < z) h5 hib
            exact ih (lo := lo+1) h4 (Nat.succ_le_of_lt hlt3) hib'
      · -- `m ≤ lo`; then `i.val < m ≤ lo ≤ i.val` is absurd.
        -- Eq.mp (congrArg (· = none) (dite_eq_right ...)) h1: single occurrence;
        -- the rewritten `h` (`none = none`) is vacuous, consumed by `cases`.
        have h6 : none = none :=
          Eq.mp (congrArg (· = none) (dite_eq_right (Nat.not_lt.mpr hge))) h1
        cases h6
        exact absurd
          (Nat.lt_of_le_of_lt hle (Nat.lt_of_lt_of_le i.isLt hge))
          (Nat.lt_irrefl lo)

-- Reference: Mines–Richman–Ruitenburg 2008, Pt. II Ch. 6.
/-- If no row satisfies the predicate, the search finds nothing. -/
theorem findPivotRow_eq_none_of {m : ℕ} {p : Fin m → Bool} {t lo : ℕ}
    (h : ∀ i : Fin m, p i = false) :
    findPivotRow p t lo = none := by
  induction t generalizing lo with
  | zero => exact findPivotRow_zero p lo
  | succ t ih =>
      -- Eq.subst on the goal for `findPivotRow_succ p t lo` (used
      -- symmetrically): fully instantiated; the goal LHS is the unique
      -- occurrence.
      refine Eq.subst (motive := fun z => z = none) (findPivotRow_succ p t lo).symm ?_
      rcases Nat.lt_or_ge lo m with hlt | hge
      · -- Eq.subst on the goal for `dite_eq_left hlt` (symmetrically): single
        -- `dite` occurrence in the goal.
        refine Eq.subst (motive := fun z => z = none) (dite_eq_left hlt).symm ?_
        have hp := h ⟨lo, hlt⟩
        -- `hp : p ⟨lo, hlt⟩ = false`; the goal's single `ite` occurrence is
        -- peeled by `ite_eq_right` on the false condition.
        have hne : ¬(p ⟨lo, hlt⟩ = true) := Bool.eq_false_iff.mp hp
        exact (ite_eq_right hne).trans (ih (lo := lo+1))
      · -- `dite_eq_right ...`: the else-branch is already `none`; single
        -- occurrence, closes the goal.
        exact dite_eq_right (Nat.not_lt.mpr hge)

