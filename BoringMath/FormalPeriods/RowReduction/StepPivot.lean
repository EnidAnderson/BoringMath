/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Init
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Fin.Basic
import BoringMath.FormalPeriods.RowReduction.RowOps
import BoringMath.FormalPeriods.RowReduction.Predicates
import BoringMath.FormalPeriods.RowReduction.Invariant

/-!
# The pivot step and the loop invariant (P.2.1, part 6)

Part 6 of `BoringMath.FormalPeriods.RowReduction`: the composed
swap-scale-elimination pivot step and the invariant preservation
`rrefState_step_pivot`.
-/

universe u

namespace BoringMath

variable {K : Type u} [Field K] {m n : ℕ}
variable (invK : K → K)
variable [DecidableEq K]

-- Reference: definitional peel of the swap-then-scale at the pivot row.
omit [DecidableEq K] in
/-- Scaling the swapped-in pivot row at the pivot row multiplies the old row
`i` entry by `s`. -/
theorem rrefStep_swap_scale_self (A : FreeMatrix K m n) (r' i : Fin m) (s : K)
    (c' : Fin n) :
    matRowScale (matRowSwap A r' i) r' s r' c' = s * A i c' := by
  -- Former `rw [matRowScale_self …]`: named peel `matRowScale_self
  -- (matRowSwap A r' i) r' s c'`; the scaled pivot entry occurs once, as the
  -- LHS of the goal, so the step composes by `trans`.
  have h1 : matRowScale (matRowSwap A r' i) r' s r' c'
      = s * matRowSwap A r' i r' c' :=
    matRowScale_self (matRowSwap A r' i) r' s c'
  -- Former `rw [matRowSwap_left …]`: named peel `matRowSwap_left A r' i c'`;
  -- `matRowSwap A r' i r' c'` occurs once, as the right factor of `s * …`.
  exact h1.trans (congrArg (fun t => s * t) (matRowSwap_left A r' i c'))

-- Reference: Mines–Richman–Ruitenburg 2008, Pt. II Ch. 6; peel of the
-- composed pivot step at the new pivot row, before the pivot column.
omit [DecidableEq K] in
/-- After the pivot step, the new pivot row vanishes at every column before
the pivot column (the swapped-in row vanished there). -/
theorem rrefStepMat_pivot_row_before (A : FreeMatrix K m n) (r' i : Fin m) (s : K)
    (c c' : Fin n) (hzero : A i c' = 0) :
    matRowElim (matRowScale (matRowSwap A r' i) r' s) r' c r' c' = 0 := by
  -- Former `rw [matRowElim_self …]`: named peel; the elimination fixes the
  -- pivot row, whose entry occurs once as the LHS of the goal.
  have h1 : matRowElim (matRowScale (matRowSwap A r' i) r' s) r' c r' c'
      = matRowScale (matRowSwap A r' i) r' s r' c' :=
    matRowElim_self (matRowScale (matRowSwap A r' i) r' s) r' c c'
  -- Former `rw [rrefStep_swap_scale_self …]`: named peel; `… r' c'` occurs once.
  have h2 : matRowScale (matRowSwap A r' i) r' s r' c' = s * A i c' :=
    rrefStep_swap_scale_self A r' i s c'
  -- Former `rw [hzero, mul_zero]`: `A i c'` occurs once as the right factor of
  -- `s * …`; then `mul_zero s : s * 0 = 0` closes the goal.
  exact h1.trans (h2.trans ((congrArg (fun t => s * t) hzero).trans (mul_zero s)))

-- Reference: Mines–Richman–Ruitenburg 2008, Pt. II Ch. 6 (normalizing the
-- pivot to `1`); peel of the composed pivot step at the pivot entry.
omit [DecidableEq K] in
/-- After the pivot step, the pivot entry is `1`. -/
theorem rrefStepMat_pivot_row_at (hinv : ∀ a : K, a ≠ 0 → invK a * a = 1)
    (A : FreeMatrix K m n) (r' i : Fin m) (c : Fin n) (hne : A i c ≠ 0) :
    matRowElim (matRowScale (matRowSwap A r' i) r' (invK (A i c))) r' c r' c = 1 := by
  -- Former `rw [matRowElim_self …]`: named peel; the eliminated pivot entry
  -- occurs once as the LHS of the goal, then `rrefStep_pivot_one` closes it.
  have h1 : matRowElim (matRowScale (matRowSwap A r' i) r' (invK (A i c))) r' c r' c
      = matRowScale (matRowSwap A r' i) r' (invK (A i c)) r' c :=
    matRowElim_self (matRowScale (matRowSwap A r' i) r' (invK (A i c))) r' c c
  exact h1.trans (rrefStep_pivot_one invK hinv A r' i c hne)

-- Reference: Mines–Richman–Ruitenburg 2008, Pt. II Ch. 6 (the pivot step
-- fixes every other row on the columns before the pivot column).
omit [DecidableEq K] in
/-- After the pivot step, every row other than the pivot row agrees with the
original matrix at every column before the pivot column. -/
theorem rrefStepMat_off_pivot_before (A : FreeMatrix K m n) (r' i a : Fin m) (s : K)
    (c c' : Fin n) (ha : a ≠ r') (hzero : A i c' = 0) (hzeror : A r' c' = 0) :
    matRowElim (matRowScale (matRowSwap A r' i) r' s) r' c a c' = A a c' := by
  -- NONLINEAR: `ha` feeds both the elimination and the scale peels, `hzero`
  -- feeds both the product step and the swap branch, and `h` below feeds both
  -- `ha'` and the final goal transport.
  -- Former `rw [matRowElim_other …]`: named peel; the eliminated off-pivot
  -- entry occurs once as the LHS of the goal.
  have h1 : matRowElim (matRowScale (matRowSwap A r' i) r' s) r' c a c'
      = matRowScale (matRowSwap A r' i) r' s a c'
        - matRowScale (matRowSwap A r' i) r' s a c
          * matRowScale (matRowSwap A r' i) r' s r' c' :=
    matRowElim_other (matRowScale (matRowSwap A r' i) r' s) r' a ha c c'
  -- Former `rw [rrefStep_swap_scale_self …, hzero, mul_zero, mul_zero,
  -- sub_zero]`: the pivot-row entry `… r' c'` occurs once as the right factor
  -- of the product; then `A i c' = 0`, `s * 0 = 0`, `… * 0 = 0`, `x - 0 = x`.
  have h2 : matRowScale (matRowSwap A r' i) r' s a c'
        - matRowScale (matRowSwap A r' i) r' s a c
          * matRowScale (matRowSwap A r' i) r' s r' c'
      = matRowScale (matRowSwap A r' i) r' s a c' := by
    calc matRowScale (matRowSwap A r' i) r' s a c'
          - matRowScale (matRowSwap A r' i) r' s a c
            * matRowScale (matRowSwap A r' i) r' s r' c'
        = matRowScale (matRowSwap A r' i) r' s a c'
          - matRowScale (matRowSwap A r' i) r' s a c * (s * A i c') :=
          congrArg (fun t => matRowScale (matRowSwap A r' i) r' s a c'
            - matRowScale (matRowSwap A r' i) r' s a c * t)
            (rrefStep_swap_scale_self A r' i s c')
      _ = matRowScale (matRowSwap A r' i) r' s a c'
          - matRowScale (matRowSwap A r' i) r' s a c * (s * 0) :=
          congrArg (fun t => matRowScale (matRowSwap A r' i) r' s a c'
            - matRowScale (matRowSwap A r' i) r' s a c * (s * t)) hzero
      _ = matRowScale (matRowSwap A r' i) r' s a c'
          - matRowScale (matRowSwap A r' i) r' s a c * 0 :=
          congrArg (fun t => matRowScale (matRowSwap A r' i) r' s a c'
            - matRowScale (matRowSwap A r' i) r' s a c * t) (mul_zero s)
      _ = matRowScale (matRowSwap A r' i) r' s a c' - 0 :=
          congrArg (fun t => matRowScale (matRowSwap A r' i) r' s a c' - t)
            (mul_zero (matRowScale (matRowSwap A r' i) r' s a c))
      _ = matRowScale (matRowSwap A r' i) r' s a c' :=
          sub_zero (matRowScale (matRowSwap A r' i) r' s a c')
  -- Former `rw [matRowScale_other …]`: named peel; the scaled off-pivot entry
  -- occurs once as the LHS.
  have h3 : matRowScale (matRowSwap A r' i) r' s a c' = matRowSwap A r' i a c' :=
    matRowScale_other (matRowSwap A r' i) r' a ha s c'
  cases (inferInstance : Decidable (a = i)) with
  | isTrue h =>
      -- Former `rw [h] at ha ⊢`: rule `h : a = i`, fully instantiated; `a`
      -- occurs once in `ha` and uniformly in the goal.
      have ha' : i ≠ r' := Eq.subst (motive := fun x => x ≠ r') h ha
      -- Former `rw [matRowSwap_right …, hzeror, hzero]`: the swap sends row
      -- `i` to the old row `r'`; both entries are `0`.
      exact h1.trans (h2.trans (h3.trans (Eq.subst
        (motive := fun x => matRowSwap A r' i x c' = A x c') h.symm
        ((matRowSwap_right A r' i ha' c').trans (hzeror.trans hzero.symm)))))
  | isFalse haI =>
      -- Former `rw [matRowSwap_other …]`: named peel; `matRowSwap A r' i a c'`
      -- occurs once as the LHS; the result is exactly its RHS.
      exact h1.trans (h2.trans (h3.trans (matRowSwap_other A r' i a ha haI c')))

-- Reference: Mines–Richman–Ruitenburg 2008, Pt. II Ch. 6 (the pivot step
-- preserves the invariant); Hörmann arXiv:2106.03803 Remark 3.3 (program
-- context).
/-- One pivot step — swap the pivot row `i` into row `r`, scale the pivot to
`1`, clear column `j` — takes `RrefState r j A` to `RrefState (r+1) (j+1) A3`. -/
theorem rrefState_step_pivot (hinv : ∀ a : K, a ≠ 0 → invK a * a = 1) {r j : ℕ}
    {A : FreeMatrix K m n} (hs : RrefState r j A) (hr : r < m) (hj : j < n) (i : Fin m)
    (hle : r ≤ i.val) (hne : A i ⟨j, hj⟩ ≠ 0) :
    RrefState (r+1) (j+1)
      (matRowElim
        (matRowScale (matRowSwap A ⟨r, hr⟩ i) ⟨r, hr⟩ (invK (A i ⟨j, hj⟩)))
        ⟨r, hr⟩ ⟨j, hj⟩) := by
  rcases hs with ⟨hR1, hR2, hR3, hR4, hR5, hR6⟩
  -- NONLINEAR: each invariant component (`hR1`, `hR3`, `hR4`, `hR5`, `hR6`) is
  -- applied at several rows/columns of the case split below.
  -- Name the three intermediate matrices: `A1` = swap, `A2` = scale, `A3` = elim.
  generalize hA1 : matRowSwap A ⟨r, hr⟩ i = A1
  generalize hA2 : matRowScale A1 ⟨r, hr⟩ (invK (A i ⟨j, hj⟩)) = A2
  generalize hA3 : matRowElim A2 ⟨r, hr⟩ ⟨j, hj⟩ = A3
  have hp1 : A2 ⟨r, hr⟩ ⟨j, hj⟩ = 1 := by
    -- Former `rw [← hA2, ← hA1]`: unfold the named generalizations by
    -- `Eq.subst` with explicit motive; `A2` occurs once (head of the goal).
    have h1 : matRowScale (matRowSwap A ⟨r, hr⟩ i) ⟨r, hr⟩ (invK (A i ⟨j, hj⟩))
        ⟨r, hr⟩ ⟨j, hj⟩ = 1 :=
      rrefStep_pivot_one invK hinv A ⟨r, hr⟩ i ⟨j, hj⟩ hne
    have h2 : matRowScale A1 ⟨r, hr⟩ (invK (A i ⟨j, hj⟩)) ⟨r, hr⟩ ⟨j, hj⟩ = 1 :=
      Eq.subst (motive := fun M =>
        matRowScale M ⟨r, hr⟩ (invK (A i ⟨j, hj⟩)) ⟨r, hr⟩ ⟨j, hj⟩ = 1) hA1 h1
    exact Eq.subst (motive := fun M => M ⟨r, hr⟩ ⟨j, hj⟩ = 1) hA2 h2
  have hA3rc : A3 ⟨r, hr⟩ ⟨j, hj⟩ = 1 := by
    -- Former `rw [← hA3, ← hA2, ← hA1]`: unfold the named generalizations by
    -- `Eq.subst`; each of `A3`, `A2`, `A1` occurs once on the way down.
    have h1 : matRowElim (matRowScale (matRowSwap A ⟨r, hr⟩ i) ⟨r, hr⟩
        (invK (A i ⟨j, hj⟩))) ⟨r, hr⟩ ⟨j, hj⟩ ⟨r, hr⟩ ⟨j, hj⟩ = 1 :=
      rrefStepMat_pivot_row_at invK hinv A ⟨r, hr⟩ i ⟨j, hj⟩ hne
    have h2 : matRowElim (matRowScale A1 ⟨r, hr⟩ (invK (A i ⟨j, hj⟩))) ⟨r, hr⟩
        ⟨j, hj⟩ ⟨r, hr⟩ ⟨j, hj⟩ = 1 :=
      Eq.subst (motive := fun M => matRowElim (matRowScale M ⟨r, hr⟩
        (invK (A i ⟨j, hj⟩))) ⟨r, hr⟩ ⟨j, hj⟩ ⟨r, hr⟩ ⟨j, hj⟩ = 1) hA1 h1
    have h3 : matRowElim A2 ⟨r, hr⟩ ⟨j, hj⟩ ⟨r, hr⟩ ⟨j, hj⟩ = 1 :=
      Eq.subst (motive := fun M => matRowElim M ⟨r, hr⟩ ⟨j, hj⟩ ⟨r, hr⟩ ⟨j, hj⟩ = 1)
        hA2 h2
    exact Eq.subst (motive := fun M => M ⟨r, hr⟩ ⟨j, hj⟩ = 1) hA3 h3
  have hA3r_before : ∀ c' : Fin n, c'.val < j → A3 ⟨r, hr⟩ c' = 0 := by
    intro c' hc'
    -- Former `rw [← hA3, ← hA2, ← hA1]`: unfold the named generalizations.
    have h1 : matRowElim (matRowScale (matRowSwap A ⟨r, hr⟩ i) ⟨r, hr⟩
        (invK (A i ⟨j, hj⟩))) ⟨r, hr⟩ ⟨j, hj⟩ ⟨r, hr⟩ c' = 0 :=
      rrefStepMat_pivot_row_before A ⟨r, hr⟩ i (invK (A i ⟨j, hj⟩)) ⟨j, hj⟩ c'
        (hR1 i hle c' hc')
    have h2 : matRowElim (matRowScale A1 ⟨r, hr⟩ (invK (A i ⟨j, hj⟩))) ⟨r, hr⟩
        ⟨j, hj⟩ ⟨r, hr⟩ c' = 0 :=
      Eq.subst (motive := fun M => matRowElim (matRowScale M ⟨r, hr⟩
        (invK (A i ⟨j, hj⟩))) ⟨r, hr⟩ ⟨j, hj⟩ ⟨r, hr⟩ c' = 0) hA1 h1
    have h3 : matRowElim A2 ⟨r, hr⟩ ⟨j, hj⟩ ⟨r, hr⟩ c' = 0 :=
      Eq.subst (motive := fun M => matRowElim M ⟨r, hr⟩ ⟨j, hj⟩ ⟨r, hr⟩ c' = 0)
        hA2 h2
    exact Eq.subst (motive := fun M => M ⟨r, hr⟩ c' = 0) hA3 h3
  have hA3off_at : ∀ a : Fin m, a ≠ ⟨r, hr⟩ → A3 a ⟨j, hj⟩ = 0 := by
    intro a ha
    -- Former `rw [← hA3]`: `A3` occurs once in the goal.
    exact Eq.subst (motive := fun M => M a ⟨j, hj⟩ = 0) hA3
      (matRowElim_pivot_zero A2 ⟨r, hr⟩ a ha ⟨j, hj⟩ hp1)
  have hA3off_before : ∀ a : Fin m, a ≠ ⟨r, hr⟩ → ∀ c' : Fin n, c'.val < j →
      A3 a c' = A a c' := by
    intro a ha c' hc'
    -- Former `rw [← hA3, ← hA2, ← hA1]`: unfold the named generalizations.
    have h1 : matRowElim (matRowScale (matRowSwap A ⟨r, hr⟩ i) ⟨r, hr⟩
        (invK (A i ⟨j, hj⟩))) ⟨r, hr⟩ ⟨j, hj⟩ a c' = A a c' :=
      rrefStepMat_off_pivot_before A ⟨r, hr⟩ i a (invK (A i ⟨j, hj⟩)) ⟨j, hj⟩ c'
        ha (hR1 i hle c' hc') (hR1 ⟨r, hr⟩ (Nat.le_refl r) c' hc')
    have h2 : matRowElim (matRowScale A1 ⟨r, hr⟩ (invK (A i ⟨j, hj⟩))) ⟨r, hr⟩
        ⟨j, hj⟩ a c' = A a c' :=
      Eq.subst (motive := fun M => matRowElim (matRowScale M ⟨r, hr⟩
        (invK (A i ⟨j, hj⟩))) ⟨r, hr⟩ ⟨j, hj⟩ a c' = A a c') hA1 h1
    have h3 : matRowElim A2 ⟨r, hr⟩ ⟨j, hj⟩ a c' = A a c' :=
      Eq.subst (motive := fun M => matRowElim M ⟨r, hr⟩ ⟨j, hj⟩ a c' = A a c') hA2 h2
    exact Eq.subst (motive := fun M => M a c' = A a c') hA3 h3
  have hne_of_lt : ∀ a : Fin m, a.val < r → a ≠ ⟨r, hr⟩ := by
    intro a ha h
    -- Former `rw [h] at ha`: rule `a = ⟨r, hr⟩`, fully instantiated; `a`
    -- occurs once in `ha`.
    exact absurd (Eq.subst (motive := fun x => x.val < r) h ha) (Nat.lt_irrefl r)
  have hne_of_ge : ∀ a : Fin m, r+1 ≤ a.val → a ≠ ⟨r, hr⟩ := by
    intro a ha h
    -- Former `rw [h] at ha`: rule `a = ⟨r, hr⟩`, fully instantiated; unique
    -- occurrence in `ha`.
    exact absurd (Eq.subst (motive := fun x => r+1 ≤ x.val) h ha)
      (Nat.not_succ_le_self r)
  have hlc_r' : matLeadingCol A3 ⟨r, hr⟩ = j := by
    have hne3 : A3 ⟨r, hr⟩ ⟨j, hj⟩ ≠ 0 := by
      intro h
      -- Former `rw [hA3rc] at h`: fully instantiated; `A3 ⟨r, hr⟩ ⟨j, hj⟩`
      -- occurs once in `h`; gives `1 = 0`.
      exact absurd (Eq.subst (motive := fun t => t = 0) hA3rc h) one_ne_zero
    exact matLeadingCol_eq_of_zero_before hj hA3r_before hne3
  have hlc_old : ∀ a : Fin m, a.val < r → matLeadingCol A3 a = matLeadingCol A a := by
    intro a hlt
    exact matLeadingCol_eq_of_agree_before (Nat.le_of_lt hj)
      (fun c' hc' => (hA3off_before a (hne_of_lt a hlt) c' hc').symm) (hR3 a hlt)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Rows at or below `r+1` vanish on columns `< j+1`.
    intro a ha c' hc'
    rcases Nat.lt_or_ge c'.val j with hlt | hge
    · -- Former `rw [hA3off_before …]`: `A3 a c'` occurs once, as the LHS of
      -- the goal; the step composes the named fact by `trans`.
      exact (hA3off_before a (hne_of_ge a ha) c' hlt).trans
        (hR1 a (Nat.le_trans (Nat.le_succ r) ha) c' hlt)
    · have hval : c'.val = j := Nat.le_antisymm (Nat.le_of_lt_succ hc') hge
      have hceq : c' = ⟨j, hj⟩ := Fin.eq_of_val_eq hval
      -- Former `rw [hceq]`: rule `c' = ⟨j, hj⟩`, fully instantiated; `c'`
      -- occurs once in the goal; transport the off-pivot-at-`j` fact.
      exact Eq.subst (motive := fun c => A3 a c = 0) hceq.symm
        (hA3off_at a (hne_of_ge a ha))
  · -- Rows `< r+1` are nonzero: old pivot rows keep their `1`, the new
    -- pivot row has `A3 ⟨r, hr⟩ ⟨j, hj⟩ = 1`.
    intro a ha
    rcases Nat.lt_or_ge a.val r with hlt | hge
    · have hk := hR3 a hlt
      have hkn : matLeadingCol A a < n := Nat.lt_trans hk hj
      have h1 : A a ⟨matLeadingCol A a, hkn⟩ = 1 :=
        hR4 a hlt ⟨matLeadingCol A a, hkn⟩ (Fin.val_mk hkn).symm
      intro hzero
      have h0 := hzero ⟨matLeadingCol A a, hkn⟩
      -- Former `rw [hA3off_before …] at h0`: Eq.subst with motive
      -- `fun t => t = 0`; `A3 a ⟨…⟩` occurs once in `h0`.
      have h0' : A a ⟨matLeadingCol A a, hkn⟩ = 0 :=
        Eq.subst (motive := fun t => t = 0)
          (hA3off_before a (hne_of_lt a hlt) ⟨matLeadingCol A a, hkn⟩ hk) h0
      -- Former `rw [h1] at h0`: Eq.subst with motive `fun t => t = 0`;
      -- `A a ⟨…⟩` occurs once in `h0`; gives `1 = 0`.
      exact absurd (Eq.subst (motive := fun t => t = 0) h1 h0') one_ne_zero
    · have haveq : a = ⟨r, hr⟩ :=
        Fin.eq_of_val_eq (Nat.le_antisymm (Nat.le_of_lt_succ ha) hge)
      -- Former `rw [haveq]` then `rw [hA3rc] at h0`: rule `a = ⟨r, hr⟩`;
      -- `a` occurs once in `h0`, then `A3 ⟨r, hr⟩ ⟨j, hj⟩` once in `h0`.
      intro hzero
      have h0 := hzero ⟨j, hj⟩
      have h0' : A3 ⟨r, hr⟩ ⟨j, hj⟩ = 0 :=
        Eq.subst (motive := fun x => A3 x ⟨j, hj⟩ = 0) haveq h0
      exact absurd (Eq.subst (motive := fun t => t = 0) hA3rc h0') one_ne_zero
  · -- Leading columns of rows `< r+1` are `< j+1`.
    intro a ha
    rcases Nat.lt_or_ge a.val r with hlt | hge
    · -- Former `rw [hlc_old a hlt]`: `matLeadingCol A3 a` occurs once in the
      -- goal; transport the bound by `Eq.subst`.
      exact Eq.subst (motive := fun t => t < j + 1) (hlc_old a hlt).symm
        (Nat.lt_trans (hR3 a hlt) (Nat.lt_succ_self j))
    · have haveq : a = ⟨r, hr⟩ :=
        Fin.eq_of_val_eq (Nat.le_antisymm (Nat.le_of_lt_succ ha) hge)
      -- Former `rw [haveq, hlc_r']`: `a` occurs once and `matLeadingCol A3
      -- ⟨r, hr⟩` once in the goal.
      exact Eq.subst (motive := fun x => matLeadingCol A3 x < j + 1) haveq.symm
        (Eq.subst (motive := fun t => t < j + 1) hlc_r'.symm (Nat.lt_succ_self j))
  · -- Pivot entries of rows `< r+1` are `1`.
    intro a ha c' hlc
    rcases Nat.lt_or_ge a.val r with hlt | hge
    · -- Former `rw [hlc_old a hlt] at hlc`: Eq.subst with motive
      -- `fun t => t = c'.val`; unique occurrence in `hlc`.
      have hlc' : matLeadingCol A a = c'.val :=
        Eq.subst (motive := fun t => t = c'.val) (hlc_old a hlt) hlc
      have hc'j : c'.val < j := by
        -- Former `rw [← hlc]`: `c'.val` occurs once in the goal.
        exact Eq.subst (motive := fun t => t < j) hlc' (hR3 a hlt)
      -- Former `rw [hA3off_before …]`: `A3 a c'` occurs once as the LHS of the
      -- goal; the step composes the named fact by `trans`.
      exact (hA3off_before a (hne_of_lt a hlt) c' hc'j).trans (hR4 a hlt c' hlc')
    · have haveq : a = ⟨r, hr⟩ :=
        Fin.eq_of_val_eq (Nat.le_antisymm (Nat.le_of_lt_succ ha) hge)
      -- Former `rw [haveq, hlc_r'] at hlc`: unique occurrences; gives
      -- `j = c'.val`.
      have hlc' : j = c'.val :=
        Eq.subst (motive := fun t => t = c'.val) hlc_r'
          (Eq.subst (motive := fun x => matLeadingCol A3 x = c'.val) haveq hlc)
      have hceq : c' = ⟨j, hj⟩ := Fin.eq_of_val_eq hlc'.symm
      -- Former `rw [haveq, hceq]`: unique occurrences in the goal; transport
      -- `hA3rc` by `Eq.subst`.
      exact Eq.subst (motive := fun x => A3 x c' = 1) haveq.symm
        (Eq.subst (motive := fun c => A3 ⟨r, hr⟩ c = 1) hceq.symm hA3rc)
  · -- Leading columns strictly increase on rows `< r+1`.
    intro a b ha hb hab
    rcases Nat.lt_or_ge a.val r with halt | hage
    · rcases Nat.lt_or_ge b.val r with hblt | hbge
      · -- Former `rw [hlc_old a halt, hlc_old b hblt]`: each leading column
        -- occurs once in the goal.
        exact Eq.subst (motive := fun t => t < matLeadingCol A3 b) (hlc_old a halt).symm
          (Eq.subst (motive := fun t => matLeadingCol A a < t) (hlc_old b hblt).symm
            (hR5 a b halt hblt hab))
      · have hbq : b = ⟨r, hr⟩ :=
          Fin.eq_of_val_eq (Nat.le_antisymm (Nat.le_of_lt_succ hb) hbge)
        -- Former `rw [hlc_old a halt, hbq, hlc_r']`: unique occurrences in the
        -- goal.
        exact Eq.subst (motive := fun t => t < matLeadingCol A3 b)
          (hlc_old a halt).symm
          (Eq.subst (motive := fun x => matLeadingCol A a < matLeadingCol A3 x) hbq.symm
            (Eq.subst (motive := fun t => matLeadingCol A a < t) hlc_r'.symm
              (hR3 a halt)))
    · have haq : a = ⟨r, hr⟩ :=
        Fin.eq_of_val_eq (Nat.le_antisymm (Nat.le_of_lt_succ ha) hage)
      -- Former `rw [haq] at hab`: rule `a = ⟨r, hr⟩`; unique occurrence in
      -- `hab`.
      have hab' : ⟨r, hr⟩ < b := Eq.subst (motive := fun x => x < b) haq hab
      exact absurd (Nat.lt_of_lt_of_le hab' (Nat.le_of_lt_succ hb))
        (Nat.lt_irrefl r)
  · -- Pivot columns are cleared in every other row.
    intro a ha b hne' c' hlc
    rcases Nat.lt_or_ge a.val r with halt | hage
    · -- Former `rw [hlc_old a halt] at hlc`: unique occurrence in `hlc`.
      have hlc' : matLeadingCol A a = c'.val :=
        Eq.subst (motive := fun t => t = c'.val) (hlc_old a halt) hlc
      have hc'j : c'.val < j := by
        -- Former `rw [← hlc]`: `c'.val` occurs once in the goal.
        exact Eq.subst (motive := fun t => t < j) hlc' (hR3 a halt)
      rcases Nat.lt_or_ge b.val r with hblt | hbge
      · -- Former `rw [hA3off_before …]`: `A3 b c'` occurs once as the LHS of
        -- the goal.
        exact (hA3off_before b (hne_of_lt b hblt) c' hc'j).trans
          (hR6 a halt b hne' c' hlc')
      · rcases Nat.lt_or_ge b.val (r+1) with hblt1 | hbge1
        · have hbq : b = ⟨r, hr⟩ :=
            Fin.eq_of_val_eq (Nat.le_antisymm (Nat.le_of_lt_succ hblt1) hbge)
          -- Former `rw [hbq]`: rule `b = ⟨r, hr⟩`; unique occurrence in the
          -- goal.
          exact Eq.subst (motive := fun x => A3 x c' = 0) hbq.symm
            (hA3r_before c' hc'j)
        · -- Former `rw [hA3off_before …]`: `A3 b c'` occurs once in the goal.
          exact (hA3off_before b (hne_of_ge b hbge1) c' hc'j).trans
            (hR1 b (Nat.le_trans (Nat.le_succ r) hbge1) c' hc'j)
    · have haq : a = ⟨r, hr⟩ :=
        Fin.eq_of_val_eq (Nat.le_antisymm (Nat.le_of_lt_succ ha) hage)
      -- Former `rw [haq, hlc_r'] at hlc`: unique occurrences; gives
      -- `j = c'.val`.
      have hlc' : j = c'.val :=
        Eq.subst (motive := fun t => t = c'.val) hlc_r'
          (Eq.subst (motive := fun x => matLeadingCol A3 x = c'.val) haq hlc)
      have hceq : c' = ⟨j, hj⟩ := Fin.eq_of_val_eq hlc'.symm
      -- Former `rw [hceq]`: rule `c' = ⟨j, hj⟩`; unique occurrence in the
      -- goal.
      exact Eq.subst (motive := fun c => A3 b c = 0) hceq.symm
        (hA3off_at b (fun h => hne' (haq.trans h.symm)))

end BoringMath
