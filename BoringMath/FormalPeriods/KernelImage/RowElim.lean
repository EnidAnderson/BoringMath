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
import BoringMath.FormalPeriods.KernelImage.Basic
import BoringMath.FormalPeriods.KernelImage.ListSum

/-!
# Elimination steps preserve the annihilation predicate (P.2.2, part 7)

Piece 7 of `BoringMath.FormalPeriods.KernelImage`: `applyMat` after
`matRowElim` fixes the pivot row and changes only the eliminated rows,
hence the predicate `applyMat _ x = 0` is preserved in both directions;
ends with `invK_ne_zero`.
-/

universe u

namespace BoringMath

variable {K : Type u} [Field K] {m n : ℕ}
variable (invK : K → K)

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6 (the elimination
-- step fixes the pivot row); pointwise peel of `matRowElim`.
/-- Matrix–vector product after an elimination step at the pivot row. -/
theorem applyMat_rowElim_self (A : FreeMatrix K n m) (r : Fin n) (j : Fin m) (x : FreeMod K m) :
    applyMat (matRowElim A r j) x r = applyMat A x r :=
  Eq.trans (applyMat_eq_listSum (matRowElim A r j) x r)
    (Eq.trans (list_sum_map_congr_mem (List.finRange m)
        (fun c _ => congrArg (fun t => t * x c) (matRowElim_self A r j c)))
      (applyMat_eq_listSum A x r).symm)

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6 (the elimination
-- step subtracts a multiple of the pivot row off row `a`); pointwise peel.
/-- Pointwise: the elimination summand at row `a ≠ r` is the original summand
minus `A a j` times the pivot summand. -/
theorem matRowElim_mul_apply (A : FreeMatrix K n m) (r a : Fin n) (h : a ≠ r) (j c : Fin m)
    (x : FreeMod K m) :
    matRowElim A r j a c * x c = A a c * x c - A a j * (A r c * x c) :=
  Eq.trans (congrArg (fun t => t * x c) (matRowElim_other A r a h j c))
    (Eq.trans (sub_mul (A a c) (A a j * A r c) (x c))
      (congrArg (fun t => A a c * x c - t) (mul_assoc (A a j) (A r c) (x c))))

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6 (the elimination
-- step subtracts a multiple of the pivot row off row `a`).
/-- Matrix–vector product after an elimination step at an off-pivot row. -/
theorem applyMat_rowElim_other (A : FreeMatrix K n m) (r a : Fin n) (h : a ≠ r) (j : Fin m)
    (x : FreeMod K m) :
    applyMat (matRowElim A r j) x a = applyMat A x a - A a j * applyMat A x r := by
  have hsum : ((List.finRange m).map (fun c => matRowElim A r j a c * x c)).sum
      = ((List.finRange m).map (fun c => A a c * x c - A a j * (A r c * x c))).sum :=
    list_sum_map_congr_mem (List.finRange m) (fun c _ => matRowElim_mul_apply A r a h j c x)
  have hsub : ((List.finRange m).map (fun c => A a c * x c - A a j * (A r c * x c))).sum
      = ((List.finRange m).map (fun c => A a c * x c)).sum
        - ((List.finRange m).map (fun c => A a j * (A r c * x c))).sum :=
    list_sum_map_sub (List.finRange m) (fun c => A a c * x c) (fun c => A a j * (A r c * x c))
  have hfactor : ((List.finRange m).map (fun c => A a j * (A r c * x c))).sum
      = A a j * ((List.finRange m).map (fun c => A r c * x c)).sum :=
    list_sum_map_mul_left (List.finRange m) (A a j) (fun c => A r c * x c)
  have hSa : ((List.finRange m).map (fun c => A a c * x c)).sum = applyMat A x a :=
    (applyMat_eq_listSum A x a).symm
  have hSr : ((List.finRange m).map (fun c => A r c * x c)).sum = applyMat A x r :=
    (applyMat_eq_listSum A x r).symm
  exact Eq.trans (applyMat_eq_listSum (matRowElim A r j) x a)
    (Eq.trans hsum (Eq.trans hsub (Eq.trans
      (congrArg (fun t => ((List.finRange m).map (fun c => A a c * x c)).sum - t) hfactor)
      (Eq.trans (congrArg (fun t => t - A a j * ((List.finRange m).map (fun c => A r c * x c)).sum)
        hSa)
        (congrArg (fun t => applyMat A x a - A a j * t) hSr)))))

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6 (the elimination
-- step is invertible: add the pivot row back); forward direction.
/-- Vanishing after an elimination step implies vanishing before it. -/
theorem applyMat_eq_zero_of_rowElim_eq_zero (A : FreeMatrix K n m) (r : Fin n) (j : Fin m)
    (x : FreeMod K m) (h : applyMat (matRowElim A r j) x = 0) :
    applyMat A x = 0 := by
  have h0 : ∀ b : Fin n, applyMat (matRowElim A r j) x b = 0 := fun b => congrFun h b
  have hr0 : applyMat A x r = 0 := Eq.trans (applyMat_rowElim_self A r j x).symm (h0 r)
  funext a
  cases (inferInstance : Decidable (a = r)) with
  | isTrue har =>
      have har' : r = a := har.symm
      subst har'
      exact hr0
  | isFalse har =>
      have helim : applyMat (matRowElim A r j) x a = applyMat A x a - A a j * applyMat A x r :=
        applyMat_rowElim_other A r a har j x
      have h0a : applyMat (matRowElim A r j) x a = 0 := h0 a
      have hD : applyMat A x a - A a j * applyMat A x r = 0 := Eq.trans helim.symm h0a
      have h1 : applyMat A x a - A a j * applyMat A x r = applyMat A x a - A a j * 0 :=
        congrArg (fun t => applyMat A x a - A a j * t) hr0
      have h2 : applyMat A x a - A a j * (0 : K) = applyMat A x a - 0 :=
        congrArg (fun t => applyMat A x a - t) (mul_zero (A a j))
      have h3 : applyMat A x a - (0 : K) = applyMat A x a := sub_zero (applyMat A x a)
      exact Eq.trans (Eq.trans h1 (Eq.trans h2 h3)).symm hD

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6 (the elimination
-- step is invertible: add the pivot row back); backward direction.
/-- Vanishing before an elimination step implies vanishing after it. -/
theorem applyMat_rowElim_eq_zero_of_eq_zero (A : FreeMatrix K n m) (r : Fin n) (j : Fin m)
    (x : FreeMod K m) (h : applyMat A x = 0) :
    applyMat (matRowElim A r j) x = 0 := by
  have k0 : ∀ b : Fin n, applyMat A x b = 0 := fun b => congrFun h b
  funext b
  cases (inferInstance : Decidable (b = r)) with
  | isTrue hbr =>
      have hbr' : r = b := hbr.symm
      subst hbr'
      exact Eq.trans (applyMat_rowElim_self A r j x) (k0 r)
  | isFalse hbr =>
      have helim : applyMat (matRowElim A r j) x b = applyMat A x b - A b j * applyMat A x r :=
        applyMat_rowElim_other A r b hbr j x
      have hkr : applyMat A x r = 0 := k0 r
      have h1 : applyMat A x b - A b j * applyMat A x r = applyMat A x b - A b j * 0 :=
        congrArg (fun t => applyMat A x b - A b j * t) hkr
      have h2 : applyMat A x b - A b j * (0 : K) = applyMat A x b - 0 :=
        congrArg (fun t => applyMat A x b - t) (mul_zero (A b j))
      have h3 : applyMat A x b - (0 : K) = applyMat A x b := sub_zero (applyMat A x b)
      have kb : applyMat A x b = 0 := k0 b
      exact Eq.trans helim (Eq.trans h1 (Eq.trans h2 (Eq.trans h3 kb)))

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6 (the elimination
-- step is invertible: add the pivot row back).
/-- An elimination step preserves `applyMat _ x = 0`. -/
theorem applyMat_rowElim_eq_zero_iff (A : FreeMatrix K n m) (r : Fin n) (j : Fin m)
    (x : FreeMod K m) :
    applyMat (matRowElim A r j) x = 0 ↔ applyMat A x = 0 :=
  ⟨applyMat_eq_zero_of_rowElim_eq_zero A r j x, applyMat_rowElim_eq_zero_of_eq_zero A r j x⟩

-- Reference: RowReduction.lean (the `invK` contract `hinv`); a left inverse
-- of a nonzero element is nonzero.
/-- The explicit inverse of a nonzero element is nonzero. -/
theorem invK_ne_zero (hinv : ∀ a : K, a ≠ 0 → invK a * a = 1) {a : K} (h : a ≠ 0) :
    invK a ≠ 0 := by
  intro h0
  have hh : invK a * a = 1 := hinv a h
  have hh' : (0 : K) = 1 :=
    Eq.trans (zero_mul a).symm (Eq.trans (congrArg (fun t => t * a) h0).symm hh)
  exact absurd hh'.symm one_ne_zero

end BoringMath
