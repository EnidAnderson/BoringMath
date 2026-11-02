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
# Row scalings preserve the annihilation predicate (P.2.2, part 6)

Piece 6 of `BoringMath.FormalPeriods.KernelImage`: `applyMat` after
`matRowScale` at the scaled row, and preservation of
`applyMat _ x = 0` under scaling a row by a nonzero scalar (via the
`invK` contract).
-/

universe u

namespace BoringMath

variable {K : Type u} [Field K] {m n : ℕ}
variable (invK : K → K)


-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6 (row scaling);
-- pointwise peel of `matRowScale`.
/-- Matrix–vector product after a row scaling. -/
theorem applyMat_rowScale_apply (A : FreeMatrix K n m) (r : Fin n) (s : K) (x : FreeMod K m)
    (a : Fin n) :
    applyMat (matRowScale A r s) x a =
      (if a = r then s * applyMat A x a else applyMat A x a) := by
  cases (inferInstance : Decidable (a = r)) with
  | isTrue har =>
      have har' : r = a := har.symm
      subst har'
      have hsum : ((List.finRange m).map (fun j => matRowScale A r s r j * x j)).sum
          = ((List.finRange m).map (fun j => s * (A r j * x j))).sum :=
        list_sum_map_congr_mem (List.finRange m)
          (fun j _ => Eq.trans (congrArg (fun t => t * x j) (matRowScale_self A r s j))
            (mul_assoc s (A r j) (x j)))
      have hfactor : ((List.finRange m).map (fun j => s * (A r j * x j))).sum
          = s * ((List.finRange m).map (fun j => A r j * x j)).sum :=
        list_sum_map_mul_left (List.finRange m) s (fun j => A r j * x j)
      have hite : (if r = r then s * applyMat A x r else applyMat A x r) = s * applyMat A x r :=
        ite_eq_left rfl
      exact Eq.trans (applyMat_eq_listSum (matRowScale A r s) x r)
        (Eq.trans hsum (Eq.trans hfactor
          (Eq.trans (congrArg (fun t => s * t) (applyMat_eq_listSum A x r).symm) hite.symm)))
  | isFalse har =>
      have hsum : ((List.finRange m).map (fun j => matRowScale A r s a j * x j)).sum
          = ((List.finRange m).map (fun j => A a j * x j)).sum :=
        list_sum_map_congr_mem (List.finRange m)
          (fun j _ => congrArg (fun t => t * x j) (matRowScale_other A r a har s j))
      have hite : (if a = r then s * applyMat A x a else applyMat A x a) = applyMat A x a :=
        ite_eq_right har
      exact Eq.trans (applyMat_eq_listSum (matRowScale A r s) x a)
        (Eq.trans hsum (Eq.trans (applyMat_eq_listSum A x a).symm hite.symm))

-- Reference: RowReduction.lean (the `invK` contract `hinv`: the explicit
-- inverse is a left inverse of every nonzero element); Axler, Ch. 1. The
-- mathlib `NoZeroDivisors` instance of a general `Field` is
-- `Classical.choice`-tainted at the pin, so the cancellation is proved
-- through the explicit `invK` instead of `mul_eq_zero`.
/-- In a field with explicit inverses, `s * y = 0` with `s ≠ 0` forces
`y = 0`. -/
theorem eq_zero_of_mul_eq_zero_of_ne_zero (hinv : ∀ a : K, a ≠ 0 → invK a * a = 1)
    {s y : K} (hs : s ≠ 0) (h : s * y = 0) :
    y = 0 :=
  calc y = 1 * y := (one_mul y).symm
    _ = (invK s * s) * y := congrArg (fun t => t * y) (hinv s hs).symm
    _ = invK s * (s * y) := mul_assoc _ _ _
    _ = invK s * 0 := congrArg (fun t => invK s * t) h
    _ = 0 := mul_zero _

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6 (scaling by a
-- nonzero scalar is invertible); the scaled row equation at `r`; same anchor
-- as `applyMat_rowScale_eq_zero_iff`.
/-- If the scaled product vanishes everywhere, the original product vanishes
at the scaled row `r` (cancellation through `invK`). -/
theorem applyMat_eq_zero_of_rowScale_eq_zero_r (hinv : ∀ a : K, a ≠ 0 → invK a * a = 1)
    (A : FreeMatrix K n m) (r : Fin n) (s : K) (x : FreeMod K m) (hs : s ≠ 0)
    (h0 : ∀ b : Fin n, applyMat (matRowScale A r s) x b = 0) :
    applyMat A x r = 0 := by
  have hswap : applyMat (matRowScale A r s) x r
      = (if r = r then s * applyMat A x r else applyMat A x r) := applyMat_rowScale_apply A r s x r
  have h0r : applyMat (matRowScale A r s) x r = 0 := h0 r
  have hite : (if r = r then s * applyMat A x r else applyMat A x r) = s * applyMat A x r :=
    ite_eq_left rfl
  have hmul : s * applyMat A x r = 0 := Eq.trans hite.symm (Eq.trans hswap.symm h0r)
  exact eq_zero_of_mul_eq_zero_of_ne_zero invK hinv hs hmul

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6 (rows outside the
-- scaled row are unchanged); same anchor as `applyMat_rowScale_eq_zero_iff`.
/-- If the scaled product vanishes everywhere, the original product vanishes
at any other row `a`. -/
theorem applyMat_eq_zero_of_rowScale_eq_zero_other (A : FreeMatrix K n m) (r a : Fin n)
    (har : a ≠ r) (s : K) (x : FreeMod K m)
    (h0 : ∀ b : Fin n, applyMat (matRowScale A r s) x b = 0) :
    applyMat A x a = 0 := by
  have hswap : applyMat (matRowScale A r s) x a
      = (if a = r then s * applyMat A x a else applyMat A x a) := applyMat_rowScale_apply A r s x a
  have h0a : applyMat (matRowScale A r s) x a = 0 := h0 a
  have hite : (if a = r then s * applyMat A x a else applyMat A x a) = applyMat A x a :=
    ite_eq_right har
  exact Eq.trans hite.symm (Eq.trans hswap.symm h0a)

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6; case analysis on
-- the row index, each branch one named peel; same anchor as
-- `applyMat_rowScale_eq_zero_iff`.
/-- If the scaled product vanishes everywhere, the original product vanishes
at the row `a`. -/
theorem applyMat_eq_zero_of_rowScale_eq_zero_at (hinv : ∀ a : K, a ≠ 0 → invK a * a = 1)
    (A : FreeMatrix K n m) (r : Fin n) (s : K) (a : Fin n) (x : FreeMod K m) (hs : s ≠ 0)
    (h0 : ∀ b : Fin n, applyMat (matRowScale A r s) x b = 0) :
    applyMat A x a = 0 := by
  cases (inferInstance : Decidable (a = r)) with
  | isTrue har =>
      have har' : r = a := har.symm
      subst har'
      exact applyMat_eq_zero_of_rowScale_eq_zero_r invK hinv A r s x hs h0
  | isFalse har =>
      exact applyMat_eq_zero_of_rowScale_eq_zero_other A r a har s x h0

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6 (scaling by a
-- nonzero scalar is invertible); forward direction.
/-- Vanishing after a nonzero row scaling implies vanishing before it. -/
theorem applyMat_eq_zero_of_rowScale_eq_zero (hinv : ∀ a : K, a ≠ 0 → invK a * a = 1)
    (A : FreeMatrix K n m) (r : Fin n) (s : K) (x : FreeMod K m) (hs : s ≠ 0)
    (h : applyMat (matRowScale A r s) x = 0) :
    applyMat A x = 0 := by
  have h0 : ∀ b : Fin n, applyMat (matRowScale A r s) x b = 0 := fun b => congrFun h b
  funext a
  exact applyMat_eq_zero_of_rowScale_eq_zero_at invK hinv A r s a x hs h0

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6 (scaling by a
-- nonzero scalar is invertible); backward direction.
/-- Vanishing before a row scaling implies vanishing after it. -/
theorem applyMat_rowScale_eq_zero_of_eq_zero (A : FreeMatrix K n m) (r : Fin n) (s : K)
    (x : FreeMod K m) (h : applyMat A x = 0) :
    applyMat (matRowScale A r s) x = 0 := by
  have k0 : ∀ b : Fin n, applyMat A x b = 0 := fun b => congrFun h b
  funext b
  cases (inferInstance : Decidable (b = r)) with
  | isTrue hbr =>
      have hbr' : r = b := hbr.symm
      subst hbr'
      have hswap : applyMat (matRowScale A r s) x r
          = (if r = r then s * applyMat A x r else applyMat A x r) :=
        applyMat_rowScale_apply A r s x r
      have hite : (if r = r then s * applyMat A x r else applyMat A x r) = s * applyMat A x r :=
        ite_eq_left rfl
      have hkr : applyMat A x r = 0 := k0 r
      have hsz : s * (0 : K) = 0 := mul_zero s
      exact Eq.trans hswap (Eq.trans hite (Eq.trans (congrArg (fun t => s * t) hkr) hsz))
  | isFalse hbr =>
      have hswap : applyMat (matRowScale A r s) x b
          = (if b = r then s * applyMat A x b else applyMat A x b) :=
        applyMat_rowScale_apply A r s x b
      have hite : (if b = r then s * applyMat A x b else applyMat A x b) = applyMat A x b :=
        ite_eq_right hbr
      have kb : applyMat A x b = 0 := k0 b
      exact Eq.trans hswap (Eq.trans hite kb)

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6 (scaling by a
-- nonzero scalar is invertible).
/-- Scaling a row by a nonzero scalar preserves `applyMat _ x = 0`. -/
theorem applyMat_rowScale_eq_zero_iff
    (hinv : ∀ a : K, a ≠ 0 → invK a * a = 1) (A : FreeMatrix K n m) (r : Fin n) (s : K)
    (x : FreeMod K m) (hs : s ≠ 0) :
    applyMat (matRowScale A r s) x = 0 ↔ applyMat A x = 0 :=
  ⟨applyMat_eq_zero_of_rowScale_eq_zero invK hinv A r s x hs,
    applyMat_rowScale_eq_zero_of_eq_zero A r s x⟩


end BoringMath
