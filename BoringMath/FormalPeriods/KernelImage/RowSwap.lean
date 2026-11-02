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
# Row swaps preserve the annihilation predicate (P.2.2, part 5)

Piece 5 of `BoringMath.FormalPeriods.KernelImage`: `applyMat` after
`matRowSwap` is the permuted product, hence the predicate
`applyMat _ x = 0` is preserved in both directions.
-/

universe u

namespace BoringMath

variable {K : Type u} [Field K] {m n : ℕ}

/-! ## Row operations preserve the annihilation predicate `applyMat _ x = 0` -/

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6 (row swap permutes
-- the equations); pointwise peel of `matRowSwap`.
/-- Matrix–vector product after a row swap is the permuted product. -/
theorem applyMat_rowSwap_apply (A : FreeMatrix K n m) (r i : Fin n) (x : FreeMod K m)
    (a : Fin n) :
    applyMat (matRowSwap A r i) x a =
      (if a = r then applyMat A x i else if a = i then applyMat A x r else applyMat A x a) := by
  cases (inferInstance : Decidable (a = r)) with
  | isTrue har =>
      have har' : r = a := har.symm
      subst har'
      have hsum : ((List.finRange m).map (fun j => matRowSwap A r i r j * x j)).sum
          = ((List.finRange m).map (fun j => A i j * x j)).sum :=
        list_sum_map_congr_mem (List.finRange m)
          (fun j _ => congrArg (fun t => t * x j) (matRowSwap_left A r i j))
      have hite : (if r = r then applyMat A x i else if r = i then applyMat A x r
          else applyMat A x r) = applyMat A x i := ite_eq_left rfl
      exact Eq.trans (applyMat_eq_listSum (matRowSwap A r i) x r)
        (Eq.trans hsum (Eq.trans (applyMat_eq_listSum A x i).symm hite.symm))
  | isFalse har =>
      cases (inferInstance : Decidable (a = i)) with
      | isTrue hai =>
          have hne : i ≠ r := fun h => har (hai.trans h)
          have hai' : i = a := hai.symm
          subst hai'
          have hsum : ((List.finRange m).map (fun j => matRowSwap A r i i j * x j)).sum
              = ((List.finRange m).map (fun j => A r j * x j)).sum :=
            list_sum_map_congr_mem (List.finRange m)
              (fun j _ => congrArg (fun t => t * x j) (matRowSwap_right A r i hne j))
          have hite1 : (if i = r then applyMat A x i else if i = i then applyMat A x r
              else applyMat A x i) = (if i = i then applyMat A x r else applyMat A x i) :=
            ite_eq_right hne
          have hite2 : (if i = i then applyMat A x r else applyMat A x i) = applyMat A x r :=
            ite_eq_left rfl
          exact Eq.trans (applyMat_eq_listSum (matRowSwap A r i) x i)
            (Eq.trans hsum (Eq.trans (applyMat_eq_listSum A x r).symm
              (Eq.trans hite1 hite2).symm))
      | isFalse hai =>
          have hsum : ((List.finRange m).map (fun j => matRowSwap A r i a j * x j)).sum
              = ((List.finRange m).map (fun j => A a j * x j)).sum :=
            list_sum_map_congr_mem (List.finRange m)
              (fun j _ => congrArg (fun t => t * x j) (matRowSwap_other A r i a har hai j))
          have hite1 : (if a = r then applyMat A x i else if a = i then applyMat A x r
              else applyMat A x a) = (if a = i then applyMat A x r else applyMat A x a) :=
            ite_eq_right har
          have hite2 : (if a = i then applyMat A x r else applyMat A x a) = applyMat A x a :=
            ite_eq_right hai
          exact Eq.trans (applyMat_eq_listSum (matRowSwap A r i) x a)
            (Eq.trans hsum (Eq.trans (applyMat_eq_listSum A x a).symm
              (Eq.trans hite1 hite2).symm))

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6 (the swapped equation
-- at row `r` reads off old row `i`); same anchor as
-- `applyMat_rowSwap_eq_zero_iff`.
/-- If the row-swapped product vanishes everywhere, the original product
vanishes at row `r`. -/
theorem applyMat_eq_zero_of_rowSwap_eq_zero_r (A : FreeMatrix K n m) (r i : Fin n)
    (x : FreeMod K m) (h0 : ∀ b : Fin n, applyMat (matRowSwap A r i) x b = 0) :
    applyMat A x r = 0 := by
  cases (inferInstance : Decidable (i = r)) with
  | isTrue hir =>
      have hir' : r = i := hir.symm
      subst hir'
      have hswap : applyMat (matRowSwap A r r) x r
          = (if r = r then applyMat A x r else if r = r then applyMat A x r
            else applyMat A x r) := applyMat_rowSwap_apply A r r x r
      have h0r : applyMat (matRowSwap A r r) x r = 0 := h0 r
      have hite : (if r = r then applyMat A x r else if r = r then applyMat A x r
          else applyMat A x r) = applyMat A x r := ite_eq_left rfl
      exact Eq.trans hite.symm (Eq.trans hswap.symm h0r)
  | isFalse hir =>
      have hswap : applyMat (matRowSwap A r i) x i
          = (if i = r then applyMat A x i else if i = i then applyMat A x r
            else applyMat A x i) := applyMat_rowSwap_apply A r i x i
      have h0i : applyMat (matRowSwap A r i) x i = 0 := h0 i
      have hite1 : (if i = r then applyMat A x i else if i = i then applyMat A x r
          else applyMat A x i) = (if i = i then applyMat A x r else applyMat A x i) :=
        ite_eq_right hir
      have hite2 : (if i = i then applyMat A x r else applyMat A x i) = applyMat A x r :=
        ite_eq_left rfl
      exact Eq.trans (Eq.trans hite1 hite2).symm (Eq.trans hswap.symm h0i)

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6 (the swapped equation
-- at row `i` reads off old row `r`); same anchor as
-- `applyMat_rowSwap_eq_zero_iff`.
/-- If the row-swapped product vanishes everywhere, the original product
vanishes at row `i`. -/
theorem applyMat_eq_zero_of_rowSwap_eq_zero_i (A : FreeMatrix K n m) (r i : Fin n)
    (x : FreeMod K m) (h0 : ∀ b : Fin n, applyMat (matRowSwap A r i) x b = 0) :
    applyMat A x i = 0 := by
  have hswap : applyMat (matRowSwap A r i) x r
      = (if r = r then applyMat A x i else if r = i then applyMat A x r else applyMat A x r) :=
    applyMat_rowSwap_apply A r i x r
  have h0r : applyMat (matRowSwap A r i) x r = 0 := h0 r
  have hite : (if r = r then applyMat A x i else if r = i then applyMat A x r
      else applyMat A x r) = applyMat A x i := ite_eq_left rfl
  exact Eq.trans hite.symm (Eq.trans hswap.symm h0r)

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6 (rows outside the
-- swap are unchanged); same anchor as `applyMat_rowSwap_eq_zero_iff`.
/-- If the row-swapped product vanishes everywhere, the original product
vanishes at any other row `a`. -/
theorem applyMat_eq_zero_of_rowSwap_eq_zero_other (A : FreeMatrix K n m) (r i a : Fin n)
    (har : a ≠ r) (hai : a ≠ i) (x : FreeMod K m)
    (h0 : ∀ b : Fin n, applyMat (matRowSwap A r i) x b = 0) :
    applyMat A x a = 0 := by
  have hswap : applyMat (matRowSwap A r i) x a
      = (if a = r then applyMat A x i else if a = i then applyMat A x r else applyMat A x a) :=
    applyMat_rowSwap_apply A r i x a
  have h0a : applyMat (matRowSwap A r i) x a = 0 := h0 a
  have hite1 : (if a = r then applyMat A x i else if a = i then applyMat A x r
      else applyMat A x a) = (if a = i then applyMat A x r else applyMat A x a) := ite_eq_right har
  have hite2 : (if a = i then applyMat A x r else applyMat A x a) = applyMat A x a :=
    ite_eq_right hai
  exact Eq.trans (Eq.trans hite1 hite2).symm (Eq.trans hswap.symm h0a)

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6; case analysis on
-- the row index, each branch one named peel; same anchor as
-- `applyMat_rowSwap_eq_zero_iff`.
/-- If the row-swapped product vanishes everywhere, the original product
vanishes at the row `a`. -/
theorem applyMat_eq_zero_of_rowSwap_eq_zero_at (A : FreeMatrix K n m) (r i a : Fin n)
    (x : FreeMod K m) (h0 : ∀ b : Fin n, applyMat (matRowSwap A r i) x b = 0) :
    applyMat A x a = 0 := by
  cases (inferInstance : Decidable (a = r)) with
  | isTrue har =>
      have har' : r = a := har.symm
      subst har'
      exact applyMat_eq_zero_of_rowSwap_eq_zero_r A r i x h0
  | isFalse har =>
      cases (inferInstance : Decidable (a = i)) with
      | isTrue hai =>
          have hai' : i = a := hai.symm
          subst hai'
          exact applyMat_eq_zero_of_rowSwap_eq_zero_i A r i x h0
      | isFalse hai =>
          exact applyMat_eq_zero_of_rowSwap_eq_zero_other A r i a har hai x h0

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6 (row swaps are
-- invertible, so the solution set is unchanged); forward direction.
/-- Vanishing after a row swap implies vanishing before it. -/
theorem applyMat_eq_zero_of_rowSwap_eq_zero (A : FreeMatrix K n m) (r i : Fin n)
    (x : FreeMod K m) (h : applyMat (matRowSwap A r i) x = 0) :
    applyMat A x = 0 := by
  have h0 : ∀ b : Fin n, applyMat (matRowSwap A r i) x b = 0 := fun b => congrFun h b
  funext a
  exact applyMat_eq_zero_of_rowSwap_eq_zero_at A r i a x h0

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6; case analysis on
-- the row index, each branch one named equation; same anchor as
-- `applyMat_rowSwap_eq_zero_iff`.
/-- If the original product vanishes everywhere, the row-swapped product
vanishes at the row `b`. -/
theorem applyMat_rowSwap_eq_zero_at (A : FreeMatrix K n m) (r i b : Fin n)
    (x : FreeMod K m) (k0 : ∀ c : Fin n, applyMat A x c = 0) :
    applyMat (matRowSwap A r i) x b = 0 := by
  cases (inferInstance : Decidable (b = r)) with
  | isTrue hbr =>
      have hbr' : r = b := hbr.symm
      subst hbr'
      have hswap : applyMat (matRowSwap A r i) x r
          = (if r = r then applyMat A x i else if r = i then applyMat A x r
            else applyMat A x r) := applyMat_rowSwap_apply A r i x r
      have hite : (if r = r then applyMat A x i else if r = i then applyMat A x r
          else applyMat A x r) = applyMat A x i := ite_eq_left rfl
      have ki : applyMat A x i = 0 := k0 i
      exact Eq.trans hswap (Eq.trans hite ki)
  | isFalse hbr =>
      cases (inferInstance : Decidable (b = i)) with
      | isTrue hbi =>
          have hbi' : i = b := hbi.symm
          subst hbi'
          have hswap : applyMat (matRowSwap A r i) x i
              = (if i = r then applyMat A x i else if i = i then applyMat A x r
                else applyMat A x i) := applyMat_rowSwap_apply A r i x i
          have hite1 : (if i = r then applyMat A x i else if i = i then applyMat A x r
              else applyMat A x i) = (if i = i then applyMat A x r else applyMat A x i) :=
            ite_eq_right hbr
          have hite2 : (if i = i then applyMat A x r else applyMat A x i) = applyMat A x r :=
            ite_eq_left rfl
          have kr : applyMat A x r = 0 := k0 r
          exact Eq.trans hswap (Eq.trans (Eq.trans hite1 hite2) kr)
      | isFalse hbi =>
          have hswap : applyMat (matRowSwap A r i) x b
              = (if b = r then applyMat A x i else if b = i then applyMat A x r
                else applyMat A x b) := applyMat_rowSwap_apply A r i x b
          have hite1 : (if b = r then applyMat A x i else if b = i then applyMat A x r
              else applyMat A x b) = (if b = i then applyMat A x r else applyMat A x b) :=
            ite_eq_right hbr
          have hite2 : (if b = i then applyMat A x r else applyMat A x b) = applyMat A x b :=
            ite_eq_right hbi
          have kb : applyMat A x b = 0 := k0 b
          exact Eq.trans hswap (Eq.trans (Eq.trans hite1 hite2) kb)

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6 (row swaps are
-- invertible, so the solution set is unchanged); backward direction.
/-- Vanishing before a row swap implies vanishing after it. -/
theorem applyMat_rowSwap_eq_zero_of_eq_zero (A : FreeMatrix K n m) (r i : Fin n)
    (x : FreeMod K m) (h : applyMat A x = 0) :
    applyMat (matRowSwap A r i) x = 0 := by
  have k0 : ∀ b : Fin n, applyMat A x b = 0 := fun b => congrFun h b
  funext b
  exact applyMat_rowSwap_eq_zero_at A r i b x k0

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6 (row swaps are
-- invertible, so the solution set is unchanged).
/-- A row swap preserves the predicate `applyMat _ x = 0`. -/
theorem applyMat_rowSwap_eq_zero_iff (A : FreeMatrix K n m) (r i : Fin n) (x : FreeMod K m) :
    applyMat (matRowSwap A r i) x = 0 ↔ applyMat A x = 0 :=
  ⟨applyMat_eq_zero_of_rowSwap_eq_zero A r i x, applyMat_rowSwap_eq_zero_of_eq_zero A r i x⟩

end BoringMath
