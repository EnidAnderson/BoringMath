/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Init
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Fin.Basic

/-!
# Matrices and elementary row operations (P.2.1, part 1)

Part 1 of `BoringMath.FormalPeriods.RowReduction`: the matrix type
`FreeMatrix` and the three elementary row operations (swap, scale,
elimination) with their pointwise peels and the pivot-entry lemmas.
-/

universe u

namespace BoringMath

variable {K : Type u} [Field K] {m n : ℕ}
variable (invK : K → K)

/-! ## Matrices and elementary row operations -/

-- Reference: Mines–Richman–Ruitenburg 2008, Pt. II Ch. 6 (a matrix over a
-- discrete field is an array of rows; TOC verified via SpringerLink).
/-- A matrix in `FreeMod` coordinates: the array form of a linear map
`FreeMod K n → FreeMod K m` in the standard basis; `A i` is row `i`. -/
abbrev FreeMatrix (K : Type u) [Field K] (m n : ℕ) := Fin m → Fin n → K

-- Reference: Mines–Richman–Ruitenburg 2008, Pt. II Ch. 6 (elementary row
-- operations over a discrete field).
/-- Swap rows `r` and `i` of `A`. -/
def matRowSwap (A : FreeMatrix K m n) (r i : Fin m) : FreeMatrix K m n :=
  fun a c => if a = r then A i c else if a = i then A r c else A a c

-- Reference: Mines–Richman–Ruitenburg 2008, Pt. II Ch. 6.
/-- Scale row `r` of `A` by the scalar `s`. -/
def matRowScale (A : FreeMatrix K m n) (r : Fin m) (s : K) : FreeMatrix K m n :=
  fun a c => if a = r then s * A a c else A a c

-- Reference: Mines–Richman–Ruitenburg 2008, Pt. II Ch. 6.
/-- Subtract `A a j` times the pivot row `r` from row `a`: the elementary
elimination step at the pivot `(r, j)`. -/
def matRowElim (A : FreeMatrix K m n) (r : Fin m) (j : Fin n) : FreeMatrix K m n :=
  fun a c => if a = r then A a c else A a c - A a j * A r c

-- Reference: definitional peel of `matRowSwap` (eta/ite reduction).
/-- Pointwise unfolding of `matRowSwap`. -/
theorem matRowSwap_apply (A : FreeMatrix K m n) (r i a : Fin m) (c : Fin n) :
    matRowSwap A r i a c = (if a = r then A i c else if a = i then A r c else A a c) :=
  rfl

-- Reference: definitional peel of `matRowSwap_apply` at `a = r`.
/-- `matRowSwap` sends the row `r` to the old row `i`. -/
theorem matRowSwap_left (A : FreeMatrix K m n) (r i : Fin m) (c : Fin n) :
    matRowSwap A r i r c = A i c :=
  ite_eq_left rfl

-- Reference: definitional peel of `matRowSwap_apply` at `a = i`, `i ≠ r`.
/-- `matRowSwap` sends the row `i` to the old row `r` (when `i ≠ r`). -/
theorem matRowSwap_right (A : FreeMatrix K m n) (r i : Fin m) (h : i ≠ r) (c : Fin n) :
    matRowSwap A r i i c = A r c :=
  (ite_eq_right h).trans (ite_eq_left rfl)

-- Reference: definitional peel of `matRowSwap_apply` at `a ∉ {r, i}`.
/-- `matRowSwap` fixes every other row. -/
theorem matRowSwap_other (A : FreeMatrix K m n) (r i a : Fin m) (hr : a ≠ r) (hi : a ≠ i)
    (c : Fin n) :
    matRowSwap A r i a c = A a c :=
  (ite_eq_right hr).trans (ite_eq_right hi)

-- Reference: definitional peel of `matRowSwap_apply` at `i = r`.
/-- Swapping a row with itself is the identity. -/
theorem matRowSwap_diag (A : FreeMatrix K m n) (r a : Fin m) (c : Fin n) :
    matRowSwap A r r a c = A a c := by
  cases (inferInstance : Decidable (a = r)) with
  | isTrue h =>
      -- Former rw [h]: rule `h : a = r`, fully instantiated; `a` occurs twice in
      -- the goal but uniformly, so one Eq.subst with the pair motive transports
      -- the whole goal; at `r` it is the named peel `ite_eq_left rfl`.
      exact Eq.subst (motive := fun x => matRowSwap A r r x c = A x c) h.symm
        (ite_eq_left rfl)
  | isFalse h => exact (ite_eq_right h).trans (ite_eq_right h)

-- Reference: definitional peel of `matRowScale` at `a = r`.
/-- `matRowScale` scales the row `r`. -/
theorem matRowScale_self (A : FreeMatrix K m n) (r : Fin m) (s : K) (c : Fin n) :
    matRowScale A r s r c = s * A r c :=
  ite_eq_left rfl

-- Reference: definitional peel of `matRowScale` at `a ≠ r`.
/-- `matRowScale` fixes every other row. -/
theorem matRowScale_other (A : FreeMatrix K m n) (r a : Fin m) (h : a ≠ r) (s : K)
    (c : Fin n) :
    matRowScale A r s a c = A a c :=
  ite_eq_right h

-- Reference: definitional peel of `matRowElim` at `a = r`.
/-- `matRowElim` fixes the pivot row. -/
theorem matRowElim_self (A : FreeMatrix K m n) (r : Fin m) (j c : Fin n) :
    matRowElim A r j r c = A r c :=
  ite_eq_left rfl

-- Reference: definitional peel of `matRowElim` at `a ≠ r`.
/-- `matRowElim` subtracts `A a j` times the pivot row from row `a`. -/
theorem matRowElim_other (A : FreeMatrix K m n) (r a : Fin m) (h : a ≠ r) (j c : Fin n) :
    matRowElim A r j a c = A a c - A a j * A r c :=
  ite_eq_right h

-- Reference: Mines–Richman–Ruitenburg 2008, Pt. II Ch. 6 (clearing the
-- pivot column); Axler, *Linear Algebra Done Right*, 4th ed., Ch. 1.
/-- The elimination step clears the pivot column in every other row when
the pivot entry is `1`. -/
theorem matRowElim_pivot_zero (A : FreeMatrix K m n) (r a : Fin m) (h : a ≠ r) (j : Fin n)
    (hp : A r j = 1) :
    matRowElim A r j a j = 0 := by
  -- Former rw [matRowElim_other A r a h j j]: named peel, fully instantiated;
  -- the LHS `matRowElim A r j a j` occurs once in the goal.
  have h1 : matRowElim A r j a j = A a j - A a j * A r j :=
    matRowElim_other A r a h j j
  -- Former rw [hp, mul_one, sub_self]: `A r j` occurs once, as the right factor
  -- of `A a j * …`; then `mul_one (A a j)` and `sub_self (A a j)` close the goal
  -- by congrArg/`trans`.
  exact h1.trans
    ((congrArg (fun t => A a j - A a j * t) hp).trans
      ((congrArg (fun t => A a j - t) (mul_one (A a j))).trans (sub_self (A a j))))

-- Reference: Mines–Richman–Ruitenburg 2008, Pt. II Ch. 6 (normalizing the
-- pivot to `1` over a field).
/-- After swapping the pivot row into place and scaling by the inverse of
the pivot entry, the pivot entry is `1`. -/
theorem rrefStep_pivot_one (hinv : ∀ a : K, a ≠ 0 → invK a * a = 1)
    (A : FreeMatrix K m n) (r i : Fin m) (c : Fin n) (h : A i c ≠ 0) :
    matRowScale (matRowSwap A r i) r (invK (A i c)) r c = 1 := by
  -- Former rw [matRowScale_self]: named peel, fully instantiated; the scaled
  -- pivot entry occurs once, as the LHS of the goal, so the step composes by
  -- `trans`.
  have h1 : matRowScale (matRowSwap A r i) r (invK (A i c)) r c
      = invK (A i c) * matRowSwap A r i r c :=
    matRowScale_self (matRowSwap A r i) r (invK (A i c)) c
  -- Former rw [matRowSwap_left]: named peel; `matRowSwap A r i r c` occurs once,
  -- as the right factor of `invK (A i c) * …`; then `hinv (A i c) h` closes it.
  have h2 : invK (A i c) * matRowSwap A r i r c = invK (A i c) * A i c :=
    congrArg (fun t => invK (A i c) * t) (matRowSwap_left A r i c)
  exact h1.trans (h2.trans (hinv (A i c) h))
