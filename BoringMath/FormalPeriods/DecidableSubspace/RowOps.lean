/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Init
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Data.Fin.Basic
import BoringMath.FormalPeriods.DecidableSubspace.RowSpan
import BoringMath.FormalPeriods.FreeMod
import BoringMath.FormalPeriods.RowReduction
/-!
# Row operations and the elimination loop preserve the row span (P.2.3, part 5)

Piece 5 of `BoringMath.FormalPeriods.DecidableSubspace`: the row-swap,
row-scale, and row-elimination steps preserve `inRowSpan`, and the whole
`rrefAux` elimination loop preserves it (`inRowSpan_rref`).
-/
universe u
namespace BoringMath
variable {K : Type u} [Field K] {m n k p : ℕ}
variable (invK : K → K)
variable [DecidableEq K]
/-! ## Row operations preserve the row span -/
-- Reference: definitional peel: the swapped rows as functions.
omit [DecidableEq K] in
/-- Row `r` of a swap is the old row `i`. -/
theorem matRowSwap_row_left (A : FreeMatrix K m n) (r i : Fin m) :
    matRowSwap A r i r = A i :=
  funext (matRowSwap_left A r i)
-- Reference: definitional peel: the swapped rows as functions.
omit [DecidableEq K] in
/-- Row `i` of a swap is the old row `r` (when `i ≠ r`). -/
theorem matRowSwap_row_right (A : FreeMatrix K m n) (r i : Fin m) (h : i ≠ r) :
    matRowSwap A r i i = A r :=
  funext (matRowSwap_right A r i h)
-- Reference: definitional peel: the swapped rows as functions.
omit [DecidableEq K] in
/-- Every other row of a swap is unchanged. -/
theorem matRowSwap_row_other (A : FreeMatrix K m n) (r i a : Fin m) (hr : a ≠ r) (hi : a ≠ i) :
    matRowSwap A r i a = A a :=
  funext (matRowSwap_other A r i a hr hi)
-- Reference: MRR 1988, Pt. II Ch. 6 (swapping rows preserves the row space);
-- the row goal of the forward direction.
omit [DecidableEq K] in
/-- Every row of the swapped matrix lies in the row span of the original. -/
theorem inRowSpan_swap_row_fwd {A : FreeMatrix K m n} {r i : Fin m} :
    ∀ a : Fin m, inRowSpan A (matRowSwap A r i a) :=
  fun a =>
    match (inferInstance : Decidable (a = r)) with
    | isTrue ha =>
        Eq.mpr (congrArg (inRowSpan A)
          ((congrArg (fun z => matRowSwap A r i z) ha).trans (matRowSwap_row_left A r i)))
          (inRowSpan_self A i)
    | isFalse ha =>
      match (inferInstance : Decidable (a = i)) with
      | isTrue ha2 =>
          let hir : i ≠ r := fun h_eq => ha (ha2.trans h_eq)
          Eq.mpr (congrArg (inRowSpan A)
            ((congrArg (fun z => matRowSwap A r i z) ha2).trans (matRowSwap_row_right A r i hir)))
            (inRowSpan_self A r)
      | isFalse ha2 =>
          Eq.mpr (congrArg (inRowSpan A) (matRowSwap_row_other A r i a ha ha2))
            (inRowSpan_self A a)
-- Reference: MRR 1988, Pt. II Ch. 6 (swapping rows preserves the row space);
-- the row goal of the backward direction.
omit [DecidableEq K] in
/-- Every row of the original matrix lies in the row span of the swapped one. -/
theorem inRowSpan_swap_row_bwd {A : FreeMatrix K m n} {r i : Fin m} :
    ∀ a : Fin m, inRowSpan (matRowSwap A r i) (A a) :=
  fun a =>
    match (inferInstance : Decidable (r = i)) with
    | isTrue hri =>
        let hswap : matRowSwap A r i = A := funext fun a' => funext fun c =>
          Eq.mp (congrArg (fun z => matRowSwap A r z a' c = A a' c) hri)
            (matRowSwap_diag A r a' c)
        Eq.mpr (congrArg (fun M => inRowSpan M (A a)) hswap) (inRowSpan_self A a)
    | isFalse hri =>
      match (inferInstance : Decidable (a = r)) with
      | isTrue ha =>
          let hir : i ≠ r := fun h => hri h.symm
          let e : A a = matRowSwap A r i i :=
            Eq.mpr (congrArg (fun z => A z = matRowSwap A r i i) ha)
              (matRowSwap_row_right A r i hir).symm
          Eq.mpr (congrArg (inRowSpan (matRowSwap A r i)) e) (inRowSpan_self _ i)
      | isFalse ha =>
        match (inferInstance : Decidable (a = i)) with
        | isTrue ha2 =>
            let e : A a = matRowSwap A r i r :=
              Eq.mpr (congrArg (fun z => A z = matRowSwap A r i r) ha2)
                (matRowSwap_row_left A r i).symm
            Eq.mpr (congrArg (inRowSpan (matRowSwap A r i)) e) (inRowSpan_self _ r)
        | isFalse ha2 =>
            Eq.mp (congrArg (inRowSpan (matRowSwap A r i))
              (matRowSwap_row_other A r i a ha ha2)) (inRowSpan_self _ a)
-- Reference: MRR 1988, Pt. II Ch. 6 (swapping rows preserves the row space).
omit [DecidableEq K] in
/-- Swapping two rows preserves the row span. -/
theorem inRowSpan_swap {A : FreeMatrix K m n} {r i : Fin m} {w : FreeMod K n} :
    inRowSpan (matRowSwap A r i) w ↔ inRowSpan A w :=
  ⟨fun h => inRowSpan_mono (B := A) _ (matRowSwap A r i) w inRowSpan_swap_row_fwd h,
   fun h => inRowSpan_mono (B := matRowSwap A r i) _ A w inRowSpan_swap_row_bwd h⟩
-- Reference: definitional peel: the scaled pivot row as a function.
omit [DecidableEq K] in
/-- The scaled row `r` is `s • A r`. -/
theorem matRowScale_row_self (A : FreeMatrix K m n) (r : Fin m) (s : K) :
    matRowScale A r s r = s • A r :=
  funext (fun c =>
    (matRowScale_self A r s c).trans
      ((Pi.smul_apply s (A r) c).trans (smul_eq_mul s (A r c))).symm)
-- Reference: definitional peel: the other rows of a scale are unchanged.
omit [DecidableEq K] in
/-- Every other row of a scale is unchanged. -/
theorem matRowScale_row_other (A : FreeMatrix K m n) (r a : Fin m) (h : a ≠ r) (s : K) :
    matRowScale A r s a = A a :=
  funext (matRowScale_other A r a h s)
-- Reference: MRR 1988, Pt. II Ch. 6 (the inverse of a nonzero scalar is at
-- hand as explicit data `invK`).
omit [DecidableEq K] in
/-- The explicit inverse of a nonzero scalar is nonzero. -/
theorem ne_zero_invK (hinv : ∀ a : K, a ≠ 0 → invK a * a = 1) {a : K} (ha : a ≠ 0) :
    invK a ≠ 0 := by
  intro h
  have h1 : (0 : K) = 1 :=
    Eq.mp (congrArg (fun z => z = 1) (zero_mul a))
      (Eq.mp (congrArg (fun z => z = 1) (congrArg (· * a) h)) (hinv a ha))
  exact absurd h1 zero_ne_one
-- Reference: MRR 1988, Pt. II Ch. 6 (scaling a row by a unit preserves the
-- row space); the row goal of the forward direction.
omit [DecidableEq K] in
/-- Every row of the scaled matrix lies in the row span of the original. -/
theorem inRowSpan_scale_row_fwd {A : FreeMatrix K m n} {r : Fin m} {s : K} :
    ∀ a : Fin m, inRowSpan A (matRowScale A r s a) :=
  fun a =>
    match (inferInstance : Decidable (a = r)) with
    | isTrue ha =>
        Eq.mpr (congrArg (inRowSpan A)
          ((congrArg (fun z => matRowScale A r s z) ha).trans (matRowScale_row_self A r s)))
          (inRowSpan_smul s (inRowSpan_self A r))
    | isFalse ha =>
        Eq.mpr (congrArg (inRowSpan A) (matRowScale_row_other A r a ha s))
          (inRowSpan_self A a)
-- Reference: MRR 1988, Pt. II Ch. 6 (scaling a row by a unit preserves the
-- row space); the row goal of the backward direction, pivot row.
omit [DecidableEq K] in
/-- The original pivot row is the scaled row times the explicit inverse. -/
theorem inRowSpan_scale_row_bwd_pivot (hinv : ∀ a : K, a ≠ 0 → invK a * a = 1)
    {A : FreeMatrix K m n} {r : Fin m} {s : K} (hs : s ≠ 0) :
    inRowSpan (matRowScale A r s) (A r) :=
  let hback : A r = invK s • matRowScale A r s r :=
    ((congrArg (invK s • ·) (matRowScale_row_self A r s)).trans
      ((smul_smul (invK s) s (A r)).trans
        ((congrArg (· • A r) (hinv s hs)).trans (one_smul K (A r))))).symm
  Eq.mpr (congrArg (inRowSpan (matRowScale A r s)) hback)
    (inRowSpan_smul (invK s) (inRowSpan_self _ r))
-- Reference: MRR 1988, Pt. II Ch. 6 (scaling a row by a unit preserves the
-- row space); the row goal of the backward direction, other rows.
omit [DecidableEq K] in
/-- Every other original row lies in the row span of the scaled matrix. -/
theorem inRowSpan_scale_row_bwd_other {A : FreeMatrix K m n} {r a : Fin m} {s : K}
    (ha : a ≠ r) : inRowSpan (matRowScale A r s) (A a) :=
  Eq.mp (congrArg (inRowSpan (matRowScale A r s)) (matRowScale_row_other A r a ha s))
    (inRowSpan_self _ a)
-- Reference: MRR 1988, Pt. II Ch. 6 (scaling a row by a unit preserves the
-- row space); the row goal of the backward direction. -/
omit [DecidableEq K] in
/-- Every original row lies in the row span of the scaled matrix. -/
theorem inRowSpan_scale_row_bwd (hinv : ∀ a : K, a ≠ 0 → invK a * a = 1)
    {A : FreeMatrix K m n} {r : Fin m} {s : K} (hs : s ≠ 0) :
    ∀ a : Fin m, inRowSpan (matRowScale A r s) (A a) :=
  fun a =>
    match (inferInstance : Decidable (a = r)) with
    | isTrue ha => Eq.mpr (congrArg (fun z => inRowSpan (matRowScale A r s) (A z)) ha)
        (inRowSpan_scale_row_bwd_pivot invK hinv hs)
    | isFalse ha => inRowSpan_scale_row_bwd_other ha
-- Reference: MRR 1988, Pt. II Ch. 6 (scaling a row by a unit preserves the
-- row space).
omit [DecidableEq K] in
/-- Scaling a row by a nonzero scalar preserves the row span. -/
theorem inRowSpan_scale (hinv : ∀ a : K, a ≠ 0 → invK a * a = 1) {A : FreeMatrix K m n}
    {r : Fin m} {s : K} (hs : s ≠ 0) {w : FreeMod K n} :
    inRowSpan (matRowScale A r s) w ↔ inRowSpan A w :=
  ⟨fun h => inRowSpan_mono (B := A) _ (matRowScale A r s) w inRowSpan_scale_row_fwd h,
   fun h => inRowSpan_mono (B := matRowScale A r s) _ A w (inRowSpan_scale_row_bwd invK hinv hs) h⟩
-- Reference: definitional peel: the pivot row of an elimination is unchanged.
omit [DecidableEq K] in
/-- The pivot row of `matRowElim` is the old row `r`. -/
theorem matRowElim_row_self (A : FreeMatrix K m n) (r : Fin m) (j : Fin n) :
    matRowElim A r j r = A r :=
  funext (matRowElim_self A r j)
-- Reference: definitional peel: the other rows of an elimination as
-- functions.
omit [DecidableEq K] in
/-- Row `a ≠ r` of an elimination is `A a - (A a j) • A r`. -/
theorem matRowElim_row_other (A : FreeMatrix K m n) (r a : Fin m) (h : a ≠ r) (j : Fin n) :
    matRowElim A r j a = A a - (A a j) • A r :=
  funext (fun c =>
    (matRowElim_other A r a h j c).trans
      ((congrArg (A a c - ·)
        ((Pi.smul_apply (A a j) (A r) c).trans (smul_eq_mul (A a j) (A r c))).symm).trans
      (Pi.sub_apply (A a) ((A a j) • A r) c).symm))
-- Reference: MRR 1988, Pt. II Ch. 6 (the elementary elimination step preserves
-- the row space); the row goal of the forward direction.
omit [DecidableEq K] in
/-- Every row of the eliminated matrix lies in the row span of the original. -/
theorem inRowSpan_elim_row_fwd {A : FreeMatrix K m n} {r : Fin m} {j : Fin n} :
    ∀ a : Fin m, inRowSpan A (matRowElim A r j a) :=
  fun a =>
    match (inferInstance : Decidable (a = r)) with
    | isTrue ha =>
        Eq.mpr (congrArg (inRowSpan A)
          ((congrArg (fun z => matRowElim A r j z) ha).trans (matRowElim_row_self A r j)))
          (inRowSpan_self A r)
    | isFalse ha =>
        Eq.mpr (congrArg (inRowSpan A) (matRowElim_row_other A r a ha j))
          (inRowSpan_sub (inRowSpan_self A a) (inRowSpan_smul (A a j) (inRowSpan_self A r)))
-- Reference: MRR 1988, Pt. II Ch. 6 (the elementary elimination step preserves
-- the row space); the row goal of the backward direction. -/
omit [DecidableEq K] in
/-- Every row of the original matrix lies in the row span of the eliminated
one. -/
theorem inRowSpan_elim_row_bwd {A : FreeMatrix K m n} {r : Fin m} {j : Fin n} :
    ∀ a : Fin m, inRowSpan (matRowElim A r j) (A a) :=
  fun a =>
    match (inferInstance : Decidable (a = r)) with
    | isTrue ha =>
        let e : A a = matRowElim A r j r :=
          Eq.mpr (congrArg (fun z => A z = matRowElim A r j r) ha)
            (matRowElim_row_self A r j).symm
        Eq.mpr (congrArg (inRowSpan (matRowElim A r j)) e) (inRowSpan_self _ r)
    | isFalse ha =>
        let hback : A a = matRowElim A r j a + (A a j) • matRowElim A r j r :=
          ((congrArg₂ (· + ·) (matRowElim_row_other A r a ha j)
            (congrArg ((A a j) • ·) (matRowElim_row_self A r j))).trans
            (sub_add_cancel (A a) ((A a j) • A r))).symm
        Eq.mpr (congrArg (inRowSpan (matRowElim A r j)) hback)
          (inRowSpan_add (inRowSpan_self _ a) (inRowSpan_smul (A a j) (inRowSpan_self _ r)))
-- Reference: MRR 1988, Pt. II Ch. 6 (the elementary elimination step preserves
-- the row space: the inverse step adds the multiple back).
omit [DecidableEq K] in
/-- The elementary elimination step preserves the row span. -/
theorem inRowSpan_elim {A : FreeMatrix K m n} {r : Fin m} {j : Fin n} {w : FreeMod K n} :
    inRowSpan (matRowElim A r j) w ↔ inRowSpan A w :=
  ⟨fun h => inRowSpan_mono (B := A) _ (matRowElim A r j) w inRowSpan_elim_row_fwd h,
   fun h => inRowSpan_mono (B := matRowElim A r j) _ A w inRowSpan_elim_row_bwd h⟩
/-! ## The elimination loop preserves the row span -/
-- Reference: MRR 1988, Pt. II Ch. 6 (each pass of Gaussian elimination is a
-- composition of row operations, so it preserves the row space); the step
-- of the loop with no pivot found in column `j`.
/-- The loop step with no pivot in column `j`: just advance the column. -/
theorem inRowSpan_rrefAux_step_none (hinv : ∀ a : K, a ≠ 0 → invK a * a = 1) (fuel : ℕ)
    (ih : ∀ r j (A : FreeMatrix K m n) (w : FreeMod K n),
      inRowSpan (rrefAux invK fuel r j A) w ↔ inRowSpan A w)
    (r j : ℕ) (hj : j < n) (A : FreeMatrix K m n) (w : FreeMod K n) :
    inRowSpan (rrefAux invK fuel r (j + 1) A) w ↔ inRowSpan A w :=
  ih r (j + 1) A w
-- Reference: MRR 1988, Pt. II Ch. 6 (each pass of Gaussian elimination is a
-- composition of row operations, so it preserves the row space); the step
-- of the loop with a pivot: swap, scale, eliminate, then recurse.
/-- The loop step with a pivot in column `j`: the row operations preserve the
span, then the recursion applies. -/
theorem inRowSpan_rrefAux_step_pivot (hinv : ∀ a : K, a ≠ 0 → invK a * a = 1) (fuel : ℕ)
    (ih : ∀ r j (A : FreeMatrix K m n) (w : FreeMod K n),
      inRowSpan (rrefAux invK fuel r j A) w ↔ inRowSpan A w)
    (r j : ℕ) (hj : j < n) (hr : r < m) (A : FreeMatrix K m n) (w : FreeMod K n)
    (i : Fin m)
    (hfp : findPivotRow
      (fun i => Nat.ble r i.val && (if A i ⟨j, hj⟩ ≠ 0 then true else false)) m r = some i) :
    inRowSpan (rrefAux invK fuel (r + 1) (j + 1)
      (matRowElim
        (matRowScale (matRowSwap A ⟨r, hr⟩ i) ⟨r, hr⟩ (invK (A i ⟨j, hj⟩)))
        ⟨r, hr⟩ ⟨j, hj⟩)) w ↔ inRowSpan A w :=
  let hpi := rrefAux_pivot_some hfp
  let hne : invK (A i ⟨j, hj⟩) ≠ 0 := ne_zero_invK invK hinv hpi.2
  (ih (r + 1) (j + 1) _ w).trans
    (inRowSpan_elim.trans ((inRowSpan_scale invK hinv hne).trans inRowSpan_swap))
-- Reference: MRR 1988, Pt. II Ch. 6 (each pass of Gaussian elimination is a
-- composition of row operations, so it preserves the row space); one unrolling
-- of the loop, by cases on the column, the row, and the pivot search.
/-- One unrolling of the elimination loop preserves the row span. -/
theorem inRowSpan_rrefAux_step (hinv : ∀ a : K, a ≠ 0 → invK a * a = 1) (fuel r j : ℕ)
    (ih : ∀ r j (A : FreeMatrix K m n) (w : FreeMod K n),
      inRowSpan (rrefAux invK fuel r j A) w ↔ inRowSpan A w)
    (A : FreeMatrix K m n) (w : FreeMod K n) :
    inRowSpan (if hj : j < n then
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
      else A) w ↔ inRowSpan A w := by
  rcases Nat.lt_or_ge j n with hj | hj
  · refine Eq.mpr (congrArg (fun M => inRowSpan M w ↔ inRowSpan A w) (dite_eq_left hj)) ?_
    rcases Nat.lt_or_ge r m with hr | hr
    · refine Eq.mpr (congrArg (fun M => inRowSpan M w ↔ inRowSpan A w)
        (dite_eq_left hr)) ?_
      cases hfp : findPivotRow
          (fun i => Nat.ble r i.val && (if A i ⟨j, hj⟩ ≠ 0 then true else false)) m r with
      | none => exact ih r (j + 1) A w
      | some i =>
          exact inRowSpan_rrefAux_step_pivot invK hinv fuel ih r j hj hr A w i hfp
    · refine Eq.mpr (congrArg (fun M => inRowSpan M w ↔ inRowSpan A w)
        (dite_eq_right (Nat.not_lt.mpr hr))) ?_
      exact ih r (j + 1) A w
  · refine Eq.mpr (congrArg (fun M => inRowSpan M w ↔ inRowSpan A w)
      (dite_eq_right (Nat.not_lt.mpr hj))) ?_
    exact ⟨fun h => h, fun h => h⟩
-- Reference: MRR 1988, Pt. II Ch. 6 (each pass of Gaussian elimination is a
-- composition of row operations, so it preserves the row space); proved by
-- induction on the fuel.
/-- Every state of the elimination loop has the same row span as the input. -/
theorem inRowSpan_rrefAux (hinv : ∀ a : K, a ≠ 0 → invK a * a = 1) :
    ∀ (fuel r j : ℕ) (A : FreeMatrix K m n) (w : FreeMod K n),
    inRowSpan (rrefAux invK fuel r j A) w ↔ inRowSpan A w :=
  fun fuel => Nat.rec (motive := fun fuel => ∀ r j (A : FreeMatrix K m n) (w : FreeMod K n),
      inRowSpan (rrefAux invK fuel r j A) w ↔ inRowSpan A w)
    (fun r j A w =>
      ⟨fun h => Eq.mp (congrArg (fun M => inRowSpan M w) (rrefAux_fuel_zero invK A r j)) h,
       fun h => Eq.mpr (congrArg (fun M => inRowSpan M w) (rrefAux_fuel_zero invK A r j)) h⟩)
    (fun fuel ih r j A w =>
      ⟨fun h => (inRowSpan_rrefAux_step invK hinv fuel r j ih A w).mp
          (Eq.mp (congrArg (fun M => inRowSpan M w) (rrefAux_fuel_succ invK A fuel r j)) h),
       fun h => Eq.mpr (congrArg (fun M => inRowSpan M w) (rrefAux_fuel_succ invK A fuel r j))
          ((inRowSpan_rrefAux_step invK hinv fuel r j ih A w).mpr h)⟩)
    fuel
-- Reference: MRR 1988, Pt. II Ch. 6; issue #108 (the RREF has the same row
-- space as the input matrix).
/-- The reduced row-echelon normal form has the same row span as the input. -/
theorem inRowSpan_rref (hinv : ∀ a : K, a ≠ 0 → invK a * a = 1) (A : FreeMatrix K m n)
    (w : FreeMod K n) : inRowSpan (rref invK A) w ↔ inRowSpan A w :=
  inRowSpan_rrefAux invK hinv (n+1) 0 0 A w
end BoringMath
