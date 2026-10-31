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

/-!
# Kernel and image of a `FreeModHom` as explicit computable data

Ticket P.2.2 (leaf of P.2, issue #109), built on the landed RREF
(`RowReduction.lean`, P.2.1). For a morphism `f : FreeModHom K m n` with
matrix `A = freeModHomMat f` (column `j` is `f` of the `j`-th standard basis
vector), let `R = rref invK A` be its reduced row-echelon normal form. Then,
as *data*:

* the **kernel basis** `kernelBasis R` — one vector `kernelVec R c` for each
  non-pivot column `c` of `R` (entry `1` at `c`, entry `-R a c` at the pivot
  column of row `a`);
* the **image basis** `imageBasis A R` — the pivot columns of the original
  matrix `A` (row reduction preserves column relations, so the pivot columns
  of `A` span the image);
* the **rank** `rankOf R` = number of pivot columns and the **nullity**
  `nullityOf R` = number of non-pivot columns, with the computation-level
  rank–nullity identity `rankOf R + nullityOf R = m`.

Correctness: `f x = 0` iff `x` is an explicit linear combination of
`kernelBasis R` (kernel membership iff annihilation), and `y` is in the image
of `f` iff `y` is an explicit linear combination of `imageBasis A R`.

All sums are `List.sum` over `List.finRange` — the mathlib `Finset`
big-operator API (`Finset.sum_insert`, `Finset.induction_on`,
`Finset.sum_ite_eq`, …) is `Classical.choice`-tainted at the pin v4.35.0-rc3
(probed with `#print axioms`), so the sum toolbox here is built directly on
`List` induction, which lints CLEAN.

## References
* R. Mines, F. Richman, W. Ruitenburg, *A Course in Constructive Algebra*,
  Springer Universitext, 1988, DOI 10.1007/978-1-4419-8640-5, Pt. II Ch. 6
  "Matrices and vector spaces" — kernel/image from the row-reduced form of
  a matrix over a discrete field (book and DOI verified via SpringerLink).
* F. Hörmann, *A note on formal periods*, arXiv:2106.03803, Def. 3.1 and
  Remark 3.3 (verified against the arXiv HTML): the finite-dimensional
  quotient computations `P^k(M) = P^∞(M)` for `k = dim H_B(M)` that this
  elimination layer supplies the decidability for.
-/

universe u

namespace BoringMath

variable {K : Type u} [Field K] {m n : ℕ}
variable (invK : K → K)

/-! ## Standard basis, matrix of a hom, matrix–vector product -/

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6 (the standard
-- basis of the coordinate module `Fin m → K`).
/-- The `j`-th standard basis vector of `FreeMod K m`: `1` at `j`, `0`
elsewhere. -/
def stdBasisVec (j : Fin m) : FreeMod K m := fun i => if i = j then 1 else 0

-- Reference: definitional peel of `stdBasisVec`.
/-- Pointwise unfolding of `stdBasisVec`. -/
theorem stdBasisVec_apply (j i : Fin m) :
    stdBasisVec j i = (if i = j then (1 : K) else (0 : K)) :=
  rfl

-- Reference: definitional peel of `stdBasisVec` at `i = j`.
/-- The standard basis vector has entry `1` at its own index. -/
theorem stdBasisVec_self (j : Fin m) : stdBasisVec j j = (1 : K) :=
  ite_eq_left rfl

-- Reference: definitional peel of `stdBasisVec` at `i ≠ j`.
/-- The standard basis vector has entry `0` off its own index. -/
theorem stdBasisVec_ne (j i : Fin m) (h : i ≠ j) : stdBasisVec j i = (0 : K) :=
  ite_eq_right h

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6 (the matrix of a
-- linear map in the standard basis: column `j` is the image of `e_j`).
/-- The matrix of a morphism `f : FreeModHom K m n` in the standard bases:
entry `(i, j)` is the `i`-th coordinate of `f (e_j)`. -/
def freeModHomMat (f : FreeModHom K m n) : FreeMatrix K n m :=
  fun i j => f.toFun (stdBasisVec j) i

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6 (matrix–vector
-- product `A x`, computed as a `List.sum` over `finRange m`; the `Finset`
-- sum API is choice-tainted at the pin, see the module doc).
/-- Matrix–vector product: `(A x) i = ∑_j A i j * x j`, as an explicit
`List.sum` over the columns. -/
def applyMat (A : FreeMatrix K n m) (x : FreeMod K m) : FreeMod K n :=
  fun i => ((List.finRange m).map (fun j => A i j * x j)).sum

-- Reference: definitional peel of `applyMat`.
/-- Pointwise unfolding of `applyMat`. -/
theorem applyMat_apply (A : FreeMatrix K n m) (x : FreeMod K m) (i : Fin n) :
    applyMat A x i = ((List.finRange m).map (fun j => A i j * x j)).sum :=
  rfl

-- Reference: definitional peel of `applyMat` (same anchor as
-- `applyMat_apply`); the pointwise sum form used by every row-operation peel.
/-- Matrix–vector product at a row is the explicit column sum of
row-times-vector entries. -/
theorem applyMat_eq_listSum (A : FreeMatrix K n m) (x : FreeMod K m) (a : Fin n) :
    applyMat A x a = ((List.finRange m).map (fun j => A a j * x j)).sum :=
  rfl

/-! ## Pivot columns and the kernel/image data of an RREF matrix -/

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6 (decidable zero-row
-- test, built directly on `List.all` — no choice-tainted instance).
/-- Boolean zero-row test for row `a` of `R`. -/
def rowIsZeroBool [DecidableEq K] (R : FreeMatrix K n m) (a : Fin n) : Bool :=
  ((List.finRange m).all (fun c => Decidable.decide (R a c = 0)))

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6; the landed pivot
-- search `findPivotRow` (RowReduction.lean).
/-- The pivot row of column `c` in an RREF matrix `R`: the first row whose
leading column is `c`, if any. -/
def pivotRowOfCol [DecidableEq K] (R : FreeMatrix K n m) (c : Fin m) : Option (Fin n) :=
  findPivotRow (fun a => Decidable.decide (matLeadingCol R a = c.val)) n 0

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6 (pivot columns).
/-- Boolean pivot-column test: column `c` is a pivot column of `R` iff some
row has leading column `c`. -/
def pivotColBool [DecidableEq K] (R : FreeMatrix K n m) (c : Fin m) : Bool :=
  (pivotRowOfCol R c).isSome

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6 (the solution-space
-- basis vector attached to a non-pivot column `c` of the RREF: entry `1` at
-- `c`, entry `-R a c` at the pivot column of each row `a`, else `0`).
/-- The kernel basis vector of the RREF matrix `R` attached to the column
`c`: entry `1` at `c`, entry `-R a c` at the pivot column of row `a`, and
`0` at every other non-pivot column. -/
def kernelVec [DecidableEq K] (R : FreeMatrix K n m) (c : Fin m) : FreeMod K m :=
  fun j => if j = c then 1 else
    match pivotRowOfCol R j with
    | some a => -(R a c)
    | none => 0

-- Reference: definitional peel of `kernelVec` at `j = c`.
/-- The kernel basis vector has entry `1` at its own column `c`. -/
theorem kernelVec_self [DecidableEq K] (R : FreeMatrix K n m) (c : Fin m) :
    kernelVec R c c = (1 : K) :=
  ite_eq_left rfl

-- Reference: definitional peel of `kernelVec` at a pivot column `j ≠ c`.
/-- At a pivot column `j ≠ c` owned by row `a`, the kernel basis vector has
entry `-R a c`. -/
theorem kernelVec_pivot [DecidableEq K] (R : FreeMatrix K n m) (c j : Fin m) (h : j ≠ c)
    (a : Fin n) (hp : pivotRowOfCol R j = some a) :
    kernelVec R c j = -(R a c) := by
  unfold kernelVec
  exact Eq.trans (ite_eq_right h)
    (Eq.trans (congrArg (fun p => match p with | some b => -(R b c) | none => (0 : K)) hp)
      rfl)

-- Reference: definitional peel of `kernelVec` at a non-pivot column `j ≠ c`.
/-- At a non-pivot column `j ≠ c`, the kernel basis vector has entry `0`. -/
theorem kernelVec_other [DecidableEq K] (R : FreeMatrix K n m) (c j : Fin m) (h : j ≠ c)
    (hp : pivotRowOfCol R j = none) :
    kernelVec R c j = (0 : K) := by
  unfold kernelVec
  exact Eq.trans (ite_eq_right h)
    (Eq.trans (congrArg (fun p => match p with | some b => -(R b c) | none => (0 : K)) hp)
      rfl)

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6 (pivot columns of
-- the RREF, in increasing order).
/-- The pivot columns of `R`, as an explicit list (a sublist of
`List.finRange m`, hence increasing). -/
def pivotCols [DecidableEq K] (R : FreeMatrix K n m) : List (Fin m) :=
  (List.finRange m).filter (pivotColBool R)

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6 (free columns of
-- the RREF: the non-pivot columns carry the kernel basis).
/-- The non-pivot columns of `R`, as an explicit list. -/
def nonPivotCols [DecidableEq K] (R : FreeMatrix K n m) : List (Fin m) :=
  (List.finRange m).filter (fun c => !(pivotColBool R c))

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6 (the kernel basis
-- is indexed by the non-pivot columns).
/-- The kernel basis of the RREF matrix `R`: `kernelVec R c` for each
non-pivot column `c`. -/
def kernelBasis [DecidableEq K] (R : FreeMatrix K n m) : List (FreeMod K m) :=
  (nonPivotCols R).map (kernelVec R)

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6 (the image is
-- spanned by the pivot columns of the *original* matrix; row reduction
-- preserves column relations).
/-- The image basis: the columns of the original matrix `A` at the pivot
columns of its RREF `R`. -/
def imageBasis [DecidableEq K] (A : FreeMatrix K n m) (R : FreeMatrix K n m) : List (FreeMod K n) :=
  (pivotCols R).map (fun c => fun i => A i c)

-- Reference: Hörmann, arXiv:2106.03803, Def. 3.1 / Remark 3.3 (the dimension
-- is computed data); Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6 (rank =
-- number of pivots).
/-- The rank of the matrix `R` in RREF: the number of pivot columns. -/
def rankOf [DecidableEq K] (R : FreeMatrix K n m) : ℕ := (pivotCols R).length

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6 (nullity = number of
-- free columns).
/-- The nullity: the number of kernel basis vectors, i.e. of non-pivot
columns of `R`. -/
def nullityOf [DecidableEq K] (R : FreeMatrix K n m) : ℕ := (kernelBasis R).length

/-! ## The `List.sum` toolbox

The mathlib `Finset` big-operator API (`Finset.sum_insert`,
`Finset.induction_on`, `Finset.sum_ite_eq`, `Finset.sum_congr`, …) is
`Classical.choice`-tainted at the pin v4.35.0-rc3 (probed with
`#print axioms`), so every sum lemma here is proved directly by structural
induction on `List`. -/

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6 (finite sums);
-- list form of `Finset.sum_add_distrib`, by structural induction.
/-- Sums distribute over pointwise addition. -/
theorem list_sum_map_add (l : List (Fin m)) (f g : Fin m → K) :
    (l.map (fun j => f j + g j)).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => exact (zero_add (0 : K)).symm
  | cons a l ih =>
      exact Eq.trans (congrArg (fun t => (f a + g a) + t) ih)
        (add_add_add_comm (f a) (g a) ((l.map f).sum) ((l.map g).sum))

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6; list form of
-- `Finset.sum_neg_distrib`, by structural induction.
/-- Sums distribute over pointwise negation. -/
theorem list_sum_map_neg (l : List (Fin m)) (f : Fin m → K) :
    (l.map (fun j => -(f j))).sum = -((l.map f).sum) := by
  induction l with
  | nil => exact neg_zero.symm
  | cons a l ih =>
      exact Eq.trans (congrArg (fun t => -(f a) + t) ih)
        ((neg_add (f a) ((l.map f).sum)).symm)

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6; list form of
-- `Finset.mul_sum`, by structural induction.
/-- A scalar factors out of a sum on the left. -/
theorem list_sum_map_mul_left (l : List (Fin m)) (c : K) (f : Fin m → K) :
    (l.map (fun j => c * f j)).sum = c * (l.map f).sum := by
  induction l with
  | nil => exact (mul_zero c).symm
  | cons a l ih =>
      exact Eq.trans (congrArg (fun t => c * f a + t) ih)
        ((mul_add c (f a) ((l.map f).sum)).symm)

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6; list form of
-- `Finset.sum_sub_distrib`, from the addition/negation peels.
/-- Sums distribute over pointwise subtraction. -/
theorem list_sum_map_sub (l : List (Fin m)) (f g : Fin m → K) :
    (l.map (fun j => f j - g j)).sum = (l.map f).sum - (l.map g).sum :=
  Eq.trans (congrArg (fun F => (l.map F).sum) (funext (fun j => sub_eq_add_neg (f j) (g j))))
    (Eq.trans (list_sum_map_add l f (fun j => -(g j)))
      (Eq.trans (congrArg (fun t => (l.map f).sum + t) (list_sum_map_neg l g))
        (sub_eq_add_neg ((l.map f).sum) ((l.map g).sum)).symm))

-- Reference: definitional peel of `List.sum` on `Pi` (pointwise addition);
-- `Pi.add_apply` and `Pi.zero_apply` are the pointwise laws.
/-- Evaluating a sum of functions at a point sums the evaluations. -/
theorem list_sum_map_apply {ι : Type*} (l : List ι) (F : ι → Fin n → K) (i : Fin n) :
    ((l.map F).sum : Fin n → K) i = (l.map (fun j => F j i)).sum := by
  induction l with
  | nil => exact Pi.zero_apply i
  | cons a l ih =>
      exact Eq.trans (Pi.add_apply (F a) ((l.map F).sum) i) (congrArg (fun t => F a i + t) ih)

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6; a congruence for
-- sums over a list, by structural induction (list form of
-- `Finset.sum_congr`).
/-- If `f` and `g` agree on every element of `l`, their sums over `l` agree. -/
theorem list_sum_map_congr_mem {ι : Type*} (l : List ι) {f g : ι → K}
    (h : ∀ j ∈ l, f j = g j) :
    (l.map f).sum = (l.map g).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      have ha : f a = g a := h a ((List.mem_cons).mpr (Or.inl rfl))
      have hl : ∀ j ∈ l, f j = g j := fun j hj => h j ((List.mem_cons).mpr (Or.inr hj))
      exact Eq.trans (congrArg (fun t => f a + t) (ih hl))
        (congrArg (fun t => t + (l.map g).sum) ha)

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6; by structural
-- induction.
/-- A sum of zeros over a list is zero. -/
theorem list_sum_eq_zero_of_forall_mem {ι : Type*} (l : List ι) {g : ι → K}
    (h : ∀ j ∈ l, g j = 0) :
    (l.map g).sum = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      have ha : g a = 0 := h a ((List.mem_cons).mpr (Or.inl rfl))
      have hl : ∀ j ∈ l, g j = 0 := fun j hj => h j ((List.mem_cons).mpr (Or.inr hj))
      exact Eq.trans (congrArg (fun t => t + (l.map g).sum) ha)
        (Eq.trans (congrArg (fun t => (0 : K) + t) (ih hl)) (add_zero (0 : K)))

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6; by structural
-- induction. The `ite` peels `ite_eq_left`/`ite_eq_right` on the `i = j` test.
/-- Off its index, an `ite`-sum vanishes. -/
theorem list_sum_ite_eq_zero_of_not_mem (l : List (Fin m)) :
    ∀ (f : Fin m → K) (i : Fin m), i ∉ l →
      (l.map (fun j => if i = j then f j else 0)).sum = 0 := by
  induction l with
  | nil => intro f i _; rfl
  | cons a l ih =>
      intro f i h
      have hl : i ∉ l := fun hi => h ((List.mem_cons).mpr (Or.inr hi))
      cases (inferInstance : Decidable (i = a)) with
      | isTrue hia => exact absurd ((List.mem_cons).mpr (Or.inl hia)) h
      | isFalse hia =>
          have hite : (if i = a then f a else (0 : K)) = (0 : K) := ite_eq_right hia
          have hS : (l.map (fun j => if i = j then f j else (0 : K))).sum = 0 := ih f i hl
          exact Eq.trans
            (congrArg (fun t => t + (l.map (fun j => if i = j then f j else (0 : K))).sum) hite)
            (Eq.trans (zero_add (l.map (fun j => if i = j then f j else (0 : K))).sum) hS)

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6; by structural
-- induction on the list (the nodup hypothesis makes the hit unique).
/-- On a nodup list, an `ite`-sum at a present index is the value there. -/
theorem list_sum_ite_eq_of_mem_nodup (l : List (Fin m)) :
    l.Nodup → ∀ (f : Fin m → K) (i : Fin m), i ∈ l →
      (l.map (fun j => if i = j then f j else 0)).sum = f i := by
  induction l with
  | nil => intro _ f i hi; exact absurd hi List.not_mem_nil
  | cons a l ih =>
      intro hnd f i hi
      rcases hnd with _ | ⟨hna, hndl⟩
      have hna' : a ∉ l := fun h => hna a h rfl
      rcases (List.mem_cons).mp hi with hia | hil
      · have hia' : a = i := hia.symm
        subst hia'
        have hzero : (l.map (fun j => if a = j then f j else (0 : K))).sum = 0 :=
          list_sum_ite_eq_zero_of_not_mem l f a hna'
        have hite : (if a = a then f a else (0 : K)) = f a := ite_eq_left rfl
        exact Eq.trans (congrArg (fun t => (if a = a then f a else (0 : K)) + t) hzero)
          (Eq.trans (congrArg (fun t => t + (0 : K)) hite) (add_zero (f a)))
      · have hia : i ≠ a := fun h => hna' (Eq.subst h hil)
        have hite : (if i = a then f a else (0 : K)) = (0 : K) := ite_eq_right hia
        have hS : (l.map (fun j => if i = j then f j else (0 : K))).sum = f i := ih hndl f i hil
        exact Eq.trans
          (congrArg (fun t => t + (l.map (fun j => if i = j then f j else (0 : K))).sum) hite)
          (Eq.trans (zero_add (l.map (fun j => if i = j then f j else (0 : K))).sum) hS)

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6; the masked summand
-- off the masked index equals the original summand (nodup makes the hit
-- unique).
/-- For `j ∈ l` with `a ∉ l`, the summand masked at `a` equals `g j`. -/
theorem eq_masked_of_mem_of_not_mem (l : List (Fin m)) (g : Fin m → K) {a j : Fin m}
    (hj : j ∈ l) (hna : a ∉ l) :
    g j = (if j = a then (0 : K) else g j) := by
  cases (inferInstance : Decidable (j = a)) with
  | isTrue hja => exact absurd (Eq.subst hja hj) hna
  | isFalse hja => exact (ite_eq_right hja).symm

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6; by structural
-- induction on the list (the nodup hypothesis makes the hit unique).
-- Splitting a sum at a present index of a nodup list.
/-- A sum over a nodup list splits off the summand at a present index. -/
theorem list_sum_split (l : List (Fin m)) :
    l.Nodup → ∀ (g : Fin m → K) (i : Fin m), i ∈ l →
      (l.map g).sum = g i + (l.map (fun j => if j = i then 0 else g j)).sum := by
  induction l with
  | nil => intro _ g i hi; exact absurd hi List.not_mem_nil
  | cons a l ih =>
      intro hnd g i hi
      rcases hnd with _ | ⟨hna, hndl⟩
      have hna' : a ∉ l := fun h => hna a h rfl
      rcases (List.mem_cons).mp hi with hia | hil
      · have hia' : a = i := hia.symm
        subst hia'
        have hcong : (l.map g).sum = (l.map (fun j => if j = a then (0 : K) else g j)).sum :=
          list_sum_map_congr_mem l (fun j hj => eq_masked_of_mem_of_not_mem l g hj hna')
        have hite : (if a = a then (0 : K) else g a) = (0 : K) := ite_eq_left rfl
        have hz : (0 : K) + (l.map (fun j => if j = a then (0 : K) else g j)).sum
            = (l.map (fun j => if j = a then (0 : K) else g j)).sum := zero_add _
        exact Eq.trans (congrArg (fun t => g a + t) hcong)
          ((Eq.trans
            (congrArg (fun t => g a + (t + (l.map (fun j => if j = a then (0 : K) else g j)).sum))
              hite)
            (congrArg (fun t => g a + t) hz)).symm)
      · have hia : i ≠ a := fun h => hna' (Eq.subst h hil)
        have hia' : a ≠ i := fun h => hia h.symm
        have hsplit : (l.map g).sum = g i + (l.map (fun j => if j = i then (0 : K) else g j)).sum :=
          ih hndl g i hil
        have hite : (if a = i then (0 : K) else g a) = g a := ite_eq_right hia'
        exact Eq.trans (congrArg (fun t => g a + t) hsplit)
          (Eq.trans (add_left_comm (g a) (g i)
              ((l.map (fun j => if j = i then (0 : K) else g j)).sum))
            (congrArg (fun t => g i + (t + (l.map (fun j => if j = i then (0 : K) else g j)).sum))
              hite).symm)

/-! ## The matrix of a hom and the matrix–vector product -/

-- Reference: Axler, Ch. 1 (a linear map kills zero); from `map_smul'` at
-- scalar `0`.
/-- A morphism of free modules sends zero to zero. -/
theorem freeModHom_map_zero (f : FreeModHom K m n) : f.toFun 0 = 0 := by
  have h : f.toFun (0 + 0) = f.toFun 0 + f.toFun 0 := f.map_add' (0 : FreeMod K m) 0
  have hz : (0 : FreeMod K m) + 0 = 0 := zero_add 0
  have h1 : f.toFun (0 + 0) = f.toFun 0 := congrArg f.toFun hz
  have h' : f.toFun 0 = f.toFun 0 + f.toFun 0 := Eq.trans h1.symm h
  have haz : f.toFun 0 + 0 = f.toFun 0 := add_zero (f.toFun 0)
  exact add_left_cancel (Eq.trans h'.symm haz.symm)

-- Reference: Axler, Ch. 1 (linear maps commute with finite sums); by
-- structural induction on the index list.
/-- A morphism of free modules commutes with a list sum of vectors. -/
theorem freeModHom_map_listSum (f : FreeModHom K m n) (l : List (Fin m))
    (g : Fin m → FreeMod K m) :
    f.toFun ((l.map g).sum) = (l.map (fun j => f.toFun (g j))).sum := by
  induction l with
  | nil => exact freeModHom_map_zero f
  | cons a l ih =>
      exact Eq.trans (f.map_add' (g a) ((l.map g).sum)) (congrArg (fun t => f.toFun (g a) + t) ih)

-- Reference: definitional peel of the standard-basis component at `i = j`
-- (same anchor as `eq_listSum_stdBasisVec`).
/-- The `i`-th component of `x j • stdBasisVec j` is `x j` when `i = j`. -/
theorem smul_stdBasisVec_apply_eq (x : FreeMod K m) (j i : Fin m) (hij : i = j) :
    (x j • stdBasisVec j) i = x j := by
  have hij' : j = i := hij.symm
  subst hij'
  have hsmul : (x j • stdBasisVec j) j = x j • (stdBasisVec j j : K) :=
    Pi.smul_apply (x j) (stdBasisVec j) j
  have hself : stdBasisVec j j = (1 : K) := stdBasisVec_self j
  have h1 : x j • (stdBasisVec j j : K) = x j • (1 : K) := congrArg (fun t => x j • t) hself
  have h2 : x j • (1 : K) = x j * (1 : K) := smul_eq_mul (x j) (1 : K)
  have h3 : x j * (1 : K) = x j := mul_one (x j)
  exact Eq.trans hsmul (Eq.trans h1 (Eq.trans h2 h3))
-- Reference: definitional peel of the standard-basis component at `i ≠ j`
-- (same anchor as `eq_listSum_stdBasisVec`).
/-- The `i`-th component of `x j • stdBasisVec j` is `0` when `i ≠ j`. -/
theorem smul_stdBasisVec_apply_ne (x : FreeMod K m) (j i : Fin m) (hij : i ≠ j) :
    (x j • stdBasisVec j) i = (0 : K) := by
  have hsmul : (x j • stdBasisVec j) i = x j • (stdBasisVec j i : K) :=
    Pi.smul_apply (x j) (stdBasisVec j) i
  have hne : stdBasisVec j i = (0 : K) := stdBasisVec_ne j i hij
  have h1 : x j • (stdBasisVec j i : K) = x j • (0 : K) := congrArg (fun t => x j • t) hne
  have h2 : x j • (0 : K) = x j * (0 : K) := smul_eq_mul (x j) (0 : K)
  have h3 : x j * (0 : K) = (0 : K) := mul_zero (x j)
  exact Eq.trans hsmul (Eq.trans h1 (Eq.trans h2 h3))
-- Reference: definitional peel of the standard-basis component (same anchor
-- as `eq_listSum_stdBasisVec`).
/-- The `i`-th component of `x j • stdBasisVec j` is the `ite` at `i = j`. -/
theorem smul_stdBasisVec_apply (x : FreeMod K m) (j i : Fin m) :
    (x j • stdBasisVec j) i = (if i = j then x j else 0) := by
  cases (inferInstance : Decidable (i = j)) with
  | isTrue hij => exact Eq.trans (smul_stdBasisVec_apply_eq x j i hij) (ite_eq_left hij).symm
  | isFalse hij => exact Eq.trans (smul_stdBasisVec_apply_ne x j i hij) (ite_eq_right hij).symm

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6 (every vector is
-- the sum of its standard-basis components); proved pointwise via the
-- `ite`-sum peels on `List.finRange m` (nodup).
/-- Every vector of `FreeMod K m` is the explicit sum of its standard-basis
components. -/
theorem eq_listSum_stdBasisVec (x : FreeMod K m) :
    x = ((List.finRange m).map (fun j => x j • stdBasisVec j)).sum := by
  have h : (((List.finRange m).map (fun j => x j • stdBasisVec j)).sum : FreeMod K m) = x := by
    funext i
    exact Eq.trans (list_sum_map_apply (List.finRange m) (fun j => x j • stdBasisVec j) i)
      (Eq.trans (congrArg (fun F => ((List.finRange m).map F).sum)
          (funext (fun j => smul_stdBasisVec_apply x j i)))
        (list_sum_ite_eq_of_mem_nodup (List.finRange m) (List.nodup_finRange m) x i
          (List.mem_finRange i)))
  exact h.symm

-- Reference: Axler, Ch. 1 (linear maps commute with scalars); Mines–Richman–
-- Ruitenburg 1988, Pt. II Ch. 6 (matrix entries); same anchor as
-- `freeModHom_apply_eq_applyMat`.
/-- Pointwise: `f (x j • e_j)` at `i` is the matrix entry `(i, j)` times `x j`. -/
theorem freeModHom_smul_stdBasisVec_apply (f : FreeModHom K m n) (x : FreeMod K m)
    (j : Fin m) (i : Fin n) :
    f.toFun (x j • stdBasisVec j) i = freeModHomMat f i j * x j :=
  Eq.trans (congrFun (f.map_smul' (x j) (stdBasisVec j)) i)
    (Eq.trans (Pi.smul_apply (x j) (f.toFun (stdBasisVec j)) i)
      (mul_comm (x j) (f.toFun (stdBasisVec j) i)))

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6 (a linear map is
-- its matrix: `f x = A x` with `A` the matrix of `f`); assembled from
-- `eq_listSum_stdBasisVec`, `freeModHom_listSum` and `map_smul'`.
/-- The morphism `f` equals matrix–vector product with its matrix. -/
theorem freeModHom_apply_eq_applyMat (f : FreeModHom K m n) (x : FreeMod K m) :
    f.toFun x = applyMat (freeModHomMat f) x := by
  funext i
  exact Eq.trans (congrFun (congrArg f.toFun (eq_listSum_stdBasisVec x)) i)
    (Eq.trans
      (congrFun (freeModHom_map_listSum f (List.finRange m) (fun j => x j • stdBasisVec j)) i)
      (Eq.trans (list_sum_map_apply (List.finRange m) (fun j => f.toFun (x j • stdBasisVec j)) i)
        (list_sum_map_congr_mem (List.finRange m)
          (fun j _ => freeModHom_smul_stdBasisVec_apply f x j i))))

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

/-! ## The elimination loop preserves the annihilation predicate -/

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6 (one pivot step —
-- swap, scale, eliminate — preserves the solution set); assembled from the
-- three row-operation preservation lemmas and `rrefAux_pivot_some`; same
-- anchor as `rrefAux_applyMat_eq_zero_iff`.
/-- One pivot step of the elimination loop preserves `applyMat _ x = 0`. -/
theorem rrefAux_step_pivot [DecidableEq K]
    (hinv : ∀ a : K, a ≠ 0 → invK a * a = 1) (fuel : ℕ)
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
  | some i => exact rrefAux_step_pivot invK hinv fuel ih r j hr hj i hfp

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
