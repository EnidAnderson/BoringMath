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

/-! ## Pivot columns and the kernel/image data of an RREF matrix -/

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6 (decidable zero-row
-- test, built directly on `List.all`/`decide` — no choice-tainted instance).
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
  -- unfold kernelVec: explicit constant; rw [ite_eq_right h, hp]: unique occurrences.
  unfold kernelVec
  rw [ite_eq_right h, hp]

-- Reference: definitional peel of `kernelVec` at a non-pivot column `j ≠ c`.
/-- At a non-pivot column `j ≠ c`, the kernel basis vector has entry `0`. -/
theorem kernelVec_other [DecidableEq K] (R : FreeMatrix K n m) (c j : Fin m) (h : j ≠ c)
    (hp : pivotRowOfCol R j = none) :
    kernelVec R c j = (0 : K) := by
  -- unfold kernelVec: explicit constant; rw [ite_eq_right h, hp]: unique occurrences.
  unfold kernelVec
  rw [ite_eq_right h, hp]

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
  | nil => change (0 : K) = 0 + 0; exact (zero_add (0 : K)).symm
  | cons a l ih =>
      change (f a + g a) + (l.map (fun j => f j + g j)).sum
          = (f a + (l.map f).sum) + (g a + (l.map g).sum)
      rw [ih]
      exact add_add_add_comm (f a) (g a) (l.map f).sum (l.map g).sum

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6; list form of
-- `Finset.sum_neg_distrib`, by structural induction.
/-- Sums distribute over pointwise negation. -/
theorem list_sum_map_neg (l : List (Fin m)) (f : Fin m → K) :
    (l.map (fun j => -(f j))).sum = -((l.map f).sum) := by
  induction l with
  | nil => change (0 : K) = -0; exact neg_zero.symm
  | cons a l ih =>
      change -(f a) + (l.map (fun j => -(f j))).sum = -(f a + (l.map f).sum)
      rw [ih]
      exact (neg_add (f a) ((l.map f).sum)).symm

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6; list form of
-- `Finset.mul_sum`, by structural induction.
/-- A scalar factors out of a sum on the left. -/
theorem list_sum_map_mul_left (l : List (Fin m)) (c : K) (f : Fin m → K) :
    (l.map (fun j => c * f j)).sum = c * (l.map f).sum := by
  induction l with
  | nil => change (0 : K) = c * 0; exact (mul_zero c).symm
  | cons a l ih =>
      change c * f a + (l.map (fun j => c * f j)).sum = c * (f a + (l.map f).sum)
      rw [ih]
      exact (mul_add c (f a) ((l.map f).sum)).symm

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6; list form of
-- `Finset.sum_sub_distrib`, from the addition/negation peels.
/-- Sums distribute over pointwise subtraction. -/
theorem list_sum_map_sub (l : List (Fin m)) (f g : Fin m → K) :
    (l.map (fun j => f j - g j)).sum = (l.map f).sum - (l.map g).sum := by
  have h : (fun j => f j - g j) = (fun j => f j + -(g j)) :=
    funext (fun j => sub_eq_add_neg (f j) (g j))
  -- rw [h]: unique occurrence of the function in the map on the left.
  rw [h, list_sum_map_add, list_sum_map_neg, sub_eq_add_neg]

-- Reference: definitional peel of `List.sum` on `Pi` (pointwise addition);
-- `Pi.add_apply` and `Pi.zero_apply` are the pointwise laws.
/-- Evaluating a sum of functions at a point sums the evaluations. -/
theorem list_sum_map_apply {ι : Type*} (l : List ι) (F : ι → Fin n → K) (i : Fin n) :
    ((l.map F).sum : Fin n → K) i = (l.map (fun j => F j i)).sum := by
  induction l with
  | nil => change (0 : Fin n → K) i = (0 : K); exact Pi.zero_apply i
  | cons a l ih =>
      change (F a + (l.map F).sum) i = F a i + (l.map (fun j => F j i)).sum
      rw [Pi.add_apply, ih]

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
      have ha := h a ((List.mem_cons).mpr (Or.inl rfl))
      have hl : ∀ j ∈ l, f j = g j := fun j hj => h j ((List.mem_cons).mpr (Or.inr hj))
      change f a + (l.map f).sum = g a + (l.map g).sum
      rw [ha, ih hl]

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6; by structural
-- induction.
/-- A sum of zeros over a list is zero. -/
theorem list_sum_eq_zero_of_forall_mem {ι : Type*} (l : List ι) {g : ι → K}
    (h : ∀ j ∈ l, g j = 0) :
    (l.map g).sum = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      have ha := h a ((List.mem_cons).mpr (Or.inl rfl))
      have hl : ∀ j ∈ l, g j = 0 := fun j hj => h j ((List.mem_cons).mpr (Or.inr hj))
      change g a + (l.map g).sum = 0
      rw [ha, ih hl, add_zero]

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6; by structural
-- induction. The `ite` peels `ite_eq_left`/`ite_eq_right` decide `i = j`.
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
          change (if i = a then f a else 0) + (l.map (fun j => if i = j then f j else 0)).sum = 0
          rw [ite_eq_right hia, ih f i hl, zero_add]

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
      · rw [hia]
        change (if a = a then f a else 0) + (l.map (fun j => if a = j then f j else 0)).sum = f a
        rw [ite_eq_left rfl, list_sum_ite_eq_zero_of_not_mem l f a hna', add_zero]
      · have hia : i ≠ a := fun h => hna' (Eq.subst h hil)
        change (if i = a then f a else 0) + (l.map (fun j => if i = j then f j else 0)).sum = f i
        rw [ite_eq_right hia, zero_add, ih hndl f i hil]

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6; by structural
-- induction. Splitting a sum at a present index of a nodup list.
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
      · rw [hia]
        change g a + (l.map g).sum
            = g a + ((if a = a then 0 else g a) + (l.map (fun j => if j = a then 0 else g j)).sum)
        rw [ite_eq_left rfl, zero_add]
        -- `(l.map g).sum = (l.map (fun j => if j = a then 0 else g j)).sum`: every `j ∈ l`
        -- satisfies `j ≠ a` (as `a ∉ l`), so the masked summand equals `g j`.
        have hcong : (l.map g).sum = (l.map (fun j => if j = a then 0 else g j)).sum :=
          list_sum_map_congr_mem l (fun j hj => by
            cases (inferInstance : Decidable (j = a)) with
            | isTrue hja => exact absurd (Eq.subst hja hj) hna'
            | isFalse hja => exact (ite_eq_right hja).symm)
        rw [hcong]
      · have hia : i ≠ a := fun h => hna' (Eq.subst h hil)
        have hia' : a ≠ i := fun h => hia h.symm
        change g a + (l.map g).sum
            = g i + ((if a = i then 0 else g a) + (l.map (fun j => if j = i then 0 else g j)).sum)
        rw [ite_eq_right hia', ih hndl g i hil]
        exact add_left_comm (g a) (g i) ((l.map (fun j => if j = i then 0 else g j)).sum)

/-! ## The matrix of a hom and the matrix–vector product -/

-- Reference: Axler, Ch. 1 (a linear map kills zero); from `map_smul'` at
-- scalar `0`.
/-- A morphism of free modules sends zero to zero. -/
theorem freeModHom_map_zero (f : FreeModHom K m n) : f.toFun 0 = 0 := by
  have h := f.map_add' (0 : FreeMod K m) 0
  -- rw [zero_add] at h: `0 + 0 = 0`; h : f 0 = f 0 + f 0.
  rw [zero_add] at h
  exact add_left_cancel (by
    rw [add_zero]
    exact h.symm)

-- Reference: Axler, Ch. 1 (linear maps commute with finite sums); by
-- structural induction on the index list.
/-- A morphism of free modules commutes with a list sum of vectors. -/
theorem freeModHom_map_listSum (f : FreeModHom K m n) (l : List (Fin m))
    (g : Fin m → FreeMod K m) :
    f.toFun ((l.map g).sum) = (l.map (fun j => f.toFun (g j))).sum := by
  induction l with
  | nil => exact freeModHom_map_zero f
  | cons a l ih =>
      change f.toFun (g a + (l.map g).sum) = f.toFun (g a) + (l.map (fun j => f.toFun (g j))).sum
      rw [f.map_add', ih]

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6 (every vector is
-- the sum of its standard-basis components); proved pointwise via the
-- `ite`-sum peels on `List.finRange m` (nodup).
/-- Every vector of `FreeMod K m` is the explicit sum of its standard-basis
components. -/
theorem eq_listSum_stdBasisVec (x : FreeMod K m) :
    x = ((List.finRange m).map (fun j => x j • stdBasisVec j)).sum := by
  have h : (((List.finRange m).map (fun j => x j • stdBasisVec j)).sum : FreeMod K m) = x := by
    funext i
    rw [list_sum_map_apply]
    have hcong : (fun j => (x j • stdBasisVec j) i) = (fun j => if i = j then x j else 0) := by
      funext j
      rw [Pi.smul_apply, stdBasisVec_apply]
      cases (inferInstance : Decidable (i = j)) with
      | isTrue hij => rw [ite_eq_left hij, ite_eq_left hij, smul_eq_mul, mul_one]
      | isFalse hij => rw [ite_eq_right hij, ite_eq_right hij, smul_eq_mul, mul_zero]
    rw [hcong]
    exact list_sum_ite_eq_of_mem_nodup (List.finRange m) (List.nodup_finRange m) x i
      (List.mem_finRange i)
  exact h.symm

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6 (a linear map is
-- its matrix: `f x = A x` with `A` the matrix of `f`); assembled from
-- `eq_listSum_stdBasisVec`, `freeModHom_listSum` and `map_smul'`.
/-- The morphism `f` equals matrix–vector product with its matrix. -/
theorem freeModHom_apply_eq_applyMat (f : FreeModHom K m n) (x : FreeMod K m) :
    f.toFun x = applyMat (freeModHomMat f) x := by
  funext i
  -- rw [congrFun (congrArg f.toFun (eq_listSum_stdBasisVec x)) i]: `f x i` is
  -- `f` of the standard-basis sum, at `i`; unique occurrence.
  rw [congrFun (congrArg f.toFun (eq_listSum_stdBasisVec x)) i,
    freeModHom_map_listSum f (List.finRange m) (fun j => x j • stdBasisVec j),
    list_sum_map_apply, applyMat_apply]
  apply list_sum_map_congr_mem
  intro j _
  rw [f.map_smul', Pi.smul_apply]
  change x j * f.toFun (stdBasisVec j) i = f.toFun (stdBasisVec j) i * x j
  exact mul_comm _ _

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
      rw [har, ite_eq_left rfl, applyMat_apply, applyMat_apply]
      exact list_sum_map_congr_mem _ (fun j _ => by
        rw [matRowSwap_left A r i j, mul_comm])
  | isFalse har =>
      rw [ite_eq_right har]
      cases (inferInstance : Decidable (a = i)) with
      | isTrue hai =>
          rw [hai, ite_eq_left rfl, applyMat_apply, applyMat_apply]
          have hne : i ≠ r := fun h => har (hai.trans h)
          exact list_sum_map_congr_mem _ (fun j _ => by
            rw [matRowSwap_right A r i hne j, mul_comm])
      | isFalse hai =>
          rw [ite_eq_right hai, applyMat_apply, applyMat_apply]
          exact list_sum_map_congr_mem _ (fun j _ => by rw [matRowSwap_other A r i a har hai j])

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6 (row swaps are
-- invertible, so the solution set is unchanged).
/-- A row swap preserves the predicate `applyMat _ x = 0`. -/
theorem applyMat_rowSwap_eq_zero_iff (A : FreeMatrix K n m) (r i : Fin n) (x : FreeMod K m) :
    applyMat (matRowSwap A r i) x = 0 ↔ applyMat A x = 0 := by
  refine ⟨?_, ?_⟩
  · intro h
    have h0 : ∀ b, applyMat (matRowSwap A r i) x b = 0 := fun b => congrFun h b
    funext a
    rw [Pi.zero_apply]
    cases (inferInstance : Decidable (a = r)) with
    | isTrue har =>
        rw [har]
        have hi := h0 i
        rw [applyMat_rowSwap_apply A r i x i] at hi
        cases (inferInstance : Decidable (i = r)) with
        | isTrue hir => rw [hir, ite_eq_left rfl] at hi; exact hi
        | isFalse hir => rw [ite_eq_right hir, ite_eq_left rfl] at hi; exact hi
    | isFalse har =>
        cases (inferInstance : Decidable (a = i)) with
        | isTrue hai =>
            rw [hai]
            have hr := h0 r
            rw [applyMat_rowSwap_apply A r i x r, ite_eq_left rfl] at hr
            exact hr
        | isFalse hai =>
            have ha := h0 a
            rw [applyMat_rowSwap_apply A r i x a, ite_eq_right har, ite_eq_right hai] at ha
            exact ha
  · intro h
    have k0 : ∀ b, applyMat A x b = 0 := fun b => congrFun h b
    funext b
    rw [Pi.zero_apply, applyMat_rowSwap_apply A r i x b]
    cases (inferInstance : Decidable (b = r)) with
    | isTrue hbr => rw [hbr, ite_eq_left rfl]; exact k0 i
    | isFalse hbr =>
        rw [ite_eq_right hbr]
        cases (inferInstance : Decidable (b = i)) with
        | isTrue hbi => rw [hbi, ite_eq_left rfl]; exact k0 r
        | isFalse hbi => rw [ite_eq_right hbi]; exact k0 b

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6 (row scaling);
-- pointwise peel of `matRowScale`.
/-- Matrix–vector product after a row scaling. -/
theorem applyMat_rowScale_apply (A : FreeMatrix K n m) (r : Fin n) (s : K) (x : FreeMod K m)
    (a : Fin n) :
    applyMat (matRowScale A r s) x a =
      (if a = r then s * applyMat A x a else applyMat A x a) := by
  cases (inferInstance : Decidable (a = r)) with
  | isTrue har =>
      rw [har, ite_eq_left rfl, applyMat_apply, applyMat_apply, ← list_sum_map_mul_left]
      exact list_sum_map_congr_mem _ (fun j _ => by rw [matRowScale_self, mul_assoc])
  | isFalse har =>
      rw [ite_eq_right har, applyMat_apply, applyMat_apply]
      exact list_sum_map_congr_mem _ (fun j _ => by rw [matRowScale_other A r a har s j])

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6 (scaling by a
-- nonzero scalar is invertible).
/-- Scaling a row by a nonzero scalar preserves `applyMat _ x = 0`. -/
theorem applyMat_rowScale_eq_zero_iff (A : FreeMatrix K n m) (r : Fin n) (s : K)
    (x : FreeMod K m) (hs : s ≠ 0) :
    applyMat (matRowScale A r s) x = 0 ↔ applyMat A x = 0 := by
  refine ⟨?_, ?_⟩
  · intro h
    have h0 : ∀ b, applyMat (matRowScale A r s) x b = 0 := fun b => congrFun h b
    funext a
    rw [Pi.zero_apply]
    cases (inferInstance : Decidable (a = r)) with
    | isTrue har =>
        rw [har]
        have ha := h0 r
        rw [applyMat_rowScale_apply A r s x r, ite_eq_left rfl] at ha
        rcases mul_eq_zero.mp ha with hs' | hx
        · exact absurd hs' hs
        · exact hx
    | isFalse har =>
        have ha := h0 a
        rw [applyMat_rowScale_apply A r s x a, ite_eq_right har] at ha
        exact ha
  · intro h
    have k0 : ∀ b, applyMat A x b = 0 := fun b => congrFun h b
    funext b
    rw [Pi.zero_apply, applyMat_rowScale_apply A r s x b]
    cases (inferInstance : Decidable (b = r)) with
    | isTrue hbr => rw [hbr, ite_eq_left rfl, k0 r, mul_zero]
    | isFalse hbr => rw [ite_eq_right hbr]; exact k0 b

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6 (the elimination
-- step fixes the pivot row); pointwise peel of `matRowElim`.
/-- Matrix–vector product after an elimination step at the pivot row. -/
theorem applyMat_rowElim_self (A : FreeMatrix K n m) (r : Fin n) (j : Fin m) (x : FreeMod K m) :
    applyMat (matRowElim A r j) x r = applyMat A x r := by
  rw [applyMat_apply, applyMat_apply]
  exact list_sum_map_congr_mem _ (fun c _ => by rw [matRowElim_self])

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6 (the elimination
-- step subtracts a multiple of the pivot row off row `a`).
/-- Matrix–vector product after an elimination step at an off-pivot row. -/
theorem applyMat_rowElim_other (A : FreeMatrix K n m) (r a : Fin n) (h : a ≠ r) (j : Fin m)
    (x : FreeMod K m) :
    applyMat (matRowElim A r j) x a = applyMat A x a - A a j * applyMat A x r := by
  rw [applyMat_apply, applyMat_apply, applyMat_apply, ← list_sum_map_mul_left,
    ← list_sum_map_sub]
  exact list_sum_map_congr_mem _ (fun c _ => by
    rw [matRowElim_other A r a h j c, sub_mul, mul_assoc])

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6 (the elimination
-- step is invertible: add the pivot row back).
/-- An elimination step preserves `applyMat _ x = 0`. -/
theorem applyMat_rowElim_eq_zero_iff (A : FreeMatrix K n m) (r : Fin n) (j : Fin m)
    (x : FreeMod K m) :
    applyMat (matRowElim A r j) x = 0 ↔ applyMat A x = 0 := by
  refine ⟨?_, ?_⟩
  · intro h
    have h0 : ∀ b, applyMat (matRowElim A r j) x b = 0 := fun b => congrFun h b
    have hr0 : applyMat A x r = 0 := by
      have := h0 r
      rw [applyMat_rowElim_self A r j x] at this
      exact this
    funext a
    rw [Pi.zero_apply]
    cases (inferInstance : Decidable (a = r)) with
    | isTrue har => rw [har]; exact hr0
    | isFalse har =>
        have ha := h0 a
        rw [applyMat_rowElim_other A r a har j x, hr0, mul_zero, sub_zero] at ha
        exact ha
  · intro h
    have k0 : ∀ b, applyMat A x b = 0 := fun b => congrFun h b
    funext b
    rw [Pi.zero_apply]
    cases (inferInstance : Decidable (b = r)) with
    | isTrue hbr => rw [hbr, applyMat_rowElim_self, k0 r]
    | isFalse hbr =>
        rw [applyMat_rowElim_other A r b hbr j x, k0 b, k0 r, mul_zero, sub_self]

-- Reference: RowReduction.lean (the `invK` contract `hinv`); a left inverse
-- of a nonzero element is nonzero.
/-- The explicit inverse of a nonzero element is nonzero. -/
theorem invK_ne_zero (hinv : ∀ a : K, a ≠ 0 → invK a * a = 1) {a : K} (h : a ≠ 0) :
    invK a ≠ 0 := by
  intro h0
  have hh := hinv a h
  rw [h0, zero_mul] at hh
  exact absurd hh.symm one_ne_zero

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6 (the elimination
-- loop preserves the solution set); induction on the fuel, using the three
-- row-operation preservation lemmas above and `rrefAux_pivot_some`.
/-- The elimination loop preserves `applyMat _ x = 0`. -/
theorem rrefAux_applyMat_eq_zero_iff [DecidableEq K]
    (hinv : ∀ a : K, a ≠ 0 → invK a * a = 1) (fuel : ℕ) :
    ∀ (r j : ℕ) (A : FreeMatrix K n m) (x : FreeMod K m),
      applyMat (rrefAux invK fuel r j A) x = 0 ↔ applyMat A x = 0 := by
  induction fuel with
  | zero => intro r j A x; rw [rrefAux_fuel_zero invK A r j]
  | succ fuel ih =>
      intro r j A x
      rw [rrefAux_fuel_succ invK A fuel r j]
      rcases Nat.lt_or_ge j m with hj | hj
      · rw [dite_eq_left hj]
        rcases Nat.lt_or_ge r n with hr | hr
        · rw [dite_eq_left hr]
          cases hfp : findPivotRow
              (fun i => Nat.ble r i.val && (if A i ⟨j, hj⟩ ≠ 0 then true else false)) n r with
          | none => exact ih r (j+1) A x
          | some i =>
              have hpi := rrefAux_pivot_some hfp
              have hswap := applyMat_rowSwap_eq_zero_iff A ⟨r, hr⟩ i x
              have hsinv : invK (A i ⟨j, hj⟩) ≠ 0 := invK_ne_zero invK hinv hpi.2
              have hscale := applyMat_rowScale_eq_zero_iff
                (matRowSwap A ⟨r, hr⟩ i) ⟨r, hr⟩ (invK (A i ⟨j, hj⟩)) x hsinv
              have helim := applyMat_rowElim_eq_zero_iff
                (matRowScale (matRowSwap A ⟨r, hr⟩ i) ⟨r, hr⟩ (invK (A i ⟨j, hj⟩)))
                ⟨r, hr⟩ ⟨j, hj⟩ x
              exact (ih (r+1) (j+1)
                (matRowElim
                  (matRowScale (matRowSwap A ⟨r, hr⟩ i) ⟨r, hr⟩ (invK (A i ⟨j, hj⟩)))
                  ⟨r, hr⟩ ⟨j, hj⟩) x).trans ((helim.trans hscale).trans hswap)
        · rw [dite_eq_right (not_lt.mpr hr)]
          exact ih r (j+1) A x
      · rw [dite_eq_right (not_lt.mpr hj)]

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
    f.toFun x = 0 ↔ applyMat (rref invK (freeModHomMat f)) x = 0 := by
  have h1 := freeModHom_apply_eq_applyMat f x
  have h2 := rref_applyMat_eq_zero_iff invK hinv (freeModHomMat f) x
  refine ⟨?_, ?_⟩
  · intro h
    rw [h1] at h
    exact h2.mpr h
  · intro h
    rw [h1]
    exact h2.mp h

/-! ## Axiom lint -/

#lint_axioms BoringMath.stdBasisVec
#lint_axioms BoringMath.stdBasisVec_apply
#lint_axioms BoringMath.stdBasisVec_self
#lint_axioms BoringMath.stdBasisVec_ne
#lint_axioms BoringMath.freeModHomMat
#lint_axioms BoringMath.applyMat
#lint_axioms BoringMath.applyMat_apply
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
#lint_axioms BoringMath.list_sum_split
#lint_axioms BoringMath.freeModHom_map_zero
#lint_axioms BoringMath.freeModHom_map_listSum
#lint_axioms BoringMath.eq_listSum_stdBasisVec
#lint_axioms BoringMath.freeModHom_apply_eq_applyMat
#lint_axioms BoringMath.applyMat_rowSwap_apply
#lint_axioms BoringMath.applyMat_rowSwap_eq_zero_iff
#lint_axioms BoringMath.applyMat_rowScale_apply
#lint_axioms BoringMath.applyMat_rowScale_eq_zero_iff
#lint_axioms BoringMath.applyMat_rowElim_self
#lint_axioms BoringMath.applyMat_rowElim_other
#lint_axioms BoringMath.applyMat_rowElim_eq_zero_iff
#lint_axioms BoringMath.invK_ne_zero
#lint_axioms BoringMath.rrefAux_applyMat_eq_zero_iff
#lint_axioms BoringMath.rref_applyMat_eq_zero_iff
#lint_axioms BoringMath.freeModHom_apply_eq_zero_iff

end BoringMath
