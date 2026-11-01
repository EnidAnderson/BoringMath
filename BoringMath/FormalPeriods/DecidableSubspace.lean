/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Init
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import BoringMath.FormalPeriods.FreeMod
import BoringMath.FormalPeriods.RowReduction
import BoringMath.FormalPeriods.AxiomLint
/-!
# Decidable subspace membership, equality, and containment (P.2.3)
Ticket P.2.3 (leaf of P.2, issue #110), built on the landed P.2.1 RREF
(`BoringMath.FormalPeriods.RowReduction`). A subspace of `FreeMod K n` is
given by an explicit spanning set, i.e. a matrix `A : FreeMatrix K m n`
whose rows span it (`inRowSpan A v`: an explicit linear combination of the
rows, pointwise in the coordinates). All decisions are computable functions
returning `Bool`, with explicit `Decidable` instances and correctness
lemmas:
* membership `v ∈ span(rows A)` is decided by the rank comparison
  `rankOf (matSnoc A v) = rankOf A` (`memRowSpanBool`), where `rankOf` is the
  number of nonzero rows of the RREF computed by P.2.1 — `v ∈ span S` iff
  `rank(S ∪ {v}) = rank S`;
* containment `span B ⊆ span A` is decided row by row (`spanContainsBool`);
* equality of spans is decided by mutual containment (`spanEqBool`);
* for a subspace given directly by its RREF normal form, membership is
  decided by the residual against the pivot rows (`rrefResidualBool`).
Correctness rests on two constructive facts proved here: row operations and
the whole elimination loop preserve the row span (`inRowSpan_rref`), and the
RREF of a matrix is unique among RREF matrices with the same row span
(`rref_eq_of_span_eq`, and the one-sided refinement
`rref_eq_of_subset_nzCount`), from which the rank criterion follows. No
`Classical.choice`, no `sorry`: every declaration lints CLEAN (see the
`#lint_axioms` block at the end of the file).
Program context: this is the decidability supply behind the finite-dimensional
quotient computations in Hörmann's formal-period filtration.
## References
* R. Mines, F. Richman, W. Ruitenburg, *A Course in Constructive Algebra*,
  Springer Universitext, 1988, eBook DOI 10.1007/978-1-4419-8640-5, Pt. II
  Ch. 6 "Matrices and vector spaces" (row spaces, rank, Gaussian elimination
  over discrete fields; DOI and TOC verified via web) — the rank criterion
  `v ∈ span S ↔ rank(S ∪ {v}) = rank S` and the uniqueness of the reduced
  row-echelon form.
* F. Hörmann, *A note on formal periods*, arXiv:2106.03803, Def. 3.1 and
  Remark 3.3 (verified against the arXiv source): `P^k(M) = P^∞(M)` for
  `k = dim H_B(M)` — the stabilization this decidability layer computes.
* S. Axler, *Linear Algebra Done Right*, 4th ed., Ch. 1 (span as the set of
  linear combinations).
-/
universe u
namespace BoringMath
open BigOperators
variable {K : Type u} [Field K] {m n k p : ℕ}
variable (invK : K → K)
/-! ## Finite sums over `Fin m` (choice-free) -/
-- Reference: program notes (P.0.4 pin-run census): `Fin.fintype` and
-- `List.toFinset` are choice-tainted at the pin v4.35.0-rc3, so finite sums
-- over `Fin m` avoid `Finset.univ`; the finset of `Fin m` is built by hand
-- from the nodup list `List.finRange m`, and sums over it are list sums.
/-- The finset of all of `Fin m`, built by hand from `List.finRange m`. -/
def finFinset (m : ℕ) : Finset (Fin m) := ⟨List.finRange m, List.nodup_finRange m⟩
-- Reference: MRR 1988, Pt. II Ch. 6 (finite sums as list sums).
/-- A finite sum over `Fin m` is the list sum of `finRange m`. -/
def finSum {m : ℕ} (f : Fin m → K) : K := ((List.finRange m).map f).sum
-- Reference: MRR 1988, Pt. II Ch. 6 (finite sums over the hand-built finset are
-- list sums).
/-- A sum over `finFinset m` is the corresponding `finSum`. -/
theorem sum_finFinset {m : ℕ} (f : Fin m → K) :
    ∑ a ∈ finFinset m, f a = finSum f := by
  show (Multiset.map f (List.finRange m : Multiset (Fin m))).sum
      = ((List.finRange m).map f).sum
  exact (congrArg Multiset.sum (Multiset.map_coe f (List.finRange m))).trans
    (Multiset.sum_coe ((List.finRange m).map f))
-- Reference: MRR 1988, Pt. II Ch. 6 (finite sums).
/-- Splitting a `finSum` over `Fin (k + 1)` at row `0`. -/
theorem finSum_succ {k : ℕ} (f : Fin (k + 1) → K) :
    finSum f = f 0 + finSum (fun a => f (Fin.succ a)) := by
  unfold finSum
  exact (congrArg (fun l => (l.map f).sum) List.finRange_succ).trans
    ((congrArg List.sum (List.map_cons (f := f) (a := 0)
        (l := (List.finRange k).map Fin.succ))).trans
    ((List.sum_cons (a := f 0) (l := ((List.finRange k).map Fin.succ).map f)).trans
    (congrArg (f 0 + ·) (congrArg List.sum (List.map_map (f := Fin.succ) (g := f) (l := List.finRange k))))))
-- Reference: MRR 1988, Pt. II Ch. 6 (finite sums).
/-- Splitting a `finSum` over `Fin (m + 1)` at the last row. -/
theorem finSum_castSucc {m : ℕ} (f : Fin (m + 1) → K) :
    finSum f = finSum (fun a => f (Fin.castSucc a)) + f (Fin.last m) := by
  unfold finSum
  exact (congrArg (fun l => (l.map f).sum) List.finRange_succ_last).trans
    ((congrArg List.sum (List.map_append (f := f)
        (l₁ := (List.finRange m).map Fin.castSucc) (l₂ := [Fin.last m]))).trans
    ((List.sum_append (l₁ := ((List.finRange m).map Fin.castSucc).map f)
        (l₂ := ([Fin.last m]).map f)).trans
    ((congrArg (· + (([Fin.last m]).map f).sum)
        (congrArg List.sum (List.map_map (f := Fin.castSucc) (g := f) (l := List.finRange m)))).trans
    (congrArg (((List.finRange m).map (f ∘ Fin.castSucc)).sum + ·)
      (((congrArg List.sum (List.map_cons (f := f) (a := Fin.last m) (l := []))).trans
        (List.sum_cons (a := f (Fin.last m)) (l := ([] : List (Fin (m + 1))).map f))).trans
      ((congrArg (f (Fin.last m) + ·)
        ((congrArg List.sum List.map_nil).trans List.sum_nil)).trans (add_zero _)))))))
-- Reference: MRR 1988, Pt. II Ch. 6 (finite sums).
/-- Splitting a finite sum over `Fin (k + 1)` at row `0`. -/
theorem sum_finFinset_succ {k : ℕ} (f : Fin (k + 1) → K) :
    ∑ a ∈ finFinset (k + 1), f a = f 0 + ∑ a ∈ finFinset k, f (Fin.succ a) :=
  ((sum_finFinset f).trans (finSum_succ f)).trans
    (congrArg (f 0 + ·) (sum_finFinset (fun a => f (Fin.succ a))).symm)
-- Reference: MRR 1988, Pt. II Ch. 6 (finite sums).
/-- Splitting a finite sum over `Fin (m + 1)` at the last row. -/
theorem sum_finFinset_castSucc {m : ℕ} (f : Fin (m + 1) → K) :
    ∑ a ∈ finFinset (m + 1), f a
        = (∑ a ∈ finFinset m, f (Fin.castSucc a)) + f (Fin.last m) :=
  ((sum_finFinset f).trans (finSum_castSucc f)).trans
    (congrArg (· + f (Fin.last m)) (sum_finFinset (fun a => f (Fin.castSucc a))).symm)
/-! ## List-sum lemmas (choice-free replacements for the tainted `Finset` ones) -/
-- Reference: MRR 1988, Pt. II Ch. 6 (finite sums); nil case of `list_sum_eq_zero`.
/-- The nil case of the vanishing list sum. -/
theorem list_sum_eq_zero_nil {α : Type} {f : α → K} :
    (([] : List α).map f).sum = 0 :=
  (congrArg List.sum List.map_nil).trans List.sum_nil
-- Reference: MRR 1988, Pt. II Ch. 6 (finite sums); cons case of
-- `list_sum_eq_zero`.
/-- The cons case of the vanishing list sum. -/
theorem list_sum_eq_zero_cons {α : Type} {f : α → K} (x : α) (xs : List α)
    (ih : (∀ y ∈ xs, f y = 0) → (xs.map f).sum = 0)
    (h : ∀ y ∈ x :: xs, f y = 0) :
    ((x :: xs).map f).sum = 0 :=
  ((congrArg List.sum (List.map_cons (f := f) (a := x) (l := xs))).trans
    (List.sum_cons (a := f x) (l := xs.map f))).trans
    ((congrArg (· + (xs.map f).sum) (h x List.mem_cons_self)).trans
      ((congrArg (0 + ·) (ih fun y hy => h y (List.mem_cons.mpr (Or.inr hy)))).trans
        (zero_add _)))
-- Reference: MRR 1988, Pt. II Ch. 6 (finite sums); `sum_finFinset_eq_zero`,
-- `Finset.sum_congr` and `Finset.sum_eq_single` are choice-tainted at the pin
-- v4.35.0-rc3, so the needed sum facts are proved directly by list induction.
/-- A list sum vanishes if every summand does. -/
theorem list_sum_eq_zero {α : Type} {l : List α} {f : α → K} (h : ∀ x ∈ l, f x = 0) :
    (l.map f).sum = 0 := by
  induction l with
  | nil => exact list_sum_eq_zero_nil
  | cons x xs ih => exact list_sum_eq_zero_cons x xs ih h
-- Reference: MRR 1988, Pt. II Ch. 6 (finite sums); nil case of `list_sum_congr`.
/-- The nil case of pointwise list-sum congruence. -/
theorem list_sum_congr_nil {α : Type} {f g : α → K} :
    (([] : List α).map f).sum = (([] : List α).map g).sum :=
  (congrArg List.sum List.map_nil).trans (congrArg List.sum List.map_nil).symm
-- Reference: MRR 1988, Pt. II Ch. 6 (finite sums); cons case of
-- `list_sum_congr`.
/-- The cons case of pointwise list-sum congruence. -/
theorem list_sum_congr_cons {α : Type} {f g : α → K} (x : α) (xs : List α)
    (ih : (∀ y ∈ xs, f y = g y) → (xs.map f).sum = (xs.map g).sum)
    (h : ∀ y ∈ x :: xs, f y = g y) :
    ((x :: xs).map f).sum = ((x :: xs).map g).sum :=
  ((congrArg List.sum (List.map_cons (f := f) (a := x) (l := xs))).trans
    (List.sum_cons (a := f x) (l := xs.map f))).trans
    ((congrArg₂ (· + ·) (h x List.mem_cons_self)
      (ih fun y hy => h y (List.mem_cons.mpr (Or.inr hy)))).trans
    ((List.sum_cons (a := g x) (l := xs.map g)).symm.trans
      (congrArg List.sum (List.map_cons (f := g) (a := x) (l := xs)).symm)))
-- Reference: MRR 1988, Pt. II Ch. 6 (finite sums).
/-- List sums are congruent pointwise. -/
theorem list_sum_congr {α : Type} {l : List α} {f g : α → K} (h : ∀ x ∈ l, f x = g x) :
    (l.map f).sum = (l.map g).sum := by
  induction l with
  | nil => exact list_sum_congr_nil
  | cons x xs ih => exact list_sum_congr_cons x xs ih h
-- Reference: MRR 1988, Pt. II Ch. 6 (finite sums); cons case of
-- `list_sum_eq_single` when the head IS the marked index.
/-- The cons case of the single-summand list sum, head equal to the mark. -/
theorem list_sum_eq_single_cons_eq {α : Type} [DecidableEq α] {f : α → K} {b : α}
    (x : α) (xs : List α) (hx : x = b)
    (h0 : ∀ a ∈ x :: xs, a ≠ b → f a = 0) (hnd : (x :: xs).Nodup) :
    ((x :: xs).map f).sum = f b :=
  ((congrArg List.sum (List.map_cons (f := f) (a := x) (l := xs))).trans
    (List.sum_cons (a := f x) (l := xs.map f))).trans
    ((congrArg (f x + ·) (list_sum_eq_zero (fun y hy =>
      h0 y (List.mem_cons.mpr (Or.inr hy))
        (fun heq => (List.nodup_cons.mp hnd).1 (Eq.mp (congrArg (· ∈ xs) (heq.trans hx.symm)) hy))))).trans
      ((congrArg (· + 0) (congrArg f hx)).trans (add_zero _)))
-- Reference: MRR 1988, Pt. II Ch. 6 (finite sums); cons case of
-- `list_sum_eq_single` when the head is NOT the marked index.
/-- The cons case of the single-summand list sum, head different from the
mark. -/
theorem list_sum_eq_single_cons_ne {α : Type} [DecidableEq α] {f : α → K} {b : α}
    (x : α) (xs : List α) (hx : x ≠ b)
    (ih : (∀ a ∈ xs, a ≠ b → f a = 0) → b ∈ xs → xs.Nodup → (xs.map f).sum = f b)
    (h0 : ∀ a ∈ x :: xs, a ≠ b → f a = 0) (hb : b ∈ x :: xs) (hnd : (x :: xs).Nodup) :
    ((x :: xs).map f).sum = f b :=
  ((congrArg List.sum (List.map_cons (f := f) (a := x) (l := xs))).trans
    (List.sum_cons (a := f x) (l := xs.map f))).trans
    ((congrArg (· + (xs.map f).sum) (h0 x List.mem_cons_self hx)).trans
      ((congrArg (0 + ·) (ih (fun a ha hne => h0 a (List.mem_cons.mpr (Or.inr ha)) hne)
        (List.mem_cons.mp hb |>.elim (fun h => absurd h.symm hx) id)
        (List.nodup_cons.mp hnd).2)).trans (zero_add _)))
-- Reference: MRR 1988, Pt. II Ch. 6 (finite sums).
set_option linter.unusedVariables false in
/-- A nodup list sum with a single possibly-nonzero summand at a listed index
is that summand. -/
theorem list_sum_eq_single {α : Type} [DecidableEq α] {l : List α} {f : α → K} {b : α}
    (h0 : ∀ a ∈ l, a ≠ b → f a = 0) (hb : b ∈ l) (hnd : l.Nodup) :
    (l.map f).sum = f b := by
  induction l with
  | nil => exact absurd hb List.not_mem_nil
  | cons x xs ih =>
      cases (inferInstance : Decidable (x = b)) with
      | isTrue hx => exact list_sum_eq_single_cons_eq x xs hx h0 hnd
      | isFalse hx => exact list_sum_eq_single_cons_ne x xs hx ih h0 hb hnd
-- Reference: MRR 1988, Pt. II Ch. 6 (counting); cons case of
-- `list_countP_eq_zero`.
/-- The cons case of the vanishing `countP`. -/
theorem list_countP_eq_zero_cons {α : Type} {p : α → Bool} (x : α) (xs : List α)
    (ih : (∀ y ∈ xs, ¬ p y = true) → List.countP p xs = 0)
    (h : ∀ y ∈ x :: xs, ¬ p y = true) :
    List.countP p (x :: xs) = 0 :=
  (List.countP_cons_of_neg (h x List.mem_cons_self)).trans
    (ih fun y hy => h y (List.mem_cons.mpr (Or.inr hy)))
-- Reference: MRR 1988, Pt. II Ch. 6 (counting); `List.countP_eq_zero` is
-- choice-tainted at the pin v4.35.0-rc3, so this is proved by list induction.
/-- A `countP` vanishes if the predicate never says `true` on the list. -/
theorem list_countP_eq_zero {α : Type} {l : List α} {p : α → Bool}
    (h : ∀ a ∈ l, ¬ p a = true) : List.countP p l = 0 := by
  induction l with
  | nil => exact List.countP_nil
  | cons x xs ih => exact list_countP_eq_zero_cons x xs ih h
-- Reference: MRR 1988, Pt. II Ch. 6 (finite sums over `Fin 0`).
/-- A `finSum` over `Fin 0` is `0`. -/
theorem finSum_zero {f : Fin 0 → K} : finSum f = 0 := by
  unfold finSum
  exact (congrArg (fun l => (l.map f).sum) List.finRange_zero).trans
    ((congrArg List.sum List.map_nil).trans List.sum_nil)
-- Reference: MRR 1988, Pt. II Ch. 6 (finite sums over `Fin m`).
/-- A `finSum` vanishes if every summand does. -/
theorem finSum_eq_zero {m : ℕ} {f : Fin m → K} (h : ∀ a, f a = 0) : finSum f = 0 := by
  unfold finSum
  exact list_sum_eq_zero (fun a _ => h a)
-- Reference: MRR 1988, Pt. II Ch. 6 (finite sums over `Fin m`).
/-- `finSum`s are congruent pointwise. -/
theorem finSum_congr {m : ℕ} {f g : Fin m → K} (h : ∀ a, f a = g a) :
    finSum f = finSum g := by
  unfold finSum
  exact list_sum_congr (fun a _ => h a)
-- Reference: MRR 1988, Pt. II Ch. 6 (finite sums over `Fin m`).
/-- A `finSum` with a single possibly-nonzero summand at `b` is `f b`. -/
theorem finSum_eq_single {m : ℕ} {f : Fin m → K} {b : Fin m} (h0 : ∀ a, a ≠ b → f a = 0) :
    finSum f = f b := by
  unfold finSum
  exact list_sum_eq_single (fun a _ ha => h0 a ha) (List.mem_finRange b)
    (List.nodup_finRange m)
-- Reference: MRR 1988, Pt. II Ch. 6 (finite sums over `finFinset m`).
/-- A sum over `finFinset m` vanishes if every summand does. -/
theorem sum_finFinset_eq_zero {m : ℕ} {f : Fin m → K} (h : ∀ a, f a = 0) :
    ∑ a ∈ finFinset m, f a = 0 :=
  (sum_finFinset _).trans (list_sum_eq_zero (fun a _ => h a))
-- Reference: MRR 1988, Pt. II Ch. 6 (finite sums over `finFinset m`).
/-- Sums over `finFinset m` are congruent pointwise. -/
theorem sum_finFinset_congr {m : ℕ} {f g : Fin m → K} (h : ∀ a, f a = g a) :
    ∑ a ∈ finFinset m, f a = ∑ a ∈ finFinset m, g a :=
  (sum_finFinset f).trans
    ((list_sum_congr (fun a _ => h a)).trans (sum_finFinset g).symm)
-- Reference: MRR 1988, Pt. II Ch. 6 (finite sums over `finFinset m`).
/-- A sum over `finFinset m` with a single possibly-nonzero summand at `b` is
`f b`. -/
theorem sum_finFinset_eq_single {m : ℕ} {f : Fin m → K} {b : Fin m}
    (h0 : ∀ a, a ≠ b → f a = 0) :
    ∑ a ∈ finFinset m, f a = f b :=
  (sum_finFinset _).trans (list_sum_eq_single (fun a _ ha => h0 a ha)
    (List.mem_finRange b) (List.nodup_finRange m))
/-! ## The row span of an explicit spanning set -/
-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6 (row space of a
-- matrix over a discrete field); Axler, Ch. 1 (span = linear combinations).
/-- `v` lies in the row span of `A`: an explicit linear combination of the
rows of `A`, stated pointwise in the coordinates. -/
def inRowSpan (A : FreeMatrix K m n) (v : FreeMod K n) : Prop :=
  ∃ c : Fin m → K, ∀ j : Fin n, v j = ∑ a ∈ finFinset _, c a * A a j
-- Reference: MRR 1988, Pt. II Ch. 6 (a row lies in its own row space).
/-- Every row of `A` lies in the row span of `A`. -/
theorem inRowSpan_self (A : FreeMatrix K m n) (b : Fin m) : inRowSpan A (A b) :=
  ⟨fun a => if a = b then 1 else 0, fun j =>
    let hs := sum_finFinset_eq_single (f := fun a => (if a = b then 1 else 0) * A a j)
      (fun a hab => (congrArg (· * A a j) (ite_eq_right hab)).trans (zero_mul (A a j)))
    let e : (if b = b then 1 else 0) * A b j = A b j :=
      (congrArg (· * A b j) (ite_eq_left (Eq.refl b))).trans (one_mul (A b j))
    (hs.trans e).symm⟩
-- Reference: MRR 1988, Pt. II Ch. 6 (the zero vector is in every span).
/-- The zero vector lies in the row span of `A`. -/
theorem inRowSpan_zero (A : FreeMatrix K m n) : inRowSpan A 0 :=
  ⟨fun _ => 0, fun _ => (sum_finFinset_eq_zero (fun _ => zero_mul _)).symm⟩
-- Reference: MRR 1988, Pt. II Ch. 6 (spans are closed under scalar
-- multiplication).
/-- The row span is closed under scalar multiplication. -/
theorem inRowSpan_smul (c : K) {A : FreeMatrix K m n} {v : FreeMod K n}
    (h : inRowSpan A v) : inRowSpan A (c • v) :=
  let ⟨d, hd⟩ := h
  ⟨fun a => c * d a, fun j =>
    (Pi.smul_apply c v j).trans ((congrArg (c * ·) (hd j)).trans
      ((Finset.mul_sum _ _ c).trans (sum_finFinset_congr (fun a =>
        (mul_assoc c (d a) (A a j)).symm))))⟩
-- Reference: MRR 1988, Pt. II Ch. 6 (spans are closed under addition).
/-- The row span is closed under addition. -/
theorem inRowSpan_add {A : FreeMatrix K m n} {u v : FreeMod K n}
    (hu : inRowSpan A u) (hv : inRowSpan A v) : inRowSpan A (u + v) :=
  let ⟨cu, hu'⟩ := hu
  let ⟨cv, hv'⟩ := hv
  ⟨fun a => cu a + cv a, fun j =>
    (Pi.add_apply u v j).trans ((congrArg₂ (· + ·) (hu' j) (hv' j)).trans
      ((Finset.sum_add_distrib).symm.trans (sum_finFinset_congr (fun a =>
        (add_mul (cu a) (cv a) (A a j)).symm))))⟩
-- Reference: MRR 1988, Pt. II Ch. 6 (spans are closed under negation).
/-- The row span is closed under negation. -/
theorem inRowSpan_neg {A : FreeMatrix K m n} {v : FreeMod K n} (h : inRowSpan A v) :
    inRowSpan A (-v) :=
  let ⟨d, hd⟩ := h
  ⟨fun a => -d a, fun j =>
    (Pi.neg_apply v j).trans ((congrArg (-·) (hd j)).trans
      (((Finset.sum_neg_distrib _).symm).trans (sum_finFinset_congr (fun a =>
        (neg_mul (d a) (A a j)).symm))))⟩
-- Reference: MRR 1988, Pt. II Ch. 6 (spans are closed under subtraction).
/-- The row span is closed under subtraction. -/
theorem inRowSpan_sub {A : FreeMatrix K m n} {u v : FreeMod K n}
    (hu : inRowSpan A u) (hv : inRowSpan A v) : inRowSpan A (u - v) :=
  Eq.mpr (congrArg (inRowSpan A) (sub_eq_add_neg u v)) (inRowSpan_add hu (inRowSpan_neg hv))
/-! ## Appending a row to the spanning set -/
-- Reference: MRR 1988, Pt. II Ch. 6 (appending a generator to a spanning set).
/-- Append the vector `v` as a new last row of `A`. -/
def matSnoc (A : FreeMatrix K m n) (v : FreeMod K n) : FreeMatrix K (m + 1) n :=
  fun a c => if h : a.val < m then A ⟨a.val, h⟩ c else v c
-- Reference: definitional peel of `matSnoc` at a `castSucc` row.
/-- The old rows of `A` are unchanged by `matSnoc`. -/
theorem matSnoc_castSucc (A : FreeMatrix K m n) (v : FreeMod K n) (a : Fin m) (c : Fin n) :
    matSnoc A v (Fin.castSucc a) c = A a c :=
  dite_eq_left a.isLt
-- Reference: definitional peel of `matSnoc` at the last row.
/-- The appended vector is the last row of `matSnoc A v`. -/
theorem matSnoc_last (A : FreeMatrix K m n) (v : FreeMod K n) (c : Fin n) :
    matSnoc A v (Fin.last m) c = v c :=
  dite_eq_right (Nat.lt_irrefl m)
-- Reference: MRR 1988, Pt. II Ch. 6 (the sum over the appended matrix splits
-- at the last row); peel of `sum_finFinset_castSucc` along `matSnoc`.
/-- The `finFinset` sum of `c a * matSnoc A v a j` splits at the last row. -/
theorem inRowSpan_snoc_sum_fwd {A : FreeMatrix K m n} {v : FreeMod K n}
    (c : Fin (m + 1) → K) (j : Fin n) :
    ∑ a ∈ finFinset (m + 1), c a * matSnoc A v a j
      = (∑ a ∈ finFinset m, c (Fin.castSucc a) * A a j) + c (Fin.last m) * v j := by
  have h2 : ∑ a ∈ finFinset (m + 1), c a * matSnoc A v a j
      = (∑ a ∈ finFinset m, c (Fin.castSucc a) * matSnoc A v (Fin.castSucc a) j)
        + c (Fin.last m) * matSnoc A v (Fin.last m) j :=
    sum_finFinset_castSucc (fun a : Fin (m + 1) => c a * matSnoc A v a j)
  have hcast : (∑ a ∈ finFinset m, c (Fin.castSucc a) * matSnoc A v (Fin.castSucc a) j)
      = ∑ a ∈ finFinset m, c (Fin.castSucc a) * A a j :=
    sum_finFinset_congr (fun a =>
      congrArg (c (Fin.castSucc a) * ·) (matSnoc_castSucc A v a j))
  have hlast : c (Fin.last m) * matSnoc A v (Fin.last m) j = c (Fin.last m) * v j :=
    congrArg (c (Fin.last m) * ·) (matSnoc_last A v j)
  exact h2.trans ((congrArg (· + c (Fin.last m) * matSnoc A v (Fin.last m) j) hcast).trans
    (congrArg ((∑ a ∈ finFinset m, c (Fin.castSucc a) * A a j) + ·) hlast))
-- Reference: MRR 1988, Pt. II Ch. 6 (the `dite`-coefficient sum reassembled
-- coefficient); peel of `sum_finFinset_castSucc` along the `dite` rows.
/-- The `finFinset` sum of a `dite` coefficient against `matSnoc` splits. -/
theorem inRowSpan_snoc_sum_bwd {A : FreeMatrix K m n} {v : FreeMod K n}
    (c : Fin m → K) (d : K) (j : Fin n) :
    ∑ a ∈ finFinset (m + 1),
        (if h : a.val < m then c ⟨a.val, h⟩ else d) * matSnoc A v a j
      = (∑ a ∈ finFinset m, c a * A a j) + d * v j := by
  have h2 : ∑ a ∈ finFinset (m + 1),
        (if h : a.val < m then c ⟨a.val, h⟩ else d) * matSnoc A v a j
      = (∑ a ∈ finFinset m, (if h : (Fin.castSucc a).val < m then
            c ⟨(Fin.castSucc a).val, h⟩ else d) * matSnoc A v (Fin.castSucc a) j)
        + (if h : (Fin.last m).val < m then c ⟨(Fin.last m).val, h⟩ else d)
          * matSnoc A v (Fin.last m) j :=
    sum_finFinset_castSucc (fun a : Fin (m + 1) =>
      (if h : a.val < m then c ⟨a.val, h⟩ else d) * matSnoc A v a j)
  have hcast : (∑ a ∈ finFinset m, (if h : (Fin.castSucc a).val < m then
        c ⟨(Fin.castSucc a).val, h⟩ else d) * matSnoc A v (Fin.castSucc a) j)
      = ∑ a ∈ finFinset m, c a * A a j :=
    sum_finFinset_congr (fun a =>
      ((congrArg (fun z => (if h : z < m then c ⟨z, h⟩ else d)
          * matSnoc A v (Fin.castSucc a) j) (Fin.val_castSucc a)).trans
        (congrArg (· * matSnoc A v (Fin.castSucc a) j) (dite_eq_left a.isLt))).trans
        (congrArg (c ⟨a.val, a.isLt⟩ * ·) (matSnoc_castSucc A v a j)))
  have hlast : (if h : (Fin.last m).val < m then c ⟨(Fin.last m).val, h⟩ else d)
      * matSnoc A v (Fin.last m) j = d * v j :=
    ((congrArg (fun z => (if h : z < m then c ⟨z, h⟩ else d)
        * matSnoc A v (Fin.last m) j) (Fin.val_last m)).trans
      (congrArg (· * matSnoc A v (Fin.last m) j)
        (dite_eq_right (Nat.lt_irrefl m)))).trans
      (congrArg (d * ·) (matSnoc_last A v j))
  exact h2.trans ((congrArg (· + (if h : (Fin.last m).val < m then c ⟨(Fin.last m).val, h⟩ else d)
        * matSnoc A v (Fin.last m) j) hcast).trans
    (congrArg ((∑ a ∈ finFinset m, c a * A a j) + ·) hlast))
-- Reference: MRR 1988, Pt. II Ch. 6 (span of a spanning set with one more
-- generator: `span(S ∪ {v}) = span S + K v`); forward direction.
/-- Forward direction of the snoc membership decomposition: read the coefficient of
the appended row off the last summand. -/
theorem inRowSpan_snoc_mp {A : FreeMatrix K m n} {v w : FreeMod K n}
    (h : inRowSpan (matSnoc A v) w) :
    ∃ u : FreeMod K n, inRowSpan A u ∧ ∃ d : K, ∀ j : Fin n, w j = u j + d * v j :=
  let ⟨c, hc⟩ := h
  ⟨fun j => ∑ a ∈ finFinset m, c (Fin.castSucc a) * A a j,
    ⟨fun a => c (Fin.castSucc a), fun _ => rfl⟩, c (Fin.last m), fun j =>
      (hc j).trans (inRowSpan_snoc_sum_fwd c j)⟩
-- Reference: MRR 1988, Pt. II Ch. 6 (span of a spanning set with one more
-- generator: `span(S ∪ {v}) = span S + K v`); backward direction.
/-- Backward direction of the snoc membership decomposition: reassemble the
combination with a `dite` coefficient. -/
theorem inRowSpan_snoc_mpr {A : FreeMatrix K m n} {v w : FreeMod K n}
    (h : ∃ u : FreeMod K n, inRowSpan A u ∧ ∃ d : K, ∀ j : Fin n, w j = u j + d * v j) :
    inRowSpan (matSnoc A v) w :=
  let ⟨u, ⟨c, hc⟩, d, hw⟩ := h
  ⟨fun a => if h : a.val < m then c ⟨a.val, h⟩ else d, fun j =>
    ((hw j).trans (congrArg (· + d * v j) (hc j))).trans
      (inRowSpan_snoc_sum_bwd c d j).symm⟩
-- Reference: MRR 1988, Pt. II Ch. 6 (span of a spanning set with one more
-- generator: `span(S ∪ {v}) = span S + K v`).
/-- Membership in the row span after appending one row: `w` is in
`span(rows A ∪ {v})` iff `w = u + d • v` pointwise with `u` in the row span
of `A`. -/
theorem inRowSpan_snoc {A : FreeMatrix K m n} {v w : FreeMod K n} :
    inRowSpan (matSnoc A v) w ↔
      ∃ u : FreeMod K n, inRowSpan A u ∧ ∃ d : K, ∀ j : Fin n, w j = u j + d * v j :=
  ⟨fun h => inRowSpan_snoc_mp h, fun h => inRowSpan_snoc_mpr h⟩
-- Reference: MRR 1988, Pt. II Ch. 6 (a matrix is the snoc of its tail and
-- its last row); definitional peel.
/-- Every matrix is the `matSnoc` of its `castSucc` rows and its last row. -/
theorem matSnoc_tail_last (A : FreeMatrix K (k + 1) n) :
    A = matSnoc (fun a : Fin k => A (Fin.castSucc a)) (A (Fin.last k)) :=
  funext fun a => funext fun c =>
    match Fin.eq_castSucc_or_eq_last a with
    | Or.inl ⟨a', ha'⟩ =>
        Eq.mp (congrArg (fun z => A z c = matSnoc (fun a' => A (Fin.castSucc a'))
            (A (Fin.last k)) z c) ha'.symm)
          (matSnoc_castSucc (fun a' => A (Fin.castSucc a')) (A (Fin.last k)) a' c).symm
    | Or.inr ha' =>
        Eq.mp (congrArg (fun z => A z c = matSnoc (fun a' => A (Fin.castSucc a'))
            (A (Fin.last k)) z c) ha'.symm)
          (matSnoc_last (fun a' => A (Fin.castSucc a')) (A (Fin.last k)) c).symm
-- Reference: MRR 1988, Pt. II Ch. 6 (if every generator of `S` lies in the
-- span of `T` then `span S ⊆ span T`); zero-row case.
/-- The zero-row case of the span monotonicity induction. -/
theorem inRowSpan_mono_zero {p : ℕ} {B : FreeMatrix K p n} (A : FreeMatrix K 0 n)
    (w : FreeMod K n) (hw : inRowSpan A w) : inRowSpan B w :=
  let ⟨c, hc⟩ := hw
  ⟨fun _ => 0, fun j =>
    ((hc j).trans ((sum_finFinset (fun a => c a * A a j)).trans finSum_zero)).trans
      (sum_finFinset_eq_zero (fun _ => zero_mul (B _ j))).symm⟩
-- Reference: MRR 1988, Pt. II Ch. 6 (if every generator of `S` lies in the
-- span of `T` then `span S ⊆ span T`); successor case, peeling the last row.
/-- The successor case of the span monotonicity induction. -/
theorem inRowSpan_mono_succ {p : ℕ} {B : FreeMatrix K p n} (k : ℕ)
    (ih : ∀ (A : FreeMatrix K k n) (w : FreeMod K n),
      (∀ a : Fin k, inRowSpan B (A a)) → inRowSpan A w → inRowSpan B w)
    (A : FreeMatrix K (k + 1) n) (w : FreeMod K n)
    (h : ∀ a : Fin (k + 1), inRowSpan B (A a)) (hw : inRowSpan A w) :
    inRowSpan B w :=
  let M := fun a : Fin k => A (Fin.castSucc a)
  let v := A (Fin.last k)
  let hsplit := matSnoc_tail_last A
  let hw' : inRowSpan (matSnoc M v) w :=
    Eq.mp (congrArg (fun M' => inRowSpan M' w) hsplit) hw
  let h' : ∀ a : Fin (k + 1), inRowSpan B (matSnoc M v a) :=
    fun a => Eq.mp (congrArg (fun M' => inRowSpan B (M' a)) hsplit) (h a)
  let ⟨u, hu, d, hwu⟩ := inRowSpan_snoc.mp hw'
  let hcast : ∀ a : Fin k, matSnoc M v (Fin.castSucc a) = A (Fin.castSucc a) :=
    fun a => funext (fun c => matSnoc_castSucc _ _ a c)
  let hlast : matSnoc M v (Fin.last k) = A (Fin.last k) := funext (fun c => matSnoc_last _ _ c)
  let hrows : ∀ a : Fin k, inRowSpan B (A (Fin.castSucc a)) :=
    fun a => Eq.mp (congrArg (inRowSpan B) (hcast a)) (h' (Fin.castSucc a))
  let huB : inRowSpan B u := ih M u hrows hu
  let hvB : inRowSpan B (A (Fin.last k)) :=
    Eq.mp (congrArg (inRowSpan B) hlast) (h' (Fin.last k))
  let hwB : inRowSpan B (u + d • A (Fin.last k)) := inRowSpan_add huB (inRowSpan_smul d hvB)
  Eq.mpr (congrArg (fun z => inRowSpan B z) (funext hwu)) hwB
-- Reference: MRR 1988, Pt. II Ch. 6 (if every generator of `S` lies in the
-- span of `T` then `span S ⊆ span T`); proved by induction on the number of
-- rows, so no choice of combination witnesses is needed.
/-- If every row of `A` lies in the row span of `B`, then every vector in
the row span of `A` lies in the row span of `B`. -/
theorem inRowSpan_mono {p : ℕ} {B : FreeMatrix K p n} :
    ∀ (q : ℕ) (A : FreeMatrix K q n) (w : FreeMod K n),
    (∀ a : Fin q, inRowSpan B (A a)) → inRowSpan A w → inRowSpan B w :=
  fun q => Nat.rec (motive := fun q => ∀ (A : FreeMatrix K q n) (w : FreeMod K n),
      (∀ a : Fin q, inRowSpan B (A a)) → inRowSpan A w → inRowSpan B w)
    (fun A w _ hw => inRowSpan_mono_zero A w hw)
    (fun k ih A w h hw => inRowSpan_mono_succ k ih A w h hw) q
-- Reference: MRR 1988, Pt. II Ch. 6 (the appended generator is in the span).
/-- The appended vector `v` lies in the row span of `matSnoc A v`. -/
theorem inRowSpan_snoc_self {A : FreeMatrix K m n} {v : FreeMod K n} :
    inRowSpan (matSnoc A v) v :=
  inRowSpan_snoc.mpr ⟨0, inRowSpan_zero _, 1, fun j =>
    (one_mul (v j)).symm.trans (zero_add (1 * v j)).symm⟩
-- Reference: MRR 1988, Pt. II Ch. 6 (span S ⊆ span(S ∪ {v})).
/-- The row span only grows when a row is appended. -/
theorem inRowSpan_snoc_mono {A : FreeMatrix K m n} {v w : FreeMod K n}
    (h : inRowSpan A w) : inRowSpan (matSnoc A v) w :=
  inRowSpan_snoc.mpr ⟨w, h, 0, fun j =>
    ((congrArg (w j + ·) (zero_mul (v j))).trans (add_zero (w j))).symm⟩
-- Reference: MRR 1988, Pt. II Ch. 6 (if `v ∈ span S` then
-- `span(S ∪ {v}) = span S`); the sum reassembly in the forward direction.
/-- The sum step of the forward direction: adding a multiple of the span
witness of `v` to the witness of `u` stays a span witness. -/
theorem inRowSpan_snoc_of_mem_sum {A : FreeMatrix K m n}
    (cu e : Fin m → K) (d : K) (j : Fin n) :
    (∑ a ∈ finFinset m, cu a * A a j) + d * (∑ a ∈ finFinset m, e a * A a j)
      = ∑ a ∈ finFinset m, (cu a + d * e a) * A a j :=
  (congrArg ((∑ a ∈ finFinset m, cu a * A a j) + ·)
    (Finset.mul_sum (finFinset m) (fun a => e a * A a j) d)).trans
    (Finset.sum_add_distrib.symm.trans (sum_finFinset_congr (fun a =>
      (congrArg (cu a * A a j + ·) (mul_assoc d (e a) (A a j)).symm).trans
        (add_mul (cu a) (d * e a) (A a j)).symm)))
-- Reference: MRR 1988, Pt. II Ch. 6 (if `v ∈ span S` then
-- `span(S ∪ {v}) = span S`); forward direction.
/-- Forward direction: membership in the enlarged span implies membership in
the original span. -/
theorem inRowSpan_snoc_of_mem_fwd {A : FreeMatrix K m n} {v w : FreeMod K n}
    (hv : inRowSpan A v) (h : inRowSpan (matSnoc A v) w) : inRowSpan A w :=
  let ⟨u, hu, d, hw⟩ := inRowSpan_snoc.mp h
  let ⟨cu, chu⟩ := hu
  let ⟨e, he⟩ := hv
  ⟨fun a => cu a + d * e a, fun j =>
    (hw j).trans ((congrArg₂ (· + ·) (chu j) (congrArg (d * ·) (he j))).trans
      (inRowSpan_snoc_of_mem_sum cu e d j))⟩
-- Reference: MRR 1988, Pt. II Ch. 6 (if v ∈ span S then span(S ∪ {v}) = span S).
/-- Appending a row that already lies in the span does not change the span. -/
theorem inRowSpan_snoc_of_mem {A : FreeMatrix K m n} {v w : FreeMod K n}
    (hv : inRowSpan A v) : inRowSpan (matSnoc A v) w ↔ inRowSpan A w :=
  ⟨fun h => inRowSpan_snoc_of_mem_fwd hv h, fun h => inRowSpan_snoc_mono h⟩
variable [DecidableEq K]
/-! ## Pivot-search and leading-column peels -/
-- Reference: MRR 1988, Pt. II Ch. 6 (the pivot search is a congruence on the
-- predicate); successor step of the induction on the fuel.
/-- The successor step of the pivot-search congruence. -/
theorem findPivotRow_congr_succ {q : ℕ} {p r : Fin q → Bool} (h : ∀ i, p i = r i)
    (t lo : ℕ) (ih : ∀ lo, findPivotRow p t lo = findPivotRow r t lo) :
    findPivotRow p (t + 1) lo = findPivotRow r (t + 1) lo := by
  rcases Nat.lt_or_ge lo q with hlt | hge
  · exact ((findPivotRow_succ p t lo).trans (dite_eq_left hlt)).trans
      ((congrArg (fun b => if b then some ⟨lo, hlt⟩ else findPivotRow p t (lo + 1))
          (h ⟨lo, hlt⟩)).trans
      ((congrArg (fun z => if r ⟨lo, hlt⟩ then some ⟨lo, hlt⟩ else z) (ih (lo + 1))).trans
      ((dite_eq_left hlt).symm.trans (findPivotRow_succ r t lo))))
  · exact ((findPivotRow_succ p t lo).trans (dite_eq_right (Nat.not_lt.mpr hge))).trans
      (((findPivotRow_succ r t lo).trans (dite_eq_right (Nat.not_lt.mpr hge))).symm)
-- Reference: MRR 1988, Pt. II Ch. 6 (the pivot search only reads the
-- predicate; equal predicates give equal searches).
/-- The pivot search is a congruence on the predicate. -/
theorem findPivotRow_congr {q : ℕ} {p r : Fin q → Bool} (h : ∀ i, p i = r i) (t lo : ℕ) :
    findPivotRow p t lo = findPivotRow r t lo :=
  Nat.rec (motive := fun t => ∀ lo, findPivotRow p t lo = findPivotRow r t lo)
    (fun lo => (findPivotRow_zero p lo).trans (findPivotRow_zero r lo).symm)
    (fun t ih lo => findPivotRow_congr_succ h t lo ih) t lo
-- Reference: MRR 1988, Pt. II Ch. 6 (the search returns the FIRST hit);
-- successor step of the induction on the fuel.
/-- The successor step of the first-hit lemma. -/
theorem findPivotRow_some_first_succ {q : ℕ} {p : Fin q → Bool} {t lo : ℕ} {i i' : Fin q}
    (ih : ∀ lo', findPivotRow p t lo' = some i → lo' ≤ i'.val → p i' = false)
    (h : findPivotRow p (t + 1) lo = some i) (hle : lo ≤ i'.val) (hlt : i'.val < i.val) :
    p i' = false := by
  have h1 : (if h : lo < q then (if p ⟨lo, h⟩ then some ⟨lo, h⟩ else
      findPivotRow p t (lo + 1)) else none) = some i := Eq.subst (motive := fun z => z = some i) (findPivotRow_succ p t lo) h
  rcases Nat.lt_or_ge lo q with hltm | hgem
  · have h2 : (if p ⟨lo, hltm⟩ then some ⟨lo, hltm⟩ else findPivotRow p t (lo + 1))
      = some i := Eq.mp (congrArg (· = some i) (dite_eq_left hltm)) h1
    cases (inferInstance : Decidable (p ⟨lo, hltm⟩ = true)) with
    | isTrue hp =>
        have h3 : some ⟨lo, hltm⟩ = some i := Eq.mp (congrArg (· = some i) (ite_eq_left hp)) h2
        injection h3 with hval
        subst hval
        exact absurd hlt (Nat.not_lt.mpr hle)
    | isFalse hp =>
        have h4 : findPivotRow p t (lo + 1) = some i := Eq.mp (congrArg (· = some i) (ite_eq_right hp)) h2
        rcases Nat.lt_or_ge lo i'.val with hlt' | hge'
        · exact ih (lo + 1) h4 (Nat.succ_le_of_lt hlt')
        · have heq : i' = ⟨lo, hltm⟩ := Fin.eq_of_val_eq (Nat.le_antisymm hge' hle)
          exact Eq.mpr (congrArg (fun z => p z = false) heq) (Bool.eq_false_iff.mpr hp)
  · have h5 : none = some i := Eq.mp (congrArg (· = some i) (dite_eq_right (Nat.not_lt.mpr hgem))) h1
    cases h5
-- Reference: MRR 1988, Pt. II Ch. 6 (the search returns the FIRST row of the
-- range where the predicate holds).
-- Reference: MRR 1988, Pt. II Ch. 6 (the search returns the FIRST hit); the
-- zero-fuel case.
/-- With no fuel left, the search finds nothing, contradicting the hit. -/
theorem findPivotRow_some_first_zero {q : ℕ} {p : Fin q → Bool} {lo : ℕ} {i : Fin q}
    (h : findPivotRow p 0 lo = some i) (i' : Fin q) (hle : lo ≤ i'.val)
    (hlt : i'.val < i.val) : p i' = false := by
  have h0 : none = some i :=
    Eq.subst (motive := fun z => z = some i) (findPivotRow_zero p lo) h
  cases h0

theorem findPivotRow_some_first {q : ℕ} {p : Fin q → Bool} {t lo : ℕ} {i : Fin q}
    (h : findPivotRow p t lo = some i) (i' : Fin q) (hle : lo ≤ i'.val)
    (hlt : i'.val < i.val) :
    p i' = false := by
  induction t generalizing lo with
  | zero => exact findPivotRow_some_first_zero h i' hle hlt
  | succ t ih => exact findPivotRow_some_first_succ (i' := i') (fun lo' h' hle' => ih h' hle') h hle hlt
-- Reference: MRR 1988, Pt. II Ch. 6 (the leading column depends only on the
-- row entries).
/-- Rows with equal entries have equal leading columns. -/
theorem matLeadingCol_congr {p q : ℕ} {A : FreeMatrix K p n} {B : FreeMatrix K q n}
    {a : Fin p} {b : Fin q}
    (h : ∀ c, A a c = B b c) :
    matLeadingCol A a = matLeadingCol B b := by
  unfold matLeadingCol
  exact congrArg (fun o => match o with | some c => c.val | none => n)
    (findPivotRow_congr (fun c => congrArg (fun x => if x ≠ 0 then true else false) (h c)) n 0)
-- Reference: MRR 1988, Pt. II Ch. 6 (a leading column is at most `n`).
-- Reference: MRR 1988, Pt. II Ch. 6 (a leading column is at most `n`); the
-- `none` case.
/-- If the leading-column search of row `a` finds nothing, the leading column
is `n`, hence `≤ n`. -/
theorem matLeadingCol_le_none {A : FreeMatrix K m n} {a : Fin m}
    (hs : findPivotRow (fun c => if A a c ≠ 0 then true else false) n 0 = none) :
    matLeadingCol A a ≤ n :=
  Eq.mpr (congrArg (· ≤ n) (matLeadingCol_eq_none hs)) (Nat.le_refl n)
-- Reference: MRR 1988, Pt. II Ch. 6 (a leading column is at most `n`); the
-- `some` case.
/-- If the leading-column search of row `a` finds `c`, the leading column is
`c.val < n`. -/
theorem matLeadingCol_le_some {A : FreeMatrix K m n} {a : Fin m} {c : Fin n}
    (hs : findPivotRow (fun c => if A a c ≠ 0 then true else false) n 0 = some c) :
    matLeadingCol A a ≤ n :=
  Eq.mpr (congrArg (· ≤ n) (matLeadingCol_eq_some hs)) (Nat.le_of_lt c.isLt)
-- Reference: MRR 1988, Pt. II Ch. 6 (a leading column is at most `n`).
/-- The leading column of a row is at most `n`. -/
theorem matLeadingCol_le (A : FreeMatrix K m n) (a : Fin m) : matLeadingCol A a ≤ n := by
  cases hs : findPivotRow (fun c => if A a c ≠ 0 then true else false) n 0 with
  | none => exact matLeadingCol_le_none hs
  | some c => exact matLeadingCol_le_some hs
-- Reference: MRR 1988, Pt. II Ch. 6 (a zero row makes the pivot search fail).
/-- A zero row has no pivot: the search returns `none`. -/
theorem findPivotRow_eq_none_of_rowZero {B : FreeMatrix K m n} {a : Fin m}
    (h : matRowZero B a) :
    findPivotRow (fun c => if B a c ≠ 0 then true else false) n 0 = none :=
  findPivotRow_eq_none_of (fun c => ite_eq_right (fun hne => hne (h c)))
-- Reference: MRR 1988, Pt. II Ch. 6 (if the pivot search fails, the row is
-- zero).
/-- If the pivot search of a row returns `none`, the row is zero. -/
theorem rowZero_of_findPivotRow_eq_none {B : FreeMatrix K m n} {a : Fin m}
    (h : findPivotRow (fun c => if B a c ≠ 0 then true else false) n 0 = none) :
    matRowZero B a :=
  fun c => eq_zero_of_pivotBool (findPivotRow_none_spec h c (Nat.zero_le c.val)
    (Eq.subst (Nat.zero_add n).symm c.isLt))
-- Reference: MRR 1988, Pt. II Ch. 6 (a row with leading column `n` is zero).
-- Reference: MRR 1988, Pt. II Ch. 6 (a row with leading column `n` is zero);
-- the `none` case.
/-- If the leading-column search of row `a` finds nothing, the row is zero. -/
theorem matRowZero_of_matLeadingCol_eq_none {A : FreeMatrix K m n} {a : Fin m}
    (hs : findPivotRow (fun c => if A a c ≠ 0 then true else false) n 0 = none) :
    matRowZero A a :=
  rowZero_of_findPivotRow_eq_none hs
-- Reference: MRR 1988, Pt. II Ch. 6 (a row with leading column `n` is zero);
-- the `some` case.
/-- If the leading-column search of row `a` finds `c`, then `c.val = n` is
absurd. -/
theorem matRowZero_of_matLeadingCol_eq_some {A : FreeMatrix K m n} {a : Fin m} {c : Fin n}
    (hs : findPivotRow (fun c => if A a c ≠ 0 then true else false) n 0 = some c)
    (h : matLeadingCol A a = n) : matRowZero A a :=
  absurd (Eq.mp (congrArg (· = n) (matLeadingCol_eq_some hs)) h) (Nat.ne_of_lt c.isLt)
-- Reference: MRR 1988, Pt. II Ch. 6 (a row with leading column `n` is zero).
/-- If the leading column of row `a` is `n`, the row is zero. -/
theorem matRowZero_of_matLeadingCol_eq {A : FreeMatrix K m n} {a : Fin m}
    (h : matLeadingCol A a = n) : matRowZero A a := by
  cases hs : findPivotRow (fun c => if A a c ≠ 0 then true else false) n 0 with
  | none => exact matRowZero_of_matLeadingCol_eq_none hs
  | some c => exact matRowZero_of_matLeadingCol_eq_some hs h
-- Reference: MRR 1988, Pt. II Ch. 6 (columns left of the leading column are
-- zero).
-- Reference: MRR 1988, Pt. II Ch. 6 (columns left of the leading column are
-- zero); the `none` case.
/-- If the leading-column search of row `a` finds nothing, every entry is
zero. -/
theorem entry_eq_zero_of_lt_matLeadingCol_none {A : FreeMatrix K m n} {a : Fin m}
    {c : Fin n}
    (hs : findPivotRow (fun c => if A a c ≠ 0 then true else false) n 0 = none) :
    A a c = 0 :=
  eq_zero_of_pivotBool (findPivotRow_none_spec hs c (Nat.zero_le c.val)
    (Eq.subst (Nat.zero_add n).symm c.isLt))
-- Reference: MRR 1988, Pt. II Ch. 6 (columns left of the leading column are
-- zero); the `some` case.
/-- If the search finds `c'`, columns left of `c'.val` are zero. -/
theorem entry_eq_zero_of_lt_matLeadingCol_some {A : FreeMatrix K m n} {a : Fin m}
    {c : Fin n} {c' : Fin n}
    (hs : findPivotRow (fun c => if A a c ≠ 0 then true else false) n 0 = some c')
    (h : c.val < matLeadingCol A a) : A a c = 0 :=
  eq_zero_of_pivotBool (findPivotRow_some_first hs c (Nat.zero_le c.val)
    (Eq.mp (congrArg (c.val < ·) (matLeadingCol_eq_some hs)) h))
-- Reference: MRR 1988, Pt. II Ch. 6 (columns left of the leading column are
-- zero).
/-- Entries strictly left of the leading column of a row are zero. -/
theorem entry_eq_zero_of_lt_matLeadingCol {A : FreeMatrix K m n} {a : Fin m} {c : Fin n}
    (h : c.val < matLeadingCol A a) : A a c = 0 := by
  cases hs : findPivotRow (fun c => if A a c ≠ 0 then true else false) n 0 with
  | none => exact entry_eq_zero_of_lt_matLeadingCol_none hs
  | some c' => exact entry_eq_zero_of_lt_matLeadingCol_some hs h
-- Reference: MRR 1988, Pt. II Ch. 6 (leading column of the first row is the
-- minimum over all rows); successor-row case.
/-- The leading column of row `0` is at most that of any successor row. -/
theorem matLeadingCol_zero_le_succ {A : FreeMatrix K (k + 1) n} (hA : IsRref A) (j : Fin k) :
    matLeadingCol A 0 ≤ matLeadingCol A (Fin.succ j) := by
  rcases hA with ⟨_, _, h3, _⟩
  cases hs : findPivotRow (fun c => if A (Fin.succ j) c ≠ 0 then true else false) n 0 with
  | none => exact Eq.mpr (congrArg (matLeadingCol A 0 ≤ ·) (matLeadingCol_eq_none hs)) (matLeadingCol_le A 0)
  | some c =>
      have hnb : ¬ matRowZero A (Fin.succ j) := fun hz =>
        ne_zero_of_pivotBool (findPivotRow_some_spec hs).2.2 (hz c)
      have hlt : matLeadingCol A 0 < matLeadingCol A (Fin.succ j) :=
        h3 0 (Fin.succ j) (Fin.succ_pos j) hnb
      exact Eq.mpr (congrArg (matLeadingCol A 0 ≤ ·) (matLeadingCol_eq_some hs))
        (Nat.le_of_lt (Eq.mp (congrArg (matLeadingCol A 0 < ·) (matLeadingCol_eq_some hs)) hlt))
-- Reference: MRR 1988, Pt. II Ch. 6 (leading column of the first row is the
-- minimum over all rows).
-- Reference: MRR 1988, Pt. II Ch. 6 (leading column of the first row is the
-- minimum over all rows); the `b = 0` case.
/-- If `b = 0`, the inequality is reflexive. -/
theorem matLeadingCol_zero_le_zero {A : FreeMatrix K (k + 1) n} (b : Fin (k + 1))
    (hb : b = 0) : matLeadingCol A 0 ≤ matLeadingCol A b :=
  Eq.mpr (congrArg (fun z => matLeadingCol A 0 ≤ matLeadingCol A z) hb) (Nat.le_refl _)
-- Reference: MRR 1988, Pt. II Ch. 6 (leading column of the first row is the
-- minimum over all rows).
/-- The leading column of row `0` is the minimum of the leading columns. -/
theorem matLeadingCol_zero_le {A : FreeMatrix K (k + 1) n} (hA : IsRref A) (b : Fin (k + 1)) :
    matLeadingCol A 0 ≤ matLeadingCol A b := by
  rcases Fin.eq_zero_or_eq_succ b with hb | ⟨j, hb⟩
  · exact matLeadingCol_zero_le_zero b hb
  · exact Eq.mpr (congrArg (fun z => matLeadingCol A 0 ≤ z) (congrArg (matLeadingCol A) hb))
      (matLeadingCol_zero_le_succ hA j)
/-! ## Nonzero-row counting (the computed rank) -/
-- Reference: MRR 1988, Pt. II Ch. 6 (deciding whether a row is zero over a
-- discrete field is a finite search for a nonzero entry).
/-- A row is nonzero iff the pivot search in it finds a column; a `Bool`. -/
def matRowNonzeroBool (B : FreeMatrix K m n) (a : Fin m) : Bool :=
  (findPivotRow (fun c => if B a c ≠ 0 then true else false) n 0).isSome
-- Reference: MRR 1988, Pt. II Ch. 6 (soundness of the search).
-- Reference: MRR 1988, Pt. II Ch. 6 (soundness of the search); the `none` case.
/-- If the search of row `a` finds nothing, the row is zero, contradicting the
test. -/
theorem matRowNonzeroBool_true_none {B : FreeMatrix K m n} {a : Fin m}
    (hs : findPivotRow (fun c => if B a c ≠ 0 then true else false) n 0 = none)
    (h : ¬ matRowZero B a) : matRowNonzeroBool B a = true :=
  absurd (rowZero_of_findPivotRow_eq_none hs) h
-- Reference: MRR 1988, Pt. II Ch. 6 (soundness of the search); the `some` case.
/-- If the search of row `a` finds `c`, the test is `true`. -/
theorem matRowNonzeroBool_true_some {B : FreeMatrix K m n} {a : Fin m} {c : Fin n}
    (hs : findPivotRow (fun c => if B a c ≠ 0 then true else false) n 0 = some c) :
    matRowNonzeroBool B a = true :=
  (congrArg Option.isSome hs).trans (Option.isSome_some (a := c))
-- Reference: MRR 1988, Pt. II Ch. 6 (soundness of the search).
/-- The nonzero test says `true` iff the row is not zero. -/
theorem matRowNonzeroBool_true {B : FreeMatrix K m n} {a : Fin m} :
    matRowNonzeroBool B a = true ↔ ¬ matRowZero B a :=
  ⟨fun h hzero =>
      absurd ((congrArg Option.isSome (findPivotRow_eq_none_of_rowZero hzero)).symm.trans h)
        Bool.false_ne_true,
    fun h => by
      cases hs : findPivotRow (fun c => if B a c ≠ 0 then true else false) n 0 with
      | none => exact matRowNonzeroBool_true_none hs h
      | some c => exact matRowNonzeroBool_true_some hs⟩
-- Reference: MRR 1988, Pt. II Ch. 6 (completeness of the search).
/-- A zero row tests `false`. -/
theorem matRowNonzeroBool_false_of_rowZero {B : FreeMatrix K m n} {a : Fin m}
    (h : matRowZero B a) : matRowNonzeroBool B a = false := by
  unfold matRowNonzeroBool
  exact (congrArg Option.isSome (findPivotRow_eq_none_of_rowZero h)).trans Option.isSome_none
-- Reference: MRR 1988, Pt. II Ch. 6 (rows with equal entries test equally).
/-- The nonzero test is a congruence on the row entries. -/
theorem matRowNonzeroBool_congr {p q : ℕ} {A : FreeMatrix K p n} {B : FreeMatrix K q n}
    {a : Fin p} {b : Fin q}
    (h : ∀ c, A a c = B b c) :
    matRowNonzeroBool A a = matRowNonzeroBool B b := by
  unfold matRowNonzeroBool
  exact congrArg Option.isSome (findPivotRow_congr
    (fun c => congrArg (fun x => if x ≠ 0 then true else false) (h c)) n 0)
-- Reference: MRR 1988, Pt. II Ch. 6 (the rank is the number of nonzero rows
-- of the normal form; here the count over any matrix).
/-- The number of nonzero rows of `B`, computed by counting. -/
def nzCount (B : FreeMatrix K m n) : ℕ :=
  (List.finRange m).countP (fun a => matRowNonzeroBool B a)
-- Reference: MRR 1988, Pt. II Ch. 6 (dropping the last row of a `snoc`).
-- Reference: MRR 1988, Pt. II Ch. 6 (dropping the last row of a `snoc`); the
-- last row is zero.
/-- The last row of `matSnoc A 0` is the zero row. -/
theorem nzCount_snoc_zero_hz (A : FreeMatrix K m n) :
    matRowZero (matSnoc A 0) (Fin.last m) :=
  fun c => (matSnoc_last A 0 c).trans (Pi.zero_apply c)
-- Reference: MRR 1988, Pt. II Ch. 6 (dropping the last row of a `snoc`); the
-- last row tests `false`.
/-- The last row of `matSnoc A 0` tests `false`. -/
theorem nzCount_snoc_zero_hb (A : FreeMatrix K m n) :
    matRowNonzeroBool (matSnoc A 0) (Fin.last m) = false :=
  matRowNonzeroBool_false_of_rowZero (nzCount_snoc_zero_hz A)
-- Reference: MRR 1988, Pt. II Ch. 6 (dropping the last row of a `snoc`); the
-- count over the `castSucc` rows agrees.
/-- The nonzero-test predicate of `matSnoc A 0` composed with `castSucc` is
that of `A`. -/
theorem nzCount_snoc_zero_hcomp (A : FreeMatrix K m n) :
    (fun a => matRowNonzeroBool (matSnoc A 0) a) ∘ Fin.castSucc
      = fun a => matRowNonzeroBool A a :=
  funext (fun a => matRowNonzeroBool_congr (A := matSnoc A 0) (B := A)
    (a := Fin.castSucc a) (b := a) (fun c => matSnoc_castSucc A 0 a c))
-- Reference: MRR 1988, Pt. II Ch. 6 (dropping the last row of a `snoc`); the
-- singleton contributes zero.
/-- The singleton list `[Fin.last m]` contributes zero to the count. -/
theorem nzCount_snoc_zero_hlast (A : FreeMatrix K m n) :
    List.countP (fun a => matRowNonzeroBool (matSnoc A 0) a) [Fin.last m] = 0 :=
  (List.countP_cons_of_neg
    (fun h => Bool.false_ne_true ((nzCount_snoc_zero_hb A).symm.trans h))).trans
    List.countP_nil
-- Reference: MRR 1988, Pt. II Ch. 6 (dropping the last row of a `snoc`).
/-- Appending a zero row does not change the nonzero-row count. -/
theorem nzCount_snoc_zero (A : FreeMatrix K m n) : nzCount (matSnoc A 0) = nzCount A := by
  unfold nzCount
  exact ((congrArg (List.countP (fun a => matRowNonzeroBool (matSnoc A 0) a))
      List.finRange_succ_last).trans (List.countP_append (p := fun a => matRowNonzeroBool (matSnoc A 0) a)
        (l₁ := (List.finRange m).map Fin.castSucc) (l₂ := [Fin.last m]))).trans
    (((congrArg (· + List.countP (fun a => matRowNonzeroBool (matSnoc A 0) a) [Fin.last m])
        (List.countP_map (p := fun a => matRowNonzeroBool (matSnoc A 0) a) (f := Fin.castSucc)
          (l := List.finRange m))).trans
    ((congrArg (fun g => List.countP g (List.finRange m)
        + List.countP (fun a => matRowNonzeroBool (matSnoc A 0) a) [Fin.last m])
        (nzCount_snoc_zero_hcomp A)).trans
    ((congrArg (List.countP (fun a => matRowNonzeroBool A a) (List.finRange m) + ·)
        (nzCount_snoc_zero_hlast A)).trans
    (Nat.add_zero _)))))
-- Reference: MRR 1988, Pt. II Ch. 6 (the tail matrix: all rows but the first).
/-- The tail of a matrix: rows `1, ...` as a matrix with one row fewer. -/
def matTail (R : FreeMatrix K (k + 1) n) : FreeMatrix K k n := fun a => R (Fin.succ a)
-- Reference: definitional peel of `matTail`.
/-- Pointwise unfolding of `matTail`. -/
theorem matRowNonzeroBool_tail (R : FreeMatrix K (k + 1) n) (a : Fin k) :
    matRowNonzeroBool (matTail R) a = matRowNonzeroBool R (Fin.succ a) :=
  rfl
-- Reference: MRR 1988, Pt. II Ch. 6 (counting with the first row peeled off).
-- Reference: MRR 1988, Pt. II Ch. 6 (counting with the first row peeled off).
/-- If row `0` is nonzero, the count is one plus the count of the tail. -/
theorem nzCount_succ_eq (R : FreeMatrix K (k + 1) n) (h : ¬ matRowZero R 0) :
    nzCount R = nzCount (matTail R) + 1 := by
  unfold nzCount
  let hcomp : (fun a => matRowNonzeroBool R a) ∘ Fin.succ
      = fun a => matRowNonzeroBool (matTail R) a :=
    funext (fun a => (matRowNonzeroBool_tail R a).symm)
  let hb : matRowNonzeroBool R 0 = true := matRowNonzeroBool_true.mpr h
  let e1 := congrArg (List.countP (fun a => matRowNonzeroBool R a)) List.finRange_succ
  let e2 := List.countP_cons (p := fun a => matRowNonzeroBool R a) (a := 0)
    (l := (List.finRange k).map Fin.succ)
  let e3 := congrArg (· + if matRowNonzeroBool R 0 then 1 else 0)
    (List.countP_map (p := fun a => matRowNonzeroBool R a) (f := Fin.succ) (l := List.finRange k))
  let e4 := congrArg (fun g => List.countP g (List.finRange k)
      + if matRowNonzeroBool R 0 then 1 else 0) hcomp
  let e5 : (if matRowNonzeroBool R 0 then 1 else 0) = 1 := ite_eq_left hb
  exact ((e1.trans e2).trans e3).trans (e4.trans (congrArg _ e5))
-- Reference: MRR 1988, Pt. II Ch. 6 (zero rows sit at the bottom, so a zero
-- first row makes the whole matrix zero).
-- Reference: MRR 1988, Pt. II Ch. 6 (zero rows sit at the bottom); all rows are
-- zero if row `0` is.
/-- If row `0` of an RREF matrix is zero, every row is zero. -/
theorem nzCount_eq_zero_of_rowZero_zero_all {R : FreeMatrix K (k + 1) n} (hR : IsRref R)
    (hz : matRowZero R 0) : ∀ a : Fin (k + 1), matRowZero R a :=
  let ⟨h1, _, _, _⟩ := hR
  fun a =>
    match Fin.eq_zero_or_eq_succ a with
    | Or.inl h => Eq.mpr (congrArg (fun z => matRowZero R z) h) hz
    | Or.inr ⟨j, h⟩ => Eq.mpr (congrArg (fun z => matRowZero R z) h)
        (h1 0 (Fin.succ j) (Fin.succ_pos j) hz)
-- Reference: MRR 1988, Pt. II Ch. 6 (zero rows sit at the bottom, so a zero
-- first row makes the whole matrix zero).
/-- If row `0` is zero in an RREF matrix, all rows are zero and the count is
`0`. -/
theorem nzCount_eq_zero_of_rowZero_zero {R : FreeMatrix K (k + 1) n} (hR : IsRref R)
    (hz : matRowZero R 0) : nzCount R = 0 := by
  unfold nzCount
  exact list_countP_eq_zero (fun a _ =>
    Bool.eq_false_iff.mp
      (matRowNonzeroBool_false_of_rowZero (nzCount_eq_zero_of_rowZero_zero_all hR hz a)))
-- Reference: MRR 1988, Pt. II Ch. 6 (a nonzero first row contributes).
/-- If row `0` is nonzero, the count is positive. -/
theorem nzCount_pos_of_not_rowZero_zero {R : FreeMatrix K (k + 1) n} (h : ¬ matRowZero R 0) :
    0 < nzCount R := by
  unfold nzCount
  exact List.countP_pos_iff.mpr ⟨0, List.mem_finRange 0, matRowNonzeroBool_true.mpr h⟩
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
/-! ## RREF is preserved by tails and by appending a zero row -/
-- Reference: MRR 1988, Pt. II Ch. 6 (dropping the first row of an RREF matrix).
-- Reference: MRR 1988, Pt. II Ch. 6 (dropping the first row of an RREF matrix).
/-- The tail of an RREF matrix is in RREF. -/
theorem isRref_matTail {R : FreeMatrix K (k + 1) n} (hR : IsRref R) : IsRref (matTail R) :=
  let ⟨h1, h2, h3, h4⟩ := hR
  ⟨fun a b hab hza c => h1 (Fin.succ a) (Fin.succ b) (Fin.succ_lt_succ_iff.mpr hab) hza c,
   fun a c hlc => h2 (Fin.succ a) c hlc,
   fun a b hab hnb => h3 (Fin.succ a) (Fin.succ b) (Fin.succ_lt_succ_iff.mpr hab) hnb,
   fun a b hne c hlc => h4 (Fin.succ a) (Fin.succ b) (fun h => hne (Fin.succ_inj.mp h)) c hlc⟩
-- Reference: MRR 1988, Pt. II Ch. 6 (appending a zero row at the bottom of an
-- RREF matrix keeps it in RREF: zero rows sit at the bottom).
-- Reference: MRR 1988, Pt. II Ch. 6 (appending a zero row); the last row of
-- `matSnoc R 0` is zero.
/-- The last row of `matSnoc R 0` is the zero row. -/
theorem isRref_snoc_zero_last {R : FreeMatrix K m n} (hR : IsRref R) :
    matRowZero (matSnoc R 0) (Fin.last m) :=
  fun c => (matSnoc_last R 0 c).trans (Pi.zero_apply c)
-- Reference: MRR 1988, Pt. II Ch. 6 (appending a zero row); leading column of
-- the zero last row.
/-- The leading column of the zero last row of `matSnoc R 0` is `n`. -/
theorem isRref_snoc_zero_hlc_last {R : FreeMatrix K m n}
    (hz : matRowZero (matSnoc R 0) (Fin.last m)) :
    matLeadingCol (matSnoc R 0) (Fin.last m) = n :=
  matLeadingCol_eq_of_rowZero _ _ hz
-- Reference: MRR 1988, Pt. II Ch. 6 (appending a zero row); leading columns of
-- the old rows are unchanged.
/-- The leading column of a `castSucc` row of `matSnoc R 0` is that of `R`. -/
theorem isRref_snoc_zero_hlc_cast {R : FreeMatrix K m n} (a : Fin m) :
    matLeadingCol (matSnoc R 0) (Fin.castSucc a) = matLeadingCol R a :=
  matLeadingCol_congr (A := matSnoc R 0) (B := R) (a := Fin.castSucc a) (b := a)
    (fun c => matSnoc_castSucc R 0 a c)
-- Reference: MRR 1988, Pt. II Ch. 6 (appending a zero row); zero-row test of
-- the old rows is unchanged.
/-- Zero-rowedness of a `castSucc` row of `matSnoc R 0` matches `R`. -/
theorem isRref_snoc_zero_hz_cast {R : FreeMatrix K m n} (a : Fin m) :
    matRowZero (matSnoc R 0) (Fin.castSucc a) ↔ matRowZero R a :=
  ⟨fun h c => Eq.mp (congrArg (fun z => z = 0) (matSnoc_castSucc R 0 a c)) (h c),
    fun h c => Eq.mpr (congrArg (fun z => z = 0) (matSnoc_castSucc R 0 a c)) (h c)⟩
-- Reference: MRR 1988, Pt. II Ch. 6 (appending a zero row); clause 1: zero rows
-- sit at the bottom.
/-- Clause 1 of RREF for `matSnoc R 0`: zero rows sit at the bottom. -/
theorem isRref_snoc_zero_c1 {R : FreeMatrix K m n}
    (h1 : ∀ a b : Fin m, a < b → matRowZero R a → matRowZero R b)
    (hz_cast : ∀ a : Fin m, matRowZero (matSnoc R 0) (Fin.castSucc a) ↔ matRowZero R a)
    (hlc_cast : ∀ a : Fin m, matLeadingCol (matSnoc R 0) (Fin.castSucc a) = matLeadingCol R a)
    (hz : matRowZero (matSnoc R 0) (Fin.last m)) :
    ∀ a b : Fin (m + 1), a < b → matRowZero (matSnoc R 0) a →
      ∀ c : Fin n, matSnoc R 0 b c = 0 := by
  intro a b hab hza c
  rcases Fin.eq_castSucc_or_eq_last b with ⟨b', hb⟩ | hb
  · rcases Fin.eq_castSucc_or_eq_last a with ⟨a', ha⟩ | ha
    · have hab' : a' < b' := Fin.castSucc_lt_castSucc_iff.mp
        (Eq.mp (congrArg (Fin.castSucc a' < ·) hb) (Eq.mp (congrArg (· < b) ha) hab))
      exact ((congrArg (fun z => matSnoc R 0 z c) hb).trans (matSnoc_castSucc R 0 b' c)).trans
        (h1 a' b' hab' ((hz_cast a').mp
          (Eq.mp (congrArg (fun z => matRowZero (matSnoc R 0) z) ha) hza)) c)
    · exact absurd (Eq.mp (congrArg (Fin.last m < ·) hb) (Eq.mp (congrArg (· < b) ha) hab))
        (Fin.not_lt.mpr (Fin.le_of_lt (Fin.castSucc_lt_last b')))
  · exact Eq.mpr (congrArg (fun z => matSnoc R 0 z c = 0) hb) (hz c)
-- Reference: MRR 1988, Pt. II Ch. 6 (appending a zero row); clause 2: pivot
-- entries are `1`.
/-- Clause 2 of RREF for `matSnoc R 0`: pivot entries are `1`. -/
theorem isRref_snoc_zero_c2 {R : FreeMatrix K m n}
    (h2 : ∀ a : Fin m, ∀ c : Fin n, matLeadingCol R a = c.val → R a c = 1)
    (hlc_cast : ∀ a : Fin m, matLeadingCol (matSnoc R 0) (Fin.castSucc a) = matLeadingCol R a)
    (hlc_last : matLeadingCol (matSnoc R 0) (Fin.last m) = n) :
    ∀ a : Fin (m + 1), ∀ c : Fin n, matLeadingCol (matSnoc R 0) a = c.val →
      matSnoc R 0 a c = 1 := by
  intro a c hlc
  rcases Fin.eq_castSucc_or_eq_last a with ⟨a', ha⟩ | ha
  · have hlc' : matLeadingCol R a' = c.val :=
      Eq.mp (congrArg (fun z => z = c.val) (hlc_cast a'))
        (Eq.mp (congrArg (fun z => matLeadingCol (matSnoc R 0) z = c.val) ha) hlc)
    exact (Eq.mpr (congrArg (fun z => matSnoc R 0 z c = R a' c) ha) (matSnoc_castSucc R 0 a' c)).trans
      (h2 a' c hlc')
  · exact absurd c.isLt (Nat.not_lt.mpr (Nat.le_of_eq
      (Eq.mp (congrArg (· = c.val) hlc_last)
        (Eq.mp (congrArg (fun z => matLeadingCol (matSnoc R 0) z = c.val) ha) hlc))))
-- Reference: MRR 1988, Pt. II Ch. 6 (appending a zero row); clause 3: leading
-- columns strictly increase.
/-- Clause 3 of RREF for `matSnoc R 0`: leading columns strictly increase. -/
theorem isRref_snoc_zero_c3 {R : FreeMatrix K m n}
    (h3 : ∀ a b : Fin m, a < b → ¬ matRowZero R b → matLeadingCol R a < matLeadingCol R b)
    (hlc_cast : ∀ a : Fin m, matLeadingCol (matSnoc R 0) (Fin.castSucc a) = matLeadingCol R a)
    (hz : matRowZero (matSnoc R 0) (Fin.last m))
    (hz_cast : ∀ a : Fin m, matRowZero (matSnoc R 0) (Fin.castSucc a) ↔ matRowZero R a) :
    ∀ a b : Fin (m + 1), a < b → ¬ matRowZero (matSnoc R 0) b →
      matLeadingCol (matSnoc R 0) a < matLeadingCol (matSnoc R 0) b := by
  intro a b hab hnb
  rcases Fin.eq_castSucc_or_eq_last b with ⟨b', hb⟩ | hb
  · rcases Fin.eq_castSucc_or_eq_last a with ⟨a', ha⟩ | ha
    · have hab' : a' < b' := Fin.castSucc_lt_castSucc_iff.mp
        (Eq.mp (congrArg (Fin.castSucc a' < ·) hb) (Eq.mp (congrArg (· < b) ha) hab))
      have hnb' : ¬ matRowZero R b' := mt (hz_cast b').mpr
        (Eq.mp (congrArg (fun z => ¬ matRowZero (matSnoc R 0) z) hb) hnb)
      have eq := congrArg₂ (· < ·)
        ((congrArg (fun z => matLeadingCol (matSnoc R 0) z) ha).trans (hlc_cast a'))
        ((congrArg (fun z => matLeadingCol (matSnoc R 0) z) hb).trans (hlc_cast b'))
      exact Eq.mpr eq (h3 a' b' hab' hnb')
    · exact absurd (Eq.mp (congrArg (Fin.last m < ·) hb) (Eq.mp (congrArg (· < b) ha) hab))
        (Fin.not_lt.mpr (Fin.le_of_lt (Fin.castSucc_lt_last b')))
  · exact absurd hz (Eq.mp (congrArg (fun z => ¬ matRowZero (matSnoc R 0) z) hb) hnb)
-- Reference: MRR 1988, Pt. II Ch. 6 (appending a zero row); clause 4: pivot
-- columns are zero in every other row.
/-- Clause 4 of RREF for `matSnoc R 0`: pivot columns vanish off-pivot. -/
theorem isRref_snoc_zero_c4 {R : FreeMatrix K m n}
    (h4 : ∀ a b : Fin m, a ≠ b → ∀ c : Fin n, matLeadingCol R a = c.val → R b c = 0)
    (hlc_cast : ∀ a : Fin m, matLeadingCol (matSnoc R 0) (Fin.castSucc a) = matLeadingCol R a)
    (hlc_last : matLeadingCol (matSnoc R 0) (Fin.last m) = n) :
    ∀ a b : Fin (m + 1), a ≠ b → ∀ c : Fin n, matLeadingCol (matSnoc R 0) a = c.val →
      matSnoc R 0 b c = 0 := by
  intro a b hne c hlc
  rcases Fin.eq_castSucc_or_eq_last a with ⟨a', ha⟩ | ha
  · have hlc' : matLeadingCol R a' = c.val :=
      Eq.mp (congrArg (fun z => z = c.val) (hlc_cast a'))
        (Eq.mp (congrArg (fun z => matLeadingCol (matSnoc R 0) z = c.val) ha) hlc)
    rcases Fin.eq_castSucc_or_eq_last b with ⟨b', hb⟩ | hb
    · have hne' : a' ≠ b' := fun h => hne (ha.trans ((congrArg Fin.castSucc h).trans hb.symm))
      exact (Eq.mpr (congrArg (fun z => matSnoc R 0 z c = R b' c) hb) (matSnoc_castSucc R 0 b' c)).trans
        (h4 a' b' hne' c hlc')
    · exact Eq.mpr (congrArg (fun z => matSnoc R 0 z c = 0) hb)
        ((matSnoc_last R 0 c).trans (Pi.zero_apply c))
  · exact absurd c.isLt (Nat.not_lt.mpr (Nat.le_of_eq
      (Eq.mp (congrArg (· = c.val) hlc_last)
        (Eq.mp (congrArg (fun z => matLeadingCol (matSnoc R 0) z = c.val) ha) hlc))))
-- Reference: MRR 1988, Pt. II Ch. 6 (appending a zero row at the bottom of an
-- RREF matrix keeps it in RREF: zero rows sit at the bottom).
-- Reference: MRR 1988, Pt. II Ch. 6 (appending a zero row at the bottom of an
-- RREF matrix keeps it in RREF: zero rows sit at the bottom).
/-- Appending a zero row to an RREF matrix keeps it in RREF. -/
theorem isRref_snoc_zero {R : FreeMatrix K m n} (hR : IsRref R) :
    IsRref (matSnoc R 0) :=
  let ⟨h1, h2, h3, h4⟩ := hR
  let hz := isRref_snoc_zero_last hR
  let hlc_last := isRref_snoc_zero_hlc_last hz
  let hlc_cast := isRref_snoc_zero_hlc_cast (R := R)
  let hz_cast := isRref_snoc_zero_hz_cast (R := R)
  ⟨isRref_snoc_zero_c1 h1 hz_cast hlc_cast hz,
   isRref_snoc_zero_c2 h2 hlc_cast hlc_last,
   isRref_snoc_zero_c3 h3 hlc_cast hz hz_cast,
   isRref_snoc_zero_c4 h4 hlc_cast hlc_last⟩
/-! ## Leading column of a vector and the residual criterion -/
-- Reference: MRR 1988, Pt. II Ch. 6 (the leading column of a vector: the
-- first nonzero coordinate).
/-- The leading (first nonzero) column of a vector; `n` if the vector is
zero. -/
def vecLeadingCol (w : FreeMod K n) : ℕ :=
  match findPivotRow (fun c => if w c ≠ 0 then true else false) n 0 with
  | some c => c.val
  | none => n
-- Reference: definitional peel of `vecLeadingCol` at a `some` search result.
/-- If the search of `w` finds column `c`, the leading column is `c.val`. -/
theorem vecLeadingCol_eq_some {w : FreeMod K n} {c : Fin n}
    (h : findPivotRow (fun c => if w c ≠ 0 then true else false) n 0 = some c) :
    vecLeadingCol w = c.val := by
  unfold vecLeadingCol
  exact congrArg (fun o => match o with | some c => c.val | none => n) h
-- Reference: definitional peel of `vecLeadingCol` at a `none` search result.
/-- If the search of `w` finds nothing, the leading column is `n`. -/
theorem vecLeadingCol_eq_none {w : FreeMod K n}
    (h : findPivotRow (fun c => if w c ≠ 0 then true else false) n 0 = none) :
    vecLeadingCol w = n := by
  unfold vecLeadingCol
  exact congrArg (fun o => match o with | some c => c.val | none => n) h
-- Reference: MRR 1988, Pt. II Ch. 6 (a vector vanishing before column `j < n`
-- and nonzero at `j` has leading column `j`).
/-- A vector vanishing before `j < n` and nonzero at `j` has leading column
`j`. -/
theorem vecLeadingCol_eq_of_zero_before {w : FreeMod K n} {j : ℕ} (hj : j < n)
    (hzero : ∀ c : Fin n, c.val < j → w c = 0) (hne : w ⟨j, hj⟩ ≠ 0) :
    vecLeadingCol w = j :=
  (vecLeadingCol_eq_some (findPivotRow_eq_some_of_first (Nat.zero_le j)
    (Eq.subst (Nat.zero_add n).symm hj) (pivotBool_true hne)
    (fun i' _ hi' => pivotBool_false (hzero i' hi')))).trans (Fin.val_mk hj)
-- Reference: MRR 1988, Pt. II Ch. 6 (a nonzero vector has a leading column
-- inside the range).
-- Reference: MRR 1988, Pt. II Ch. 6 (a nonzero vector has a leading column
-- inside the range); the `none` case.
/-- If the search of `w` finds nothing, `w` is zero, contradicting `w ≠ 0`. -/
theorem vecLeadingCol_lt_none {w : FreeMod K n} (hw : w ≠ 0)
    (hs : findPivotRow (fun c => if w c ≠ 0 then true else false) n 0 = none) :
    vecLeadingCol w < n :=
  absurd (funext (fun c => eq_zero_of_pivotBool
    (findPivotRow_none_spec hs c (Nat.zero_le c.val)
      (Eq.subst (Nat.zero_add n).symm c.isLt)))) hw
-- Reference: MRR 1988, Pt. II Ch. 6 (a nonzero vector has a leading column
-- inside the range); the `some` case.
/-- If the search of `w` finds `c`, the leading column is `c.val < n`. -/
theorem vecLeadingCol_lt_some {w : FreeMod K n} {c : Fin n}
    (hs : findPivotRow (fun c => if w c ≠ 0 then true else false) n 0 = some c) :
    vecLeadingCol w < n :=
  Eq.mpr (congrArg (· < n) (vecLeadingCol_eq_some hs)) c.isLt
-- Reference: MRR 1988, Pt. II Ch. 6 (a nonzero vector has a leading column
-- inside the range).
/-- A nonzero vector has leading column `< n`. -/
theorem vecLeadingCol_lt {w : FreeMod K n} (hw : w ≠ 0) : vecLeadingCol w < n := by
  cases hs : findPivotRow (fun c => if w c ≠ 0 then true else false) n 0 with
  | none => exact vecLeadingCol_lt_none hw hs
  | some c => exact vecLeadingCol_lt_some hs
-- Reference: MRR 1988, Pt. II Ch. 6 (the entry at the leading column is
-- nonzero).
-- Reference: MRR 1988, Pt. II Ch. 6 (the entry at the leading column is
-- nonzero); the `none` case.
/-- If the search of `w` finds nothing, `w` is zero, contradicting `w ≠ 0`. -/
theorem vecLeadingCol_ne_zero_none {w : FreeMod K n} (hw : w ≠ 0)
    (hs : findPivotRow (fun c => if w c ≠ 0 then true else false) n 0 = none) :
    w ⟨vecLeadingCol w, vecLeadingCol_lt hw⟩ ≠ 0 :=
  absurd (funext (fun c => eq_zero_of_pivotBool
    (findPivotRow_none_spec hs c (Nat.zero_le c.val)
      (Eq.subst (Nat.zero_add n).symm c.isLt)))) hw
-- Reference: MRR 1988, Pt. II Ch. 6 (the entry at the leading column is
-- nonzero); the `some` case.
/-- If the search of `w` finds `c`, the leading column is `c.val` and `w c ≠ 0`. -/
theorem vecLeadingCol_ne_zero_some {w : FreeMod K n} (hw : w ≠ 0) {c : Fin n}
    (hs : findPivotRow (fun c => if w c ≠ 0 then true else false) n 0 = some c) :
    w ⟨vecLeadingCol w, vecLeadingCol_lt hw⟩ ≠ 0 :=
  let hlt := vecLeadingCol_lt hw
  let hne : w c ≠ 0 := ne_zero_of_pivotBool (findPivotRow_some_spec hs).2.2
  let heq : (⟨vecLeadingCol w, hlt⟩ : Fin n) = c :=
    Fin.eq_of_val_eq (vecLeadingCol_eq_some hs)
  Eq.mpr (congrArg (fun z => w z ≠ 0) heq) hne
-- Reference: MRR 1988, Pt. II Ch. 6 (the entry at the leading column is
-- nonzero).
/-- A nonzero vector is nonzero at its leading column. -/
theorem vecLeadingCol_ne_zero {w : FreeMod K n} (hw : w ≠ 0) :
    w ⟨vecLeadingCol w, vecLeadingCol_lt hw⟩ ≠ 0 := by
  cases hs : findPivotRow (fun c => if w c ≠ 0 then true else false) n 0 with
  | none => exact vecLeadingCol_ne_zero_none hw hs
  | some c => exact vecLeadingCol_ne_zero_some hw hs
-- Reference: MRR 1988, Pt. II Ch. 6 (columns left of the leading column of a
-- vector are zero).
-- Reference: MRR 1988, Pt. II Ch. 6 (columns left of the leading column of a
-- vector are zero); the `none` case.
/-- If the search of `w` finds nothing, every entry is zero. -/
theorem vecLeadingCol_vanish_before_none {w : FreeMod K n} {c : Fin n}
    (hs : findPivotRow (fun c => if w c ≠ 0 then true else false) n 0 = none) :
    w c = 0 :=
  eq_zero_of_pivotBool (findPivotRow_none_spec hs c (Nat.zero_le c.val)
    (Eq.subst (Nat.zero_add n).symm c.isLt))
-- Reference: MRR 1988, Pt. II Ch. 6 (columns left of the leading column of a
-- vector are zero); the `some` case.
/-- If the search of `w` finds `c'`, columns left of `c'.val` are zero. -/
theorem vecLeadingCol_vanish_before_some {w : FreeMod K n} {c c' : Fin n}
    (hs : findPivotRow (fun c => if w c ≠ 0 then true else false) n 0 = some c')
    (h : c.val < vecLeadingCol w) : w c = 0 :=
  eq_zero_of_pivotBool (findPivotRow_some_first hs c (Nat.zero_le c.val)
    (Eq.mp (congrArg (c.val < ·) (vecLeadingCol_eq_some hs)) h))
-- Reference: MRR 1988, Pt. II Ch. 6 (columns left of the leading column of a
-- vector are zero).
/-- A vector vanishes strictly left of its leading column. -/
theorem vecLeadingCol_vanish_before {w : FreeMod K n} {c : Fin n}
    (h : c.val < vecLeadingCol w) : w c = 0 := by
  cases hs : findPivotRow (fun c => if w c ≠ 0 then true else false) n 0 with
  | none => exact vecLeadingCol_vanish_before_none hs
  | some c' => exact vecLeadingCol_vanish_before_some hs h
-- Reference: MRR 1988, Pt. II Ch. 6 (a nonzero vector vanishing up to column
-- `j` has leading column strictly right of `j`).
/-- If `w ≠ 0` vanishes at all columns `≤ j`, then `j < vecLeadingCol w`. -/
theorem vecLeadingCol_lt_of_vanish {w : FreeMod K n} {j : ℕ} (hw : w ≠ 0)
    (hvan : ∀ c : Fin n, c.val ≤ j → w c = 0) : j < vecLeadingCol w := by
  rcases Nat.lt_or_ge j (vecLeadingCol w) with h | h
  · exact h
  · have hlt := vecLeadingCol_lt hw
    have hne := vecLeadingCol_ne_zero hw
    exact absurd (hvan ⟨vecLeadingCol w, hlt⟩ h) hne
-- Reference: MRR 1988, Pt. II Ch. 6 (evaluating a combination at a pivot
-- column reads off one coefficient).
/-- At the pivot column of row `b` of an RREF matrix, the combination
`∑ a ∈ finFinset _, d a * R a` equals `d b`. -/
theorem rref_sum_at_pivot {R : FreeMatrix K m n} (hR : IsRref R) {d : Fin m → K} {b : Fin m}
    {c : Fin n} (hlc : matLeadingCol R b = c.val) :
    (∑ a ∈ finFinset _, d a * R a c) = d b :=
  let ⟨_, h2, _, h4⟩ := hR
  let h1 : R b c = 1 := h2 b c hlc
  (sum_finFinset_eq_single (f := fun a => d a * R a c)
    (fun a hab => (congrArg (d a * ·) (h4 b a hab.symm c hlc)).trans (mul_zero _))).trans
    ((congrArg (d b * ·) h1).trans (mul_one _))
-- Reference: MRR 1988, Pt. II Ch. 6 (the coefficient of a combination at a
-- pivot row, read as data).
/-- The coefficient of row `a` in a combination, read at a pivot row. -/
def rrefCoeff (R : FreeMatrix K m n) (v : FreeMod K n) (a : Fin m) : K :=
  if h : matLeadingCol R a < n then v ⟨matLeadingCol R a, h⟩ else 0
-- Reference: MRR 1988, Pt. II Ch. 6 (the residual of `v` against the pivot
-- rows of an RREF matrix `R`).
/-- The residual of `v` against the pivot rows of `R`: at each column,
subtract the pivot-row coefficients times the rows. -/
def rrefResidual (R : FreeMatrix K m n) (v : FreeMod K n) : FreeMod K n :=
  fun c => v c - ∑ a ∈ finFinset _, rrefCoeff R v a * R a c
-- Reference: MRR 1988, Pt. II Ch. 6 (reading the coefficient of a combination
-- at the pivot column of row `a` as the residual coefficient).
/-- The span witness coefficient `d a` equals the residual coefficient
`rrefCoeff R v a` whenever row `a` has a pivot. -/
theorem rrefCoeff_eq_of_lt {R : FreeMatrix K m n} (hR : IsRref R) {v : FreeMod K n}
    {d : Fin m → K} (hd : ∀ j : Fin n, v j = ∑ a ∈ finFinset _, d a * R a j)
    (a : Fin m) (ha : matLeadingCol R a < n) : d a = rrefCoeff R v a := by
  unfold rrefCoeff
  exact Eq.mpr (congrArg (fun z => d a = z) (dite_eq_left ha))
    (((hd _).trans (rref_sum_at_pivot (d := d) hR (b := a)
      (c := ⟨matLeadingCol R a, ha⟩) (Fin.val_mk ha).symm)).symm)
-- Reference: MRR 1988, Pt. II Ch. 6 (the residual coefficient sum equals the
-- witness sum at every column).
/-- The sum of `rrefCoeff` times the rows equals the sum of `d` times the rows. -/
theorem inRowSpan_rref_iff_sum {R : FreeMatrix K m n} (hR : IsRref R) {v : FreeMod K n}
    {d : Fin m → K} (hd : ∀ j : Fin n, v j = ∑ a ∈ finFinset _, d a * R a j) (c : Fin n) :
    (∑ a ∈ finFinset _, rrefCoeff R v a * R a c) = ∑ a ∈ finFinset _, d a * R a c :=
  sum_finFinset_congr (fun a => by
    rcases Nat.lt_or_ge (matLeadingCol R a) n with hlt | hge
    · exact congrArg (· * R a c) (rrefCoeff_eq_of_lt hR hd a hlt).symm
    · have hn : matLeadingCol R a = n := Nat.le_antisymm (matLeadingCol_le R a) hge
      have hz : matRowZero R a := matRowZero_of_matLeadingCol_eq hn
      have h0 : (0 : K) * R a c = d a * R a c :=
        (zero_mul (R a c)).trans ((congrArg (d a * ·) (hz c)).trans (mul_zero _)).symm
      unfold rrefCoeff
      exact Eq.mpr (congrArg (fun z => z * R a c = d a * R a c)
        (dite_eq_right (Nat.not_lt.mpr hge))) h0)
-- Reference: MRR 1988, Pt. II Ch. 6 (membership in the row span of an RREF
-- matrix iff the residual against the pivot rows vanishes; the forward
-- direction evaluates the combination at each pivot column).
-- Reference: MRR 1988, Pt. II Ch. 6 (membership iff residual vanishes); the
-- forward step at a column.
/-- If `v` is a combination with coefficients `d`, the residual at `c` is
zero. -/
theorem inRowSpan_rref_iff_fwd {R : FreeMatrix K m n} (hR : IsRref R) {v : FreeMod K n}
    {d : Fin m → K} (hd : ∀ j : Fin n, v j = ∑ a ∈ finFinset _, d a * R a j) (c : Fin n) :
    rrefResidual R v c = 0 :=
  let e1 : v c = ∑ a ∈ finFinset _, d a * R a c := hd c
  let hsum2 := inRowSpan_rref_iff_sum hR hd c
  (congrArg (v c - ·) hsum2).trans
    (Eq.mpr (congrArg (fun z => z - ∑ a ∈ finFinset _, d a * R a c = 0) e1) (sub_self _))
-- Reference: MRR 1988, Pt. II Ch. 6 (membership in the row span of an RREF
-- matrix iff the residual against the pivot rows vanishes; the forward
-- direction evaluates the combination at each pivot column).
/-- `v` lies in the row span of the RREF matrix `R` iff its residual against
the pivot rows of `R` vanishes. -/
theorem inRowSpan_rref_iff {R : FreeMatrix K m n} (hR : IsRref R) (v : FreeMod K n) :
    inRowSpan R v ↔ ∀ c : Fin n, rrefResidual R v c = 0 :=
  ⟨fun h => by
      let ⟨d, hd⟩ := h
      intro c
      exact inRowSpan_rref_iff_fwd hR hd c,
    fun h => ⟨rrefCoeff R v, fun c => by
      have hc := h c
      unfold rrefResidual at hc
      exact sub_eq_zero.mp hc⟩⟩
-- Reference: MRR 1988, Pt. II Ch. 6 (reading the `≠ 0` test off a `false`
-- conjunction disjunct).
-- Reference: MRR 1988, Pt. II Ch. 6 (reading the `≠ 0` test off a `false`
-- conjunction disjunct); the `x = 0` step.
/-- If the `≠ 0` test is `false`, then `x = 0`. -/
theorem mul_eq_zero_of_and_false_x {x : K}
    (h1 : (if x ≠ 0 then true else false) = false) : x = 0 := by
  cases (inferInstance : Decidable (x ≠ 0)) with
  | isTrue hne =>
      have ht : (if x ≠ 0 then true else false) = true := ite_eq_left hne
      exact absurd (Eq.mp (congrArg (· = false) ht) h1) Bool.false_ne_true.symm
  | isFalse hnne =>
      cases (inferInstance : Decidable (x = 0)) with
      | isTrue h0 => exact h0
      | isFalse h2' => exact absurd (fun heq => h2' heq) hnne
-- Reference: MRR 1988, Pt. II Ch. 6 (reading the `≠ 0` test off a `false`
-- conjunction disjunct); the row-zero step.
/-- If the row-nonzero test is `false`, the row is zero. -/
theorem mul_eq_zero_of_and_false_row {B : FreeMatrix K m n} {a : Fin m}
    (h2 : matRowNonzeroBool B a = false) : matRowZero B a := by
  cases hs : findPivotRow (fun c => if B a c ≠ 0 then true else false) n 0 with
  | none => exact rowZero_of_findPivotRow_eq_none hs
  | some c =>
      have h2' : (some c).isSome = false :=
        (congrArg Option.isSome hs).symm.trans
          (h2 : (findPivotRow (fun c => if B a c ≠ 0 then true else false) n 0).isSome = false)
      exact absurd h2' (fun h => Bool.false_ne_true (h.symm.trans (Option.isSome_some (a := c))))
-- Reference: MRR 1988, Pt. II Ch. 6 (reading the `≠ 0` test off a `false`
-- conjunction disjunct).
/-- If the conjunction `(x ≠ 0 test) && (row nonzero test)` is `false`, then
`x * B a c = 0`. -/
theorem mul_eq_zero_of_and_false {x : K} {B : FreeMatrix K m n} {a : Fin m}
    (h : ((if x ≠ 0 then true else false) && matRowNonzeroBool B a) = false) (c : Fin n) :
    x * B a c = 0 :=
  match Bool.and_eq_false_iff.mp h with
  | Or.inl h1 =>
      let hx := mul_eq_zero_of_and_false_x h1
      (congrArg (· * B a c) hx).trans (zero_mul (B a c))
  | Or.inr h2 =>
      let hz := mul_eq_zero_of_and_false_row h2
      (congrArg (x * ·) (hz c)).trans (mul_zero x)
-- Reference: MRR 1988, Pt. II Ch. 6 (the leading column of a nonzero element
-- of the row span of an RREF matrix is a pivot column); vanishing step.
/-- Left of the pivot column of the first nonzero row of the combination, the
combination vanishes. -/
theorem exists_matLeadingCol_eq_vecLeadingCol_vanish {R : FreeMatrix K m n} (hR : IsRref R)
    {w : FreeMod K n} {d : Fin m → K}
    (hd : ∀ j : Fin n, w j = ∑ a ∈ finFinset _, d a * R a j)
    {ast : Fin m}
    (hs : findPivotRow (fun a => (if d a ≠ 0 then true else false) && matRowNonzeroBool R a)
      m 0 = some ast)
    (c : Fin n) (hc : c.val < matLeadingCol R ast) :
    w c = 0 := by
  let ⟨_, _, hR3, _⟩ := hR
  have e : w c = ∑ a ∈ finFinset _, d a * R a c := hd c
  refine Eq.mp (congrArg (fun z => z = 0) e.symm) (sum_finFinset_eq_zero (fun a => ?_))
  rcases Nat.lt_or_ge a.val ast.val with hlt | hge
  · exact mul_eq_zero_of_and_false (findPivotRow_some_first hs a (Nat.zero_le a.val) hlt) c
  · rcases Nat.lt_or_ge ast.val a.val with hlt2 | hge2
    · cases hs3 : findPivotRow (fun c => if R a c ≠ 0 then true else false) n 0 with
      | none =>
          exact (congrArg (d a * ·) (rowZero_of_findPivotRow_eq_none hs3 c)).trans (mul_zero (d a))
      | some c3 =>
          have hnb : ¬ matRowZero R a := fun hz =>
            ne_zero_of_pivotBool (findPivotRow_some_spec hs3).2.2 (hz c3)
          have hlt3 : matLeadingCol R ast < matLeadingCol R a :=
            hR3 ast a (Fin.lt_def.mpr hlt2) hnb
          exact (congrArg (d a * ·) (entry_eq_zero_of_lt_matLeadingCol (Nat.lt_trans hc hlt3))).trans
            (mul_zero (d a))
    · have heq : a = ast := Fin.eq_of_val_eq (Nat.le_antisymm hge2 hge)
      exact Eq.mpr (congrArg (fun z => d z * R z c = 0) heq)
        ((congrArg (d ast * ·) (entry_eq_zero_of_lt_matLeadingCol hc)).trans (mul_zero (d ast)))
-- Reference: MRR 1988, Pt. II Ch. 6 (the leading column of a nonzero element
-- of the row span of an RREF matrix is a pivot column); nonzero step.
/-- At the pivot column of the first nonzero row of the combination, the
combination is nonzero. -/
theorem exists_matLeadingCol_eq_vecLeadingCol_ne {R : FreeMatrix K m n} (hR : IsRref R)
    {w : FreeMod K n} {d : Fin m → K}
    (hd : ∀ j : Fin n, w j = ∑ a ∈ finFinset _, d a * R a j)
    {ast : Fin m}
    (hs : findPivotRow (fun a => (if d a ≠ 0 then true else false) && matRowNonzeroBool R a)
      m 0 = some ast)
    (hlc_lt : matLeadingCol R ast < n) :
    w ⟨matLeadingCol R ast, hlc_lt⟩ ≠ 0 := by
  have hspec := findPivotRow_some_spec hs
  rcases Bool.and_eq_true_iff.mp hspec.2.2 with ⟨hdne, hrow⟩
  have e2 := rref_sum_at_pivot (d := d) hR (b := ast) (c := ⟨matLeadingCol R ast, hlc_lt⟩)
    (Fin.val_mk hlc_lt).symm
  have e : w ⟨matLeadingCol R ast, hlc_lt⟩ = d ast := (hd _).trans e2
  exact fun h => ne_zero_of_pivotBool hdne (Eq.mpr (congrArg (· = 0) e.symm) h)
-- Reference: MRR 1988, Pt. II Ch. 6 (the leading column of a nonzero element
-- of the row span of an RREF matrix is a pivot column: take the first row
-- with a nonzero coefficient).
-- Reference: MRR 1988, Pt. II Ch. 6 (the leading column of a nonzero element
-- of the row span is a pivot column); the no-pivot case.
/-- If the combined search finds no row, the combination is zero,
contradicting `w ≠ 0`. -/
theorem exists_matLeadingCol_eq_vecLeadingCol_none {R : FreeMatrix K m n}
    {w : FreeMod K n} {d : Fin m → K} (hd : ∀ j : Fin n, w j = ∑ a ∈ finFinset _, d a * R a j)
    (hw0 : w ≠ 0)
    (hs : findPivotRow (fun a => (if d a ≠ 0 then true else false) && matRowNonzeroBool R a)
      m 0 = none) : ∃ b : Fin m, ¬ matRowZero R b ∧ matLeadingCol R b = vecLeadingCol w :=
  let hzero : ∀ a : Fin m, ∀ c : Fin n, d a * R a c = 0 := fun a c =>
    mul_eq_zero_of_and_false
      (findPivotRow_none_spec hs a (Nat.zero_le a.val)
        (Eq.subst (Nat.zero_add m).symm a.isLt)) c
  absurd (funext (fun c => (hd c).trans (sum_finFinset_eq_zero (fun a => hzero a c)))) hw0
-- Reference: MRR 1988, Pt. II Ch. 6 (the leading column of a nonzero element
-- of the row span is a pivot column); the leading column of a nonzero row.
/-- The leading column of a nonzero row `ast` of `R` is `< n`. -/
theorem exists_matLeadingCol_eq_vecLeadingCol_lt {R : FreeMatrix K m n} {ast : Fin m}
    (hrow' : ¬ matRowZero R ast) :
    matLeadingCol R ast < n := by
  cases hs2 : findPivotRow (fun c => if R ast c ≠ 0 then true else false) n 0 with
  | none => exact absurd (rowZero_of_findPivotRow_eq_none hs2) hrow'
  | some c => exact Eq.mpr (congrArg (· < n) (matLeadingCol_eq_some hs2)) c.isLt
theorem exists_matLeadingCol_eq_vecLeadingCol {R : FreeMatrix K m n} (hR : IsRref R)
    {w : FreeMod K n} (hw : inRowSpan R w) (hw0 : w ≠ 0) :
    ∃ b : Fin m, ¬ matRowZero R b ∧ matLeadingCol R b = vecLeadingCol w := by
  let ⟨d, hd⟩ := hw
  cases hs : findPivotRow
      (fun a => (if d a ≠ 0 then true else false) && matRowNonzeroBool R a) m 0 with
  | none => exact exists_matLeadingCol_eq_vecLeadingCol_none hd hw0 hs
  | some ast =>
      let hspec := findPivotRow_some_spec hs
      let ⟨hdne, hrow⟩ := Bool.and_eq_true_iff.mp hspec.2.2
      let hrow' : ¬ matRowZero R ast := matRowNonzeroBool_true.mp hrow
      let hlc_lt : matLeadingCol R ast < n :=
        exists_matLeadingCol_eq_vecLeadingCol_lt hrow'
      let hvan : ∀ c : Fin n, c.val < matLeadingCol R ast → w c = 0 :=
        fun c hc => exists_matLeadingCol_eq_vecLeadingCol_vanish hR hd hs c hc
      let hne : w ⟨matLeadingCol R ast, hlc_lt⟩ ≠ 0 :=
        exists_matLeadingCol_eq_vecLeadingCol_ne hR hd hs hlc_lt
      let hlcw : vecLeadingCol w = matLeadingCol R ast :=
        vecLeadingCol_eq_of_zero_before hlc_lt hvan hne
      exact ⟨ast, hrow', hlcw.symm⟩
/-! ## Uniqueness of the reduced row-echelon form -/
-- Reference: MRR 1988, Pt. II Ch. 6 (lifting a combination over the tail to a
-- combination over the whole matrix with zero first coefficient).
/-- A combination over the tail rows lifts to the whole matrix. -/
theorem inRowSpan_matTail_lift {R : FreeMatrix K (k + 1) n} {w : FreeMod K n}
    {e : Fin k → K} (he : ∀ j : Fin n, w j = ∑ a ∈ finFinset k, e a * matTail R a j) :
    inRowSpan R w :=
  ⟨Fin.cases 0 e, fun j => by
    have h2 := sum_finFinset_succ (fun b : Fin (k + 1) => Fin.cases 0 e b * R b j)
    have c0 : Fin.cases 0 e 0 * R 0 j = 0 :=
      (congrArg (· * R 0 j) (Fin.cases_zero (motive := fun _ => K) (zero := (0 : K)) (succ := e))).trans
        (zero_mul (R 0 j))
    have cS : (∑ a ∈ finFinset k, Fin.cases 0 e (Fin.succ a) * R (Fin.succ a) j)
        = ∑ a ∈ finFinset k, e a * R (Fin.succ a) j :=
      sum_finFinset_congr (fun a =>
        congrArg (· * R (Fin.succ a) j) (Fin.cases_succ (motive := fun _ => K) (zero := (0 : K)) (succ := e) a))
    have h2' : (∑ b ∈ finFinset (k + 1), Fin.cases 0 e b * R b j)
        = ∑ a ∈ finFinset k, e a * R (Fin.succ a) j :=
      h2.trans ((congrArg (· + _) c0).trans
        ((congrArg (0 + ·) cS).trans (zero_add _)))
    exact (he j).trans h2'.symm⟩
-- Reference: MRR 1988, Pt. II Ch. 6 (if the tail rows of `R` vanish at
-- column `c`, the combination over the tail vanishes there).
/-- A tail combination vanishes at a column where the tail rows vanish. -/
theorem inRowSpan_matTail_of_subset_wc {R : FreeMatrix K (k + 1) n} {w : FreeMod K n}
    {e : Fin k → K} (he : ∀ j : Fin n, w j = ∑ a ∈ finFinset k, e a * matTail R a j)
    {c : Fin n} (hcR : ∀ a : Fin k, R (Fin.succ a) c = 0) : w c = 0 :=
  Eq.mp (congrArg (fun z => z = 0) (he c).symm)
    (sum_finFinset_eq_zero (fun a => (congrArg (e a * ·) (hcR a)).trans (mul_zero (e a))))
-- Reference: MRR 1988, Pt. II Ch. 6 (evaluating the `S`-combination at the
-- pivot column of row `0` of `S` reads off the first coefficient).
/-- At the pivot column of row `0` of `S`, the `S`-combination equals `f 0`. -/
theorem inRowSpan_matTail_of_subset_f0 {S : FreeMatrix K (k + 1) n}
    (hS2 : ∀ a : Fin (k + 1), ∀ c : Fin n, matLeadingCol S a = c.val → S a c = 1)
    (hS4 : ∀ a b : Fin (k + 1), a ≠ b → ∀ c : Fin n,
      matLeadingCol S a = c.val → S b c = 0)
    {w : FreeMod K n} {f : Fin (k + 1) → K}
    (hf : ∀ j : Fin n, w j = ∑ b ∈ finFinset (k + 1), f b * S b j)
    {c : Fin n} (hlcS : matLeadingCol S 0 = c.val) (hwc : w c = 0) : f 0 = 0 := by
  have e1 : w c = ∑ b ∈ finFinset (k + 1), f b * S b c := hf c
  have hcl : ∀ a : Fin k, S (Fin.succ a) c = 0 := fun a =>
    hS4 0 (Fin.succ a) (Ne.symm (Fin.succ_ne_zero a)) c hlcS
  have hsum : (∑ a ∈ finFinset k, f (Fin.succ a) * S (Fin.succ a) c) = 0 :=
    sum_finFinset_eq_zero (fun a => (congrArg (f (Fin.succ a) * ·) (hcl a)).trans (mul_zero _))
  have h2 : (∑ b ∈ finFinset (k + 1), f b * S b c)
      = f 0 * S 0 c + ∑ a ∈ finFinset k, f (Fin.succ a) * S (Fin.succ a) c :=
    sum_finFinset_succ (fun b : Fin (k + 1) => f b * S b c)
  have e2 : (∑ b ∈ finFinset (k + 1), f b * S b c) = f 0 :=
    h2.trans ((congrArg (· + _) (congrArg (f 0 * ·) (hS2 0 c hlcS))).trans
      ((congrArg (f 0 * 1 + ·) hsum).trans ((add_zero _).trans (mul_one _))))
  exact ((Eq.mp (congrArg (fun z => z = ∑ b ∈ finFinset (k + 1), f b * S b c) hwc) e1).trans e2).symm
-- Reference: MRR 1988, Pt. II Ch. 6 (if the rows of `R` after the first vanish
-- at column `c`, then the span of the tail of `R` injects into the span of
-- the tail of `S` via the coefficient at row `0` of `S`).
-- Reference: MRR 1988, Pt. II Ch. 6 (tail-span injection); the final sum step.
/-- The `f 0` summand vanishes, so the full sum is the tail sum. -/
theorem inRowSpan_matTail_of_subset_tail {S : FreeMatrix K (k + 1) n} {f : Fin (k + 1) → K}
    (hf0 : f 0 = 0) (j : Fin n) :
    (∑ b ∈ finFinset (k + 1), f b * S b j)
      = ∑ a ∈ finFinset k, f (Fin.succ a) * S (Fin.succ a) j :=
  let h2 : (∑ b ∈ finFinset (k + 1), f b * S b j)
      = f 0 * S 0 j + ∑ a ∈ finFinset k, f (Fin.succ a) * S (Fin.succ a) j :=
    sum_finFinset_succ (fun b : Fin (k + 1) => f b * S b j)
  h2.trans ((congrArg (· + _) ((congrArg (· * S 0 j) hf0).trans (zero_mul (S 0 j)))).trans
    (zero_add _))
-- Reference: MRR 1988, Pt. II Ch. 6 (if the rows of `R` after the first vanish
-- at column `c`, then the span of the tail of `R` injects into the span of
-- the tail of `S` via the coefficient at row `0` of `S`).
/-- If every tail row of `R` vanishes at column `c`, where `c` is the pivot
column of row `0` of the RREF matrix `S`, then the row span of the tail of
`R` is contained in the row span of the tail of `S`. -/
theorem inRowSpan_matTail_of_subset {R S : FreeMatrix K (k + 1) n}
    (hS : IsRref S) (hsub : ∀ w : FreeMod K n, inRowSpan R w → inRowSpan S w)
    {c : Fin n} (hcR : ∀ a : Fin k, R (Fin.succ a) c = 0)
    (hlcS : matLeadingCol S 0 = c.val) :
    ∀ w : FreeMod K n, inRowSpan (matTail R) w → inRowSpan (matTail S) w := by
  rcases hS with ⟨_, hS2, _, hS4⟩
  intro w hw
  let ⟨e, he⟩ := hw
  let hwR : inRowSpan R w := inRowSpan_matTail_lift he
  let ⟨f, hf⟩ := hsub w hwR
  let hwc : w c = 0 := inRowSpan_matTail_of_subset_wc he hcR
  let hf0 : f 0 = 0 := inRowSpan_matTail_of_subset_f0 hS2 hS4 hf hlcS hwc
  refine ⟨fun a => f (Fin.succ a), fun j => ?_⟩
  exact (hf j).trans (inRowSpan_matTail_of_subset_tail hf0 j)
-- Reference: MRR 1988, Pt. II Ch. 6 (uniqueness of the reduced row-echelon
-- form); the case where row `0` of `R` is zero (then all rows of both
-- matrices are zero).
/-- If row `0` of the RREF matrix `R` is zero, then `R = S`. -/
theorem rref_eq_of_subset_aux_zero_row {n k : ℕ} {R S : FreeMatrix K (k + 1) n}
    (hR : IsRref R) (hS : IsRref S)
    (hsub : ∀ w : FreeMod K n, inRowSpan R w → inRowSpan S w)
    (hd : (∀ w : FreeMod K n, inRowSpan S w → inRowSpan R w) ∨ nzCount R = nzCount S)
    (hs0 : findPivotRow (fun c => if R 0 c ≠ 0 then true else false) n 0 = none) :
    R = S := by
  let ⟨hR1, hR2, hR3, hR4⟩ := hR
  let ⟨hS1, hS2, hS3, hS4⟩ := hS
  have hzR : matRowZero R 0 := rowZero_of_findPivotRow_eq_none hs0
  have hzRall : ∀ a : Fin (k + 1), matRowZero R a := fun a =>
    match Fin.eq_zero_or_eq_succ a with
    | Or.inl h => Eq.mpr (congrArg (fun z => matRowZero R z) h) hzR
    | Or.inr ⟨j, h⟩ => Eq.mpr (congrArg (fun z => matRowZero R z) h) (hR1 0 (Fin.succ j) (Fin.succ_pos j) hzR)
  have hk0 : nzCount R = 0 := nzCount_eq_zero_of_rowZero_zero ⟨hR1, hR2, hR3, hR4⟩ hzR
  have hzS : ∀ b : Fin (k + 1), matRowZero S b := by
    rcases hd with hback | hk
    · intro b
      have hmem : inRowSpan R (S b) := hback (S b) (inRowSpan_self S b)
      let ⟨c, hc⟩ := hmem
      intro c'
      have hsum : (∑ a ∈ finFinset (k + 1), c a * R a c') = 0 :=
        sum_finFinset_eq_zero (fun a => (congrArg (c a * ·) (hzRall a c')).trans (mul_zero (c a)))
      exact (hc c').trans hsum
    · have hkS : nzCount S = 0 := hk.symm.trans hk0
      intro b
      cases hs' : findPivotRow (fun c => if S b c ≠ 0 then true else false) n 0 with
      | none => exact rowZero_of_findPivotRow_eq_none hs'
      | some c =>
          have hpos : 0 < nzCount S := by
            unfold nzCount
            exact List.countP_pos_iff.mpr
              ⟨b, List.mem_finRange b, (congrArg Option.isSome hs').trans (Option.isSome_some (a := c))⟩
          exact absurd (Eq.mp (congrArg (0 < ·) hkS) hpos) (Nat.lt_irrefl 0)
  funext a c
  exact (hzRall a c).trans (hzS a c).symm
-- Reference: MRR 1988, Pt. II Ch. 6 (uniqueness of the reduced row-echelon
-- form); the successor case of the induction on the number of rows, with a
-- pivot in row `0` of `R`.
/-- The successor case of the RREF uniqueness induction: row `0` of `R` is
nonzero; compare leading columns, recurse on the tails, and match row `0`. -/
theorem rref_eq_of_subset_aux_succ {n k : ℕ} (ih : ∀ (R S : FreeMatrix K k n),
    IsRref R → IsRref S →
    (∀ w : FreeMod K n, inRowSpan R w → inRowSpan S w) →
    ((∀ w : FreeMod K n, inRowSpan S w → inRowSpan R w) ∨ nzCount R = nzCount S) →
    R = S)
    {R S : FreeMatrix K (k + 1) n} (hR : IsRref R) (hS : IsRref S)
    (hsub : ∀ w : FreeMod K n, inRowSpan R w → inRowSpan S w)
    (hd : (∀ w : FreeMod K n, inRowSpan S w → inRowSpan R w) ∨ nzCount R = nzCount S)
    {c0 : Fin n}
    (hs0 : findPivotRow (fun c => if R 0 c ≠ 0 then true else false) n 0 = some c0) :
    R = S := by
  let ⟨hR1, hR2, hR3, hR4⟩ := hR
  let ⟨hS1, hS2, hS3, hS4⟩ := hS
  have hspec0 := findPivotRow_some_spec hs0
  have hneR0 : R 0 c0 ≠ 0 := ne_zero_of_pivotBool hspec0.2.2
  have hnzR0 : ¬ matRowZero R 0 := fun hz => hneR0 (hz c0)
  have hlcR : matLeadingCol R 0 = c0.val := matLeadingCol_eq_some hs0
  have hjR : c0.val < n := c0.isLt
  have hjR' : matLeadingCol R 0 < n := Eq.mpr (congrArg (· < n) hlcR) hjR
  have hnzS0 : ¬ matRowZero S 0 := by
    rcases hd with hback | hk
    · intro hzS
      have hzSall : ∀ b : Fin (k + 1), matRowZero S b := fun b =>
        match Fin.eq_zero_or_eq_succ b with
        | Or.inl h => Eq.mpr (congrArg (fun z => matRowZero S z) h) hzS
        | Or.inr ⟨j, h⟩ => Eq.mpr (congrArg (fun z => matRowZero S z) h) (hS1 0 (Fin.succ j) (Fin.succ_pos j) hzS)
      have hmem : inRowSpan S (R 0) := hsub (R 0) (inRowSpan_self R 0)
      let ⟨c, hc⟩ := hmem
      have hsum : ∀ c' : Fin n, (∑ a ∈ finFinset (k + 1), c a * S a c') = 0 :=
        fun c' => sum_finFinset_eq_zero (fun a => (congrArg (c a * ·) (hzSall a c')).trans (mul_zero (c a)))
      have h00 : R 0 c0 = 0 := Eq.mpr (congrArg (· = 0) (hc c0)) (hsum c0)
      exact hneR0 h00
    · intro hzS
      have hkpos : 0 < nzCount R := nzCount_pos_of_not_rowZero_zero hnzR0
      have hkS : nzCount S = nzCount R := hk.symm
      have hk0 : nzCount S = 0 := nzCount_eq_zero_of_rowZero_zero ⟨hS1, hS2, hS3, hS4⟩ hzS
      have hR0 : nzCount R = 0 := hkS.symm.trans hk0
      exact absurd (Eq.mp (congrArg (0 < ·) hR0) hkpos) (Nat.lt_irrefl 0)
  cases hs1 : findPivotRow (fun c => if S 0 c ≠ 0 then true else false) n 0 with
  | none => exact absurd (rowZero_of_findPivotRow_eq_none hs1) hnzS0
  | some c1 =>
    have hlcS : matLeadingCol S 0 = c1.val := matLeadingCol_eq_some hs1
    have hjS : c1.val < n := c1.isLt
    have hjS' : matLeadingCol S 0 < n := Eq.mpr (congrArg (· < n) hlcS) hjS
    -- Step A(i): the leading column of row 0 of S is at most that of R.
    have hle1 : matLeadingCol S 0 ≤ matLeadingCol R 0 := by
      rcases Nat.lt_or_ge (matLeadingCol R 0) (matLeadingCol S 0) with hlt | hge
      · have hvan : ∀ b : Fin (k + 1),
            S b ⟨matLeadingCol R 0, hjR'⟩ = 0 := fun b =>
          entry_eq_zero_of_lt_matLeadingCol
            (Nat.lt_of_lt_of_le hlt (matLeadingCol_zero_le ⟨hS1, hS2, hS3, hS4⟩ b))
        rcases hsub (R 0) (inRowSpan_self R 0) with ⟨d, hd⟩
        have e1 : R 0 ⟨matLeadingCol R 0, hjR'⟩ = 1 := hR2 0 _ (Fin.val_mk hjR').symm
        have e2 : R 0 ⟨matLeadingCol R 0, hjR'⟩
            = ∑ b ∈ finFinset _, d b * S b ⟨matLeadingCol R 0, hjR'⟩ := hd _
        have e3 : (∑ b ∈ finFinset _, d b * S b ⟨matLeadingCol R 0, hjR'⟩) = 0 :=
          sum_finFinset_eq_zero (fun b => (congrArg (d b * ·) (hvan b)).trans (mul_zero (d b)))
        exact absurd (e1.symm.trans (e2.trans e3)) one_ne_zero
      · exact hge
    -- Step A(ii): the leading column of row 0 of R is at most that of S.
    have hle2 : matLeadingCol R 0 ≤ matLeadingCol S 0 := by
      rcases hd with hback | hk
      · rcases Nat.lt_or_ge (matLeadingCol S 0) (matLeadingCol R 0) with hlt | hge
        · have hvan : ∀ b : Fin (k + 1),
              R b ⟨matLeadingCol S 0, hjS'⟩ = 0 := fun b =>
            entry_eq_zero_of_lt_matLeadingCol
              (Nat.lt_of_lt_of_le hlt (matLeadingCol_zero_le ⟨hR1, hR2, hR3, hR4⟩ b))
          rcases hback (S 0) (inRowSpan_self S 0) with ⟨d, hd⟩
          have e1 : S 0 ⟨matLeadingCol S 0, hjS'⟩ = 1 :=
            hS2 0 _ (Fin.val_mk hjS').symm
          have e2 : S 0 ⟨matLeadingCol S 0, hjS'⟩
              = ∑ b ∈ finFinset _, d b * R b ⟨matLeadingCol S 0, hjS'⟩ := hd _
          have e3 : (∑ b ∈ finFinset _, d b * R b ⟨matLeadingCol S 0, hjS'⟩) = 0 :=
            sum_finFinset_eq_zero (fun b => (congrArg (d b * ·) (hvan b)).trans (mul_zero (d b)))
          exact absurd (e1.symm.trans (e2.trans e3)) one_ne_zero
        · exact hge
      · rcases Nat.lt_or_ge (matLeadingCol S 0) (matLeadingCol R 0) with hlt | hge
        · -- jS < jR: absurdity via the tails
          rcases hsub (R 0) (inRowSpan_self R 0) with ⟨d, hd⟩
          have hd0 : d 0 = 0 := by
            have e1 : R 0 ⟨matLeadingCol S 0, hjS'⟩
                = ∑ b ∈ finFinset _, d b * S b ⟨matLeadingCol S 0, hjS'⟩ := hd _
            have e0 : R 0 ⟨matLeadingCol S 0, hjS'⟩ = 0 :=
              entry_eq_zero_of_lt_matLeadingCol hlt
            have hcl : ∀ a : Fin k,
                S (Fin.succ a) ⟨matLeadingCol S 0, hjS'⟩ = 0 := fun a =>
              hS4 0 (Fin.succ a) (Ne.symm (Fin.succ_ne_zero a)) _ (Fin.val_mk hjS').symm
            have hsum : (∑ a ∈ finFinset k,
                d (Fin.succ a) * S (Fin.succ a) ⟨matLeadingCol S 0, hjS'⟩) = 0 :=
              sum_finFinset_eq_zero (fun a => (congrArg (d (Fin.succ a) * ·) (hcl a)).trans (mul_zero _))
            have h2 : (∑ b ∈ finFinset (k + 1), d b * S b ⟨matLeadingCol S 0, hjS'⟩)
                = d 0 * S 0 ⟨matLeadingCol S 0, hjS'⟩
                  + ∑ a ∈ finFinset k,
                    d (Fin.succ a) * S (Fin.succ a) ⟨matLeadingCol S 0, hjS'⟩ :=
              sum_finFinset_succ
                (fun b : Fin (k + 1) => d b * S b ⟨matLeadingCol S 0, hjS'⟩)
            have e2 : (∑ b ∈ finFinset _, d b * S b ⟨matLeadingCol S 0, hjS'⟩) = d 0 :=
              h2.trans ((congrArg (· + _)
                (congrArg (d 0 * ·) (hS2 0 _ (Fin.val_mk hjS' ).symm))).trans
                ((congrArg (d 0 * 1 + ·) hsum).trans ((add_zero _).trans (mul_one _))))
            exact (e0.symm.trans (e1.trans e2)).symm
          have hcR' : ∀ a : Fin k,
              R (Fin.succ a) ⟨matLeadingCol S 0, hjS'⟩ = 0 := by
            intro a
            cases hs3 : findPivotRow
                (fun c => if R (Fin.succ a) c ≠ 0 then true else false) n 0 with
            | none => exact rowZero_of_findPivotRow_eq_none hs3 _
            | some c3 =>
                have hnb : ¬ matRowZero R (Fin.succ a) := fun hz =>
                  ne_zero_of_pivotBool (findPivotRow_some_spec hs3).2.2 (hz c3)
                have hlt3 : matLeadingCol R 0 < matLeadingCol R (Fin.succ a) :=
                  hR3 0 (Fin.succ a) (Fin.succ_pos a) hnb
                exact entry_eq_zero_of_lt_matLeadingCol (Nat.lt_trans hlt hlt3)
          have htail_sub : ∀ w : FreeMod K n, inRowSpan (matTail R) w →
              inRowSpan (matTail S) w :=
            inRowSpan_matTail_of_subset ⟨hS1, hS2, hS3, hS4⟩ hsub hcR'
              (Fin.val_mk hjS').symm
          have hktail : nzCount (matTail R) = nzCount (matTail S) := by
            have e1 := nzCount_succ_eq R hnzR0
            have e2 := nzCount_succ_eq S hnzS0
            exact Nat.add_right_cancel ((Eq.mp (congrArg (fun z => z = nzCount (matTail R) + 1) hk) e1).symm.trans e2)
          have htail_eq : matTail R = matTail S :=
            ih (matTail R) (matTail S) (isRref_matTail ⟨hR1, hR2, hR3, hR4⟩)
              (isRref_matTail ⟨hS1, hS2, hS3, hS4⟩) htail_sub (Or.inr hktail)
          have hR0tail : inRowSpan (matTail S) (R 0) := by
            refine ⟨fun a => d (Fin.succ a), fun j => ?_⟩
            have h2 : (∑ b ∈ finFinset (k + 1), d b * S b j)
                = d 0 * S 0 j + ∑ a ∈ finFinset k, d (Fin.succ a) * S (Fin.succ a) j :=
              sum_finFinset_succ (fun b : Fin (k + 1) => d b * S b j)
            have h2' : (∑ b ∈ finFinset (k + 1), d b * S b j)
                = ∑ a ∈ finFinset k, d (Fin.succ a) * S (Fin.succ a) j :=
              h2.trans ((congrArg (· + _) ((congrArg (· * S 0 j) hd0).trans (zero_mul (S 0 j)))).trans
                (zero_add _))
            exact (hd j).trans h2'
          let hw_tail : inRowSpan (matTail R) (R 0) := Eq.mpr (congrArg (fun M => inRowSpan M (R 0)) htail_eq) hR0tail
          let ⟨e, he⟩ := hw_tail
          have e1 : R 0 ⟨matLeadingCol R 0, hjR'⟩ = 1 := hR2 0 _ (Fin.val_mk hjR').symm
          have e2 : R 0 ⟨matLeadingCol R 0, hjR'⟩
              = ∑ a ∈ finFinset _, e a * matTail R a ⟨matLeadingCol R 0, hjR'⟩ := he _
          have e3 : (∑ a ∈ finFinset _, e a * matTail R a ⟨matLeadingCol R 0, hjR'⟩) = 0 :=
            sum_finFinset_eq_zero (fun a => by
              change e a * R (Fin.succ a) ⟨matLeadingCol R 0, hjR'⟩ = 0
              cases hs3 : findPivotRow
                  (fun c => if R (Fin.succ a) c ≠ 0 then true else false) n 0 with
              | none =>
                  exact (congrArg (e a * ·) (rowZero_of_findPivotRow_eq_none hs3 _)).trans (mul_zero (e a))
              | some c3 =>
                  have hnb : ¬ matRowZero R (Fin.succ a) := fun hz =>
                    ne_zero_of_pivotBool (findPivotRow_some_spec hs3).2.2 (hz c3)
                  have hlt3 : matLeadingCol R 0 < matLeadingCol R (Fin.succ a) :=
                    hR3 0 (Fin.succ a) (Fin.succ_pos a) hnb
                  exact (congrArg (e a * ·) (entry_eq_zero_of_lt_matLeadingCol
                    (c := ⟨matLeadingCol R 0, hjR'⟩) hlt3)).trans (mul_zero (e a)))
          exact absurd (e1.symm.trans (e2.trans e3)) one_ne_zero
        · exact hge
    have hj : matLeadingCol R 0 = matLeadingCol S 0 := Nat.le_antisymm hle2 hle1
    -- The tails: span of the tail of R injects into the tail of S.
    have hcR : ∀ a : Fin k, R (Fin.succ a) ⟨matLeadingCol R 0, hjR'⟩ = 0 := by
      intro a
      cases hs3 : findPivotRow
          (fun c => if R (Fin.succ a) c ≠ 0 then true else false) n 0 with
      | none => exact rowZero_of_findPivotRow_eq_none hs3 _
      | some c3 =>
          have hnb : ¬ matRowZero R (Fin.succ a) := fun hz =>
            ne_zero_of_pivotBool (findPivotRow_some_spec hs3).2.2 (hz c3)
          have hlt3 : matLeadingCol R 0 < matLeadingCol R (Fin.succ a) :=
            hR3 0 (Fin.succ a) (Fin.succ_pos a) hnb
          exact entry_eq_zero_of_lt_matLeadingCol
            (c := ⟨matLeadingCol R 0, hjR'⟩) hlt3
    have hlcS_at : matLeadingCol S 0
        = (⟨matLeadingCol R 0, hjR'⟩ : Fin n).val :=
      Eq.mp (congrArg (fun z => z = (⟨matLeadingCol R 0, hjR'⟩ : Fin n).val) hj) (Fin.val_mk hjR').symm
    have htail_sub : ∀ w : FreeMod K n, inRowSpan (matTail R) w →
        inRowSpan (matTail S) w :=
      inRowSpan_matTail_of_subset ⟨hS1, hS2, hS3, hS4⟩ hsub hcR hlcS_at
    have hdtail : (∀ w : FreeMod K n, inRowSpan (matTail S) w →
          inRowSpan (matTail R) w) ∨
        nzCount (matTail R) = nzCount (matTail S) := by
      rcases hd with hback | hk
      · left
        have hcS : ∀ a : Fin k,
            S (Fin.succ a) ⟨matLeadingCol S 0, hjS'⟩ = 0 := by
          intro a
          cases hs3 : findPivotRow
              (fun c => if S (Fin.succ a) c ≠ 0 then true else false) n 0 with
          | none => exact rowZero_of_findPivotRow_eq_none hs3 _
          | some c3 =>
              have hnb : ¬ matRowZero S (Fin.succ a) := fun hz =>
                ne_zero_of_pivotBool (findPivotRow_some_spec hs3).2.2 (hz c3)
              have hlt3 : matLeadingCol S 0 < matLeadingCol S (Fin.succ a) :=
                hS3 0 (Fin.succ a) (Fin.succ_pos a) hnb
              exact entry_eq_zero_of_lt_matLeadingCol
                (c := ⟨matLeadingCol S 0, hjS'⟩) hlt3
        have hlcR_at : matLeadingCol R 0
            = (⟨matLeadingCol S 0, hjS'⟩ : Fin n).val :=
          Eq.mp (congrArg (fun z => z = (⟨matLeadingCol S 0, hjS'⟩ : Fin n).val) hj.symm) (Fin.val_mk hjS').symm
        exact inRowSpan_matTail_of_subset ⟨hR1, hR2, hR3, hR4⟩ hback hcS hlcR_at
      · right
        have e1 := nzCount_succ_eq R hnzR0
        have e2 := nzCount_succ_eq S hnzS0
        exact Nat.add_right_cancel ((Eq.mp (congrArg (fun z => z = nzCount (matTail R) + 1) hk) e1).symm.trans e2)
    have htail_eq : matTail R = matTail S :=
      ih (matTail R) (matTail S) (isRref_matTail ⟨hR1, hR2, hR3, hR4⟩)
        (isRref_matTail ⟨hS1, hS2, hS3, hS4⟩) htail_sub hdtail
    have hrows : ∀ a : Fin k, R (Fin.succ a) = S (Fin.succ a) :=
      fun a => congrFun htail_eq a
    -- The coefficient of row 0 in the expansion of R 0 over S is 1.
    rcases hsub (R 0) (inRowSpan_self R 0) with ⟨d, hd⟩
    have hd0 : d 0 = 1 := by
      have e1 : R 0 ⟨matLeadingCol R 0, hjR'⟩
          = ∑ b ∈ finFinset _, d b * S b ⟨matLeadingCol R 0, hjR'⟩ := hd _
      have e0 : R 0 ⟨matLeadingCol R 0, hjR'⟩ = 1 :=
        hR2 0 _ (Fin.val_mk hjR').symm
      have hcl : ∀ a : Fin k,
          S (Fin.succ a) ⟨matLeadingCol R 0, hjR'⟩ = 0 := fun a =>
        hS4 0 (Fin.succ a) (Ne.symm (Fin.succ_ne_zero a)) _ hlcS_at
      have hsum : (∑ a ∈ finFinset k,
          d (Fin.succ a) * S (Fin.succ a) ⟨matLeadingCol R 0, hjR'⟩) = 0 :=
        sum_finFinset_eq_zero (fun a => (congrArg (d (Fin.succ a) * ·) (hcl a)).trans (mul_zero _))
      have h2 : (∑ b ∈ finFinset (k + 1), d b * S b ⟨matLeadingCol R 0, hjR'⟩)
          = d 0 * S 0 ⟨matLeadingCol R 0, hjR'⟩
            + ∑ a ∈ finFinset k,
              d (Fin.succ a) * S (Fin.succ a) ⟨matLeadingCol R 0, hjR'⟩ :=
        sum_finFinset_succ
          (fun b : Fin (k + 1) => d b * S b ⟨matLeadingCol R 0, hjR'⟩)
      have e2 : (∑ b ∈ finFinset _, d b * S b ⟨matLeadingCol R 0, hjR'⟩) = d 0 :=
        h2.trans ((congrArg (· + _) (congrArg (d 0 * ·) (hS2 0 _ hlcS_at))).trans
          ((congrArg (d 0 * 1 + ·) hsum).trans ((add_zero _).trans (mul_one _))))
      exact (e0.symm.trans (e1.trans e2)).symm
    -- The difference `R 0 - S 0` lies in the span of the tail of S.
    have hw_tail : inRowSpan (matTail S) (R 0 - S 0) := by
      refine ⟨fun a => d (Fin.succ a), fun j => ?_⟩
      have h2 : (∑ b ∈ finFinset (k + 1), d b * S b j)
          = d 0 * S 0 j + ∑ a ∈ finFinset k, d (Fin.succ a) * S (Fin.succ a) j :=
        sum_finFinset_succ (fun b : Fin (k + 1) => d b * S b j)
      have h2' : (∑ b ∈ finFinset (k + 1), d b * S b j)
          = S 0 j + ∑ a ∈ finFinset k, d (Fin.succ a) * S (Fin.succ a) j :=
        h2.trans (congrArg (· + ∑ a ∈ finFinset k, d (Fin.succ a) * S (Fin.succ a) j)
          ((congrArg (· * S 0 j) hd0).trans (one_mul (S 0 j))))
      change R 0 j - S 0 j = ∑ a ∈ finFinset k, d (Fin.succ a) * S (Fin.succ a) j
      exact Eq.mpr (congrArg (fun z => z - S 0 j = ∑ a ∈ finFinset k, d (Fin.succ a) * S (Fin.succ a) j) (hd j))
        (Eq.mpr (congrArg (fun z => z - S 0 j = ∑ a ∈ finFinset k, d (Fin.succ a) * S (Fin.succ a) j) h2')
          (add_sub_cancel_left _ _))
    let hw_tail' : inRowSpan (matTail R) (R 0 - S 0) := Eq.mpr (congrArg (fun M => inRowSpan M (R 0 - S 0)) htail_eq) hw_tail
    -- Show `R 0 = S 0`: otherwise the pivot lemma contradicts clause 4.
    have hR0eqS0 : R 0 = S 0 := by
      cases (inferInstance : Decidable (R 0 - S 0 = 0)) with
      | isTrue h => exact sub_eq_zero.mp h
      | isFalse hw0 =>
          rcases exists_matLeadingCol_eq_vecLeadingCol
              (isRref_matTail ⟨hR1, hR2, hR3, hR4⟩) hw_tail' hw0 with
            ⟨bstar, hnb, hlc⟩
          have hlc' : matLeadingCol R (Fin.succ bstar)
              = vecLeadingCol (R 0 - S 0) := hlc
          have hvan : ∀ c : Fin n, c.val ≤ matLeadingCol R 0 →
              (R 0 - S 0) c = 0 := by
            intro c hc
            rcases Nat.lt_or_ge c.val (matLeadingCol R 0) with hlt | hge
            · exact (Pi.sub_apply (R 0) (S 0) c).trans
                ((congrArg₂ (· - ·)
                  (entry_eq_zero_of_lt_matLeadingCol (A := R) (a := 0) (c := c) hlt)
                  (entry_eq_zero_of_lt_matLeadingCol (A := S) (a := 0) (c := c)
(Eq.mp (congrArg (c.val < ·) hj) hlt))).trans (sub_self 0))
            · have heq : c = ⟨matLeadingCol R 0, hjR'⟩ :=
                Fin.eq_of_val_eq (Nat.le_antisymm hc hge)
              exact Eq.mpr (congrArg (fun z => (R 0 - S 0) z = 0) heq) ((Pi.sub_apply (R 0) (S 0) _).trans
                ((congrArg₂ (· - ·) (hR2 0 _ (Fin.val_mk hjR').symm) (hS2 0 _ hlcS_at)).trans
                  (sub_self 1)))
          have hgt : matLeadingCol R 0 < vecLeadingCol (R 0 - S 0) :=
            vecLeadingCol_lt_of_vanish hw0 hvan
          have hjj : vecLeadingCol (R 0 - S 0) < n := vecLeadingCol_lt hw0
          have hne_w : (R 0 - S 0) ⟨vecLeadingCol (R 0 - S 0), hjj⟩ ≠ 0 :=
            vecLeadingCol_ne_zero hw0
          have hlcS' : matLeadingCol S (Fin.succ bstar)
              = (⟨vecLeadingCol (R 0 - S 0), hjj⟩ : Fin n).val := by
            have h1 := matLeadingCol_congr (A := R) (B := S)
              (a := Fin.succ bstar) (b := Fin.succ bstar)
              (fun c => congrFun (hrows bstar) c)
            exact Eq.mp (congrArg (fun z => z = (⟨vecLeadingCol (R 0 - S 0), hjj⟩ : Fin n).val) h1) (hlc'.trans (Fin.val_mk hjj).symm)
          have hS0 : S 0 ⟨vecLeadingCol (R 0 - S 0), hjj⟩ = 0 :=
            hS4 (Fin.succ bstar) 0 (Fin.succ_ne_zero bstar) _ hlcS'
          have hR0 : R 0 ⟨vecLeadingCol (R 0 - S 0), hjj⟩ = 0 :=
            hR4 (Fin.succ bstar) 0 (Fin.succ_ne_zero bstar) _ hlc'
          have hzero : (R 0 - S 0) ⟨vecLeadingCol (R 0 - S 0), hjj⟩ = 0 :=
            (Pi.sub_apply (R 0) (S 0) _).trans
              ((congrArg₂ (· - ·) hR0 hS0).trans (sub_self 0))
          exact absurd hzero hne_w
    funext a
    rcases Fin.eq_zero_or_eq_succ a with h | ⟨j', h⟩
    · exact Eq.mpr (congrArg (fun z => R z = S z) h) hR0eqS0
    · exact Eq.mpr (congrArg (fun z => R z = S z) h) (hrows j')
-- Reference: MRR 1988, Pt. II Ch. 6 (uniqueness of the reduced row-echelon
-- form: proved by induction on the number of rows — compare the leading
-- columns of the first rows, show the first rows agree, and recurse on the
-- tails). The disjunctive hypothesis covers both the symmetric case (spans
-- equal) and the one-sided case (nonzero-row counts equal).
/-- Auxiliary induction for uniqueness of the RREF: two RREF matrices with
the same number of rows, one-sided span inclusion, and either the reverse
inclusion or equal nonzero-row counts, are equal. -/
theorem rref_eq_of_subset_aux {n : ℕ} :
    ∀ (l : ℕ) (R S : FreeMatrix K l n), IsRref R → IsRref S →
      (∀ w : FreeMod K n, inRowSpan R w → inRowSpan S w) →
      ((∀ w : FreeMod K n, inRowSpan S w → inRowSpan R w) ∨ nzCount R = nzCount S) →
      R = S :=
  fun l => Nat.rec (motive := fun l => ∀ (R S : FreeMatrix K l n), IsRref R → IsRref S →
      (∀ w : FreeMod K n, inRowSpan R w → inRowSpan S w) →
      ((∀ w : FreeMod K n, inRowSpan S w → inRowSpan R w) ∨ nzCount R = nzCount S) →
      R = S)
    (fun R S _ _ _ _ => funext fun a => Fin.elim0 a)
    (fun k ih R S hR hS hsub hd => by
      cases hs0 : findPivotRow (fun c => if R 0 c ≠ 0 then true else false) n 0 with
      | none => exact rref_eq_of_subset_aux_zero_row hR hS hsub hd hs0
      | some c0 => exact rref_eq_of_subset_aux_succ ih hR hS hsub hd hs0)
    l
-- Reference: MRR 1988, Pt. II Ch. 6 (uniqueness of the RREF).
/-- Two RREF matrices with the same number of rows and the same row span are
equal. -/
theorem rref_eq_of_span_eq {l : ℕ} {R S : FreeMatrix K l n} (hR : IsRref R) (hS : IsRref S)
    (h : ∀ w : FreeMod K n, inRowSpan R w ↔ inRowSpan S w) : R = S :=
  rref_eq_of_subset_aux l R S hR hS (fun w hw => (h w).mp hw)
    (Or.inl (fun w hw => (h w).mpr hw))
-- Reference: MRR 1988, Pt. II Ch. 6 (uniqueness of the RREF, one-sided form:
-- inclusion of spans plus equal rank forces equality).
/-- Two RREF matrices with the same number of rows, one-sided span inclusion,
and equal nonzero-row counts are equal. -/
theorem rref_eq_of_subset_nzCount {l : ℕ} {R S : FreeMatrix K l n} (hR : IsRref R)
    (hS : IsRref S) (hsub : ∀ w : FreeMod K n, inRowSpan R w → inRowSpan S w)
    (hk : nzCount R = nzCount S) : R = S :=
  rref_eq_of_subset_aux l R S hR hS hsub (Or.inr hk)
/-! ## The rank criterion and the decision procedures -/
-- Reference: MRR 1988, Pt. II Ch. 6 (the rank of a matrix is the number of
-- nonzero rows of its RREF).
/-- The computed rank of `A`: the number of nonzero rows of its RREF. -/
def rankOf (invK : K → K) (A : FreeMatrix K m n) : ℕ := nzCount (rref invK A)
-- Reference: MRR 1988, Pt. II Ch. 6 (`v ∈ span S` implies
-- `rank(S ∪ {v}) = rank S`: the span is unchanged, the RREF is unique, and
-- appending a zero row does not change the count).
/-- If `v` lies in the row span of `A`, appending it as a row does not change
the computed rank. -/
theorem nzCount_rref_snoc_eq_of_mem (hinv : ∀ a : K, a ≠ 0 → invK a * a = 1)
    {A : FreeMatrix K m n} {v : FreeMod K n} (hv : inRowSpan A v) :
    nzCount (rref invK (matSnoc A v)) = nzCount (rref invK A) := by
  have hR : IsRref (rref invK A) := rref_isRref invK hinv A
  have hR' : IsRref (rref invK (matSnoc A v)) := rref_isRref invK hinv (matSnoc A v)
  have hpad : IsRref (matSnoc (rref invK A) 0) := isRref_snoc_zero hR
  have hs1 : ∀ w : FreeMod K n, inRowSpan (matSnoc (rref invK A) 0) w ↔
      inRowSpan (rref invK A) w :=
    fun w => inRowSpan_snoc_of_mem (w := w) (inRowSpan_zero (rref invK A))
  have hs2 : ∀ w : FreeMod K n, inRowSpan (rref invK (matSnoc A v)) w ↔
      inRowSpan (matSnoc A v) w := fun w => inRowSpan_rref invK hinv (matSnoc A v) w
  have hs3 : ∀ w : FreeMod K n, inRowSpan (rref invK A) w ↔ inRowSpan A w :=
    fun w => inRowSpan_rref invK hinv A w
  have hs4 : ∀ w : FreeMod K n, inRowSpan (matSnoc A v) w ↔ inRowSpan A w :=
    fun w => inRowSpan_snoc_of_mem hv
  have heq : ∀ w : FreeMod K n, inRowSpan (matSnoc (rref invK A) 0) w ↔
      inRowSpan (rref invK (matSnoc A v)) w :=
    fun w => (hs1 w).trans ((hs3 w).trans ((hs4 w).symm.trans (hs2 w).symm))
  have h_eq_mat := rref_eq_of_span_eq hpad hR' heq
  exact Eq.mp (congrArg (fun M => nzCount M = nzCount (rref invK A)) h_eq_mat) (nzCount_snoc_zero (rref invK A))
-- Reference: MRR 1988, Pt. II Ch. 6 (`rank(S ∪ {v}) = rank S` implies
-- `v ∈ span S`: pad the RREF of `A` with a zero row; the one-sided uniqueness
-- with equal counts forces it to equal the RREF of `A` with `v` appended).
/-- If appending `v` as a row does not change the computed rank, then `v`
lies in the row span of `A`. -/
theorem mem_of_nzCount_rref_snoc_eq (hinv : ∀ a : K, a ≠ 0 → invK a * a = 1)
    {A : FreeMatrix K m n} {v : FreeMod K n}
    (hk : nzCount (rref invK (matSnoc A v)) = nzCount (rref invK A)) :
    inRowSpan A v := by
  have hR : IsRref (rref invK A) := rref_isRref invK hinv A
  have hR' : IsRref (rref invK (matSnoc A v)) := rref_isRref invK hinv (matSnoc A v)
  have hpad : IsRref (matSnoc (rref invK A) 0) := isRref_snoc_zero hR
  have hkpad : nzCount (matSnoc (rref invK A) 0) = nzCount (rref invK (matSnoc A v)) :=
    (nzCount_snoc_zero (rref invK A)).trans hk.symm
  have hsub : ∀ w : FreeMod K n, inRowSpan (matSnoc (rref invK A) 0) w →
      inRowSpan (rref invK (matSnoc A v)) w := by
    intro w hw
    have h1 : inRowSpan (rref invK A) w :=
      (inRowSpan_snoc_of_mem (w := w) (inRowSpan_zero (rref invK A))).mp hw
    have h2 : inRowSpan A w := (inRowSpan_rref invK hinv A w).mp h1
    have h3 : inRowSpan (matSnoc A v) w := inRowSpan_snoc_mono h2
    exact (inRowSpan_rref invK hinv (matSnoc A v) w).mpr h3
  have h_eq_mat := rref_eq_of_subset_nzCount hpad hR' hsub hkpad
  have hv1 : inRowSpan (matSnoc A v) v := inRowSpan_snoc_self
  have hv2 : inRowSpan (rref invK (matSnoc A v)) v :=
    (inRowSpan_rref invK hinv (matSnoc A v) v).mpr hv1
  have hv2' : inRowSpan (matSnoc (rref invK A) 0) v := Eq.mpr (congrArg (fun M => inRowSpan M v) h_eq_mat) hv2
  have hv3 : inRowSpan (rref invK A) v :=
    (inRowSpan_snoc_of_mem (w := v) (inRowSpan_zero (rref invK A))).mp hv2'
  exact (inRowSpan_rref invK hinv A v).mp hv3
-- Reference: MRR 1988, Pt. II Ch. 6 (the rank criterion for membership:
-- `v ∈ span S` iff `rank(S ∪ {v}) = rank S`).
/-- The rank criterion: `v` lies in the row span of `A` iff appending it as a
row leaves the computed rank unchanged. -/
theorem inRowSpan_iff_rankOf_snoc_eq (hinv : ∀ a : K, a ≠ 0 → invK a * a = 1)
    {A : FreeMatrix K m n} {v : FreeMod K n} :
    inRowSpan A v ↔ rankOf invK (matSnoc A v) = rankOf invK A := by
  unfold rankOf
  exact ⟨fun hv => nzCount_rref_snoc_eq_of_mem invK hinv hv,
    fun hk => mem_of_nzCount_rref_snoc_eq invK hinv hk⟩
-- Reference: MRR 1988, Pt. II Ch. 6 (membership decided by the rank
-- comparison, as a `Bool`).
/-- The membership decision for a spanning-set subspace: `v ∈ span(rows A)`
iff `rankOf (A; v) = rankOf A`, computed as a `Bool`. -/
def memRowSpanBool (invK : K → K) (A : FreeMatrix K m n) (v : FreeMod K n) : Bool :=
  (rankOf invK (matSnoc A v) == rankOf invK A)
-- Reference: issue #110 (membership decided by the rank comparison).
/-- The membership decision is correct: it says `true` iff `v` lies in the
row span of `A`. -/
theorem memRowSpanBool_true_iff (hinv : ∀ a : K, a ≠ 0 → invK a * a = 1)
    {A : FreeMatrix K m n} {v : FreeMod K n} :
    memRowSpanBool invK A v = true ↔ inRowSpan A v :=
  beq_iff_eq.trans (inRowSpan_iff_rankOf_snoc_eq invK hinv).symm
-- Reference: issue #110 (an explicit `Decidable` instance replacing
-- `Classical.dec`).
/-- Decidable membership in the row span of `A`, computed by the rank
comparison; explicit in the inverse data `invK`/`hinv` (STYLE §2.3), so this
is a `def` rather than a typeclass instance. -/
def memRowSpanDecidable (invK : K → K) (hinv : ∀ a : K, a ≠ 0 → invK a * a = 1)
    (A : FreeMatrix K m n) (v : FreeMod K n) : Decidable (inRowSpan A v) :=
  decidable_of_iff (memRowSpanBool invK A v = true) (memRowSpanBool_true_iff invK hinv)
-- Reference: MRR 1988, Pt. II Ch. 6 (containment of spans reduces to
-- membership of the generators of one in the other).
/-- Containment of spans is decided by membership of every row of `B` in the
span of `A`, row by row, as a `Bool`. -/
def spanContainsBool (invK : K → K) (A : FreeMatrix K m n) (B : FreeMatrix K p n) : Bool :=
  (List.finRange p).all (fun b => memRowSpanBool invK A (B b))
-- Reference: MRR 1988, Pt. II Ch. 6 (`span B ⊆ span A` iff every generator of
-- `B` lies in `span A`).
omit [DecidableEq K] in
/-- Containment of spans holds iff every row of `B` lies in the span of `A`. -/
theorem spanContains_iff_rows {A : FreeMatrix K m n} {B : FreeMatrix K p n} :
    (∀ b : Fin p, inRowSpan A (B b)) ↔
      ∀ w : FreeMod K n, inRowSpan B w → inRowSpan A w :=
  ⟨fun h w hw => inRowSpan_mono (B := A) _ B w h hw, fun h b => h (B b) (inRowSpan_self B b)⟩
-- Reference: MRR 1988, Pt. II Ch. 6 (the elements of `finRange n` are exactly
-- the `Fin n`).
/-- A pointwise condition on `List.finRange n` is equivalent to the condition
on all of `Fin n`. -/
theorem forall_mem_finRange {n : ℕ} {p : Fin n → Bool} :
    (∀ x ∈ List.finRange n, p x = true) ↔ ∀ x : Fin n, p x = true :=
  ⟨fun h x => h x (List.mem_finRange x), fun h x _ => h x⟩
-- Reference: issue #110 (containment decided by the membership decisions).
-- Reference: issue #110 (containment decided by the membership decisions);
-- the pointwise iff step.
/-- Membership decisions say `true` pointwise iff every row of `B` is in the
span of `A`. -/
theorem spanContainsBool_true_iff_rows (hinv : ∀ a : K, a ≠ 0 → invK a * a = 1)
    {A : FreeMatrix K m n} {B : FreeMatrix K p n} :
    (∀ b : Fin p, memRowSpanBool invK A (B b) = true) ↔ ∀ b : Fin p, inRowSpan A (B b) :=
  forall_congr' (fun b => memRowSpanBool_true_iff invK hinv (A := A) (v := B b))
theorem spanContainsBool_true_iff (hinv : ∀ a : K, a ≠ 0 → invK a * a = 1)
    {A : FreeMatrix K m n} {B : FreeMatrix K p n} :
    spanContainsBool invK A B = true ↔ ∀ b : Fin p, inRowSpan A (B b) := by
  change (List.finRange p).all (fun b => memRowSpanBool invK A (B b)) = true ↔ _
  exact ((List.all_eq_true (l := List.finRange p)
      (p := fun b => memRowSpanBool invK A (B b))).trans forall_mem_finRange).trans
    (spanContainsBool_true_iff_rows invK hinv)
-- Reference: issue #110 (an explicit `Decidable` for containment).
/-- Decidable containment `span B ⊆ span A`, computed row by row; explicit
in the inverse data `invK`/`hinv` (STYLE §2.3), so a `def`. -/
def spanContainsDecidable (invK : K → K) (hinv : ∀ a : K, a ≠ 0 → invK a * a = 1)
    (A : FreeMatrix K m n) (B : FreeMatrix K p n) :
    Decidable (∀ w : FreeMod K n, inRowSpan B w → inRowSpan A w) :=
  decidable_of_iff (spanContainsBool invK A B = true)
    ((spanContainsBool_true_iff invK hinv).trans (spanContains_iff_rows))
-- Reference: MRR 1988, Pt. II Ch. 6 (equality of spans is mutual
-- containment).
/-- Equality of spans is decided by mutual containment, as a `Bool`. -/
def spanEqBool (invK : K → K) (A : FreeMatrix K m n) (B : FreeMatrix K p n) : Bool :=
  spanContainsBool invK A B && spanContainsBool invK B A
-- Reference: issue #110 (equality decided by mutual containment).
-- Reference: issue #110 (equality decided by mutual containment); forward
-- direction.
/-- If both containment decisions hold, the spans are equal. -/
theorem spanEqBool_true_iff_fwd (hinv : ∀ a : K, a ≠ 0 → invK a * a = 1)
    {A : FreeMatrix K m n} {B : FreeMatrix K p n}
    (h1 : spanContainsBool invK A B = true) (h2 : spanContainsBool invK B A = true) :
    ∀ w : FreeMod K n, inRowSpan A w ↔ inRowSpan B w :=
  let e1 := (spanContainsBool_true_iff invK hinv).mp h1
  let e2 := (spanContainsBool_true_iff invK hinv).mp h2
  fun w => ⟨(spanContains_iff_rows.mp e2) w, (spanContains_iff_rows.mp e1) w⟩
-- Reference: issue #110 (equality decided by mutual containment); backward
-- direction.
/-- If the spans are equal, both containment decisions hold. -/
theorem spanEqBool_true_iff_bwd (hinv : ∀ a : K, a ≠ 0 → invK a * a = 1)
    {A : FreeMatrix K m n} {B : FreeMatrix K p n}
    (h : ∀ w : FreeMod K n, inRowSpan A w ↔ inRowSpan B w) :
    spanContainsBool invK A B = true ∧ spanContainsBool invK B A = true :=
  ⟨(spanContainsBool_true_iff invK hinv).mpr (fun b => (h (B b)).mpr (inRowSpan_self B b)),
    (spanContainsBool_true_iff invK hinv).mpr (fun a => (h (A a)).mp (inRowSpan_self A a))⟩
theorem spanEqBool_true_iff (hinv : ∀ a : K, a ≠ 0 → invK a * a = 1)
    {A : FreeMatrix K m n} {B : FreeMatrix K p n} :
    spanEqBool invK A B = true ↔ ∀ w : FreeMod K n, inRowSpan A w ↔ inRowSpan B w := by
  change (spanContainsBool invK A B && spanContainsBool invK B A) = true ↔ _
  exact Bool.and_eq_true_iff.trans
    ⟨fun ⟨h1, h2⟩ => spanEqBool_true_iff_fwd invK hinv h1 h2,
      fun h => spanEqBool_true_iff_bwd invK hinv h⟩
-- Reference: issue #110 (an explicit `Decidable` for span equality).
/-- Decidable equality of the spans of `A` and `B`, computed by mutual
containment; explicit in the inverse data `invK`/`hinv` (STYLE §2.3), so a
`def`. -/
def spanEqDecidable (invK : K → K) (hinv : ∀ a : K, a ≠ 0 → invK a * a = 1)
    (A : FreeMatrix K m n) (B : FreeMatrix K p n) :
    Decidable (∀ w : FreeMod K n, inRowSpan A w ↔ inRowSpan B w) :=
  decidable_of_iff (spanEqBool invK A B = true) (spanEqBool_true_iff invK hinv)
-- Reference: MRR 1988, Pt. II Ch. 6 (for an RREF-given subspace, membership is
-- decided by the residual against the pivot rows).
/-- The membership decision for an RREF-given subspace: the residual of `v`
against the pivot rows vanishes at every column, as a `Bool`. -/
def rrefResidualBool (R : FreeMatrix K m n) (v : FreeMod K n) : Bool :=
  (List.finRange n).all (fun c => if rrefResidual R v c = 0 then true else false)
-- Reference: MRR 1988, Pt. II Ch. 6 (the residual criterion, as a `Bool`).
-- Reference: MRR 1988, Pt. II Ch. 6 (the residual criterion, as a `Bool`); the
-- per-column iff.
/-- The residual test at `c` says `true` iff the residual at `c` is zero. -/
theorem rrefResidualBool_true_iff_col {R : FreeMatrix K m n} {v : FreeMod K n} (c : Fin n) :
    (if rrefResidual R v c = 0 then true else false) = true ↔ rrefResidual R v c = 0 :=
  ⟨fun h => by
      cases (inferInstance : Decidable (rrefResidual R v c = 0)) with
      | isTrue h0 => exact h0
      | isFalse h0 =>
          let hf : (if rrefResidual R v c = 0 then true else false) = false := ite_eq_right h0
          exact absurd (Eq.mp (congrArg (· = true) hf) h) Bool.false_ne_true,
    fun h => ite_eq_left h⟩
-- Reference: MRR 1988, Pt. II Ch. 6 (the residual criterion, as a `Bool`); the
-- pointwise iff over all columns.
/-- The residual test holds on all of `finRange n` iff the residual vanishes
at every column. -/
theorem rrefResidualBool_true_iff_all {R : FreeMatrix K m n} {v : FreeMod K n} :
    (∀ x ∈ List.finRange n, (if rrefResidual R v x = 0 then true else false) = true) ↔
      ∀ c : Fin n, rrefResidual R v c = 0 :=
  forall_mem_finRange.trans (forall_congr' (fun c => rrefResidualBool_true_iff_col c))
-- Reference: MRR 1988, Pt. II Ch. 6 (the residual criterion, as a `Bool`).
/-- The residual decision is correct for RREF matrices. -/
theorem rrefResidualBool_true_iff {R : FreeMatrix K m n} (hR : IsRref R) (v : FreeMod K n) :
    rrefResidualBool R v = true ↔ inRowSpan R v := by
  change (List.finRange n).all (fun c => if rrefResidual R v c = 0 then true else false)
      = true ↔ _
  exact ((List.all_eq_true (l := List.finRange n)
      (p := fun c => if rrefResidual R v c = 0 then true else false)).trans
    rrefResidualBool_true_iff_all).trans (inRowSpan_rref_iff hR v).symm
-- Reference: issue #110 (an explicit `Decidable` for membership in an
-- RREF-given subspace; the RREF predicate is explicit data, STYLE §2.3).
/-- Decidable membership in the row span of an RREF matrix `R`, computed by
the residual criterion; explicit in the RREF proof (a `def`, not a typeclass
instance). -/
def rrefMemRowSpanDecidable (R : FreeMatrix K m n) (hR : IsRref R) (v : FreeMod K n) :
    Decidable (inRowSpan R v) :=
  decidable_of_iff (rrefResidualBool R v = true) (rrefResidualBool_true_iff hR v)
/-! ## Smoke tests -/
-- Reference: smoke test for the acceptance criterion of issue #110 (concrete
-- decisions over `ℚ`).
/-- The explicit inverse of a nonzero rational, as the core data `Rat.inv`
(avoiding the choice-tainted `⁻¹` instance path at the pin, as in
`RowReduction`). -/
def ratInv (a : ℚ) : ℚ := Rat.inv a
-- Reference: smoke test (issue #110): the plane in `ℚ³` spanned by `(1,0,1)`
-- and `(0,1,1)`.
/-- A 2×3 matrix over `ℚ` whose rows span a plane in `ℚ³`. -/
def smokeA : Fin 2 → Fin 3 → ℚ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 1 | 0, 2 => 1
  | 1, 1 => 1 | 1, 2 => 1
  | _, _ => 0
-- Reference: smoke test: the row `(1,1,2)` lies in the plane (it is the sum of
-- the two rows of `smokeA`).
/-- A 1×3 matrix over `ℚ` whose row lies in the plane of `smokeA`. -/
def smokeB : Fin 1 → Fin 3 → ℚ := fun _ j =>
  match j.val with
  | 0 => 1 | 1 => 1 | 2 => 2
  | _ => 0
-- Reference: smoke test: the row `(1,1,1)` does not lie in the plane.
/-- A 1×3 matrix over `ℚ` whose row does not lie in the plane of `smokeA`. -/
def smokeC : Fin 1 → Fin 3 → ℚ := fun _ j =>
  match j.val with
  | 0 => 1 | 1 => 1 | 2 => 1
  | _ => 0
#eval memRowSpanBool ratInv smokeA (smokeB 0)
#eval memRowSpanBool ratInv smokeA (smokeC 0)
#eval spanContainsBool ratInv smokeA smokeB
#eval spanContainsBool ratInv smokeA smokeC
#eval spanEqBool ratInv smokeA smokeA
#eval rrefResidualBool (rref ratInv smokeA) (smokeB 0)
#eval rrefResidualBool (rref ratInv smokeA) (smokeC 0)
#eval rankOf ratInv smokeA
#eval rankOf ratInv (matSnoc smokeA (smokeB 0))
/-! ## Axiom lint -/
#lint_axioms BoringMath.inRowSpan
#lint_axioms BoringMath.inRowSpan_self
#lint_axioms BoringMath.inRowSpan_zero
#lint_axioms BoringMath.inRowSpan_smul
#lint_axioms BoringMath.inRowSpan_add
#lint_axioms BoringMath.inRowSpan_neg
#lint_axioms BoringMath.inRowSpan_sub
#lint_axioms BoringMath.matSnoc
#lint_axioms BoringMath.matSnoc_castSucc
#lint_axioms BoringMath.matSnoc_last
#lint_axioms BoringMath.inRowSpan_snoc
#lint_axioms BoringMath.inRowSpan_mono
#lint_axioms BoringMath.inRowSpan_snoc_self
#lint_axioms BoringMath.inRowSpan_snoc_mono
#lint_axioms BoringMath.inRowSpan_snoc_of_mem
#lint_axioms BoringMath.findPivotRow_congr
#lint_axioms BoringMath.findPivotRow_some_first
#lint_axioms BoringMath.matLeadingCol_congr
#lint_axioms BoringMath.matLeadingCol_le
#lint_axioms BoringMath.findPivotRow_eq_none_of_rowZero
#lint_axioms BoringMath.rowZero_of_findPivotRow_eq_none
#lint_axioms BoringMath.matRowZero_of_matLeadingCol_eq
#lint_axioms BoringMath.entry_eq_zero_of_lt_matLeadingCol
#lint_axioms BoringMath.matLeadingCol_zero_le
#lint_axioms BoringMath.matRowNonzeroBool
#lint_axioms BoringMath.matRowNonzeroBool_true
#lint_axioms BoringMath.matRowNonzeroBool_false_of_rowZero
#lint_axioms BoringMath.matRowNonzeroBool_congr
#lint_axioms BoringMath.nzCount
#lint_axioms BoringMath.nzCount_snoc_zero
#lint_axioms BoringMath.matTail
#lint_axioms BoringMath.matRowNonzeroBool_tail
#lint_axioms BoringMath.nzCount_succ_eq
#lint_axioms BoringMath.nzCount_eq_zero_of_rowZero_zero
#lint_axioms BoringMath.nzCount_pos_of_not_rowZero_zero
#lint_axioms BoringMath.matRowSwap_row_left
#lint_axioms BoringMath.matRowSwap_row_right
#lint_axioms BoringMath.matRowSwap_row_other
#lint_axioms BoringMath.inRowSpan_swap
#lint_axioms BoringMath.matRowScale_row_self
#lint_axioms BoringMath.matRowScale_row_other
#lint_axioms BoringMath.ne_zero_invK
#lint_axioms BoringMath.inRowSpan_scale
#lint_axioms BoringMath.matRowElim_row_self
#lint_axioms BoringMath.matRowElim_row_other
#lint_axioms BoringMath.inRowSpan_elim
#lint_axioms BoringMath.inRowSpan_rrefAux
#lint_axioms BoringMath.inRowSpan_rref
#lint_axioms BoringMath.isRref_matTail
#lint_axioms BoringMath.isRref_snoc_zero
#lint_axioms BoringMath.vecLeadingCol
#lint_axioms BoringMath.vecLeadingCol_eq_some
#lint_axioms BoringMath.vecLeadingCol_eq_none
#lint_axioms BoringMath.vecLeadingCol_eq_of_zero_before
#lint_axioms BoringMath.vecLeadingCol_lt
#lint_axioms BoringMath.vecLeadingCol_ne_zero
#lint_axioms BoringMath.vecLeadingCol_vanish_before
#lint_axioms BoringMath.vecLeadingCol_lt_of_vanish
#lint_axioms BoringMath.rref_sum_at_pivot
#lint_axioms BoringMath.rrefCoeff
#lint_axioms BoringMath.rrefResidual
#lint_axioms BoringMath.inRowSpan_rref_iff
#lint_axioms BoringMath.mul_eq_zero_of_and_false
#lint_axioms BoringMath.exists_matLeadingCol_eq_vecLeadingCol
#lint_axioms BoringMath.inRowSpan_matTail_of_subset
#lint_axioms BoringMath.rref_eq_of_subset_aux
#lint_axioms BoringMath.rref_eq_of_span_eq
#lint_axioms BoringMath.rref_eq_of_subset_nzCount
#lint_axioms BoringMath.rankOf
#lint_axioms BoringMath.nzCount_rref_snoc_eq_of_mem
#lint_axioms BoringMath.mem_of_nzCount_rref_snoc_eq
#lint_axioms BoringMath.inRowSpan_iff_rankOf_snoc_eq
#lint_axioms BoringMath.memRowSpanBool
#lint_axioms BoringMath.memRowSpanBool_true_iff
#lint_axioms BoringMath.memRowSpanDecidable
#lint_axioms BoringMath.spanContainsBool
#lint_axioms BoringMath.forall_mem_finRange
#lint_axioms BoringMath.spanContains_iff_rows
#lint_axioms BoringMath.spanContainsBool_true_iff
#lint_axioms BoringMath.spanContainsDecidable
#lint_axioms BoringMath.spanEqBool
#lint_axioms BoringMath.spanEqBool_true_iff
#lint_axioms BoringMath.spanEqDecidable
#lint_axioms BoringMath.rrefResidualBool
#lint_axioms BoringMath.rrefResidualBool_true_iff
#lint_axioms BoringMath.rrefMemRowSpanDecidable
#lint_axioms BoringMath.ratInv
#lint_axioms BoringMath.smokeA
#lint_axioms BoringMath.smokeB
#lint_axioms BoringMath.smokeC
#lint_axioms BoringMath.finFinset
#lint_axioms BoringMath.finSum
#lint_axioms BoringMath.sum_finFinset
#lint_axioms BoringMath.finSum_succ
#lint_axioms BoringMath.finSum_castSucc
#lint_axioms BoringMath.sum_finFinset_succ
#lint_axioms BoringMath.sum_finFinset_castSucc
#lint_axioms BoringMath.list_sum_eq_zero
#lint_axioms BoringMath.list_sum_congr
#lint_axioms BoringMath.list_sum_eq_single
#lint_axioms BoringMath.finSum_eq_zero
#lint_axioms BoringMath.finSum_zero
#lint_axioms BoringMath.list_countP_eq_zero
#lint_axioms BoringMath.finSum_congr
#lint_axioms BoringMath.finSum_eq_single
#lint_axioms BoringMath.sum_finFinset_eq_zero
#lint_axioms BoringMath.sum_finFinset_congr
#lint_axioms BoringMath.sum_finFinset_eq_single
end BoringMath
