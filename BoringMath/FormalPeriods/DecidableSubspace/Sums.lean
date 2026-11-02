/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Init
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
/-!
# Choice-free finite sums over `Fin m` and list-sum lemmas (P.2.3, part 1)

Piece 1 of `BoringMath.FormalPeriods.DecidableSubspace`: the hand-built
finset `finFinset` of `Fin m`, the list sum `finSum`, the conversions between
`Finset.sum` over `finFinset` and `finSum`, and the choice-free list-sum
lemmas used across the row-span development.
-/
universe u
namespace BoringMath
open BigOperators
variable {K : Type u} [Field K] {m n k p : ℕ}
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
end BoringMath
