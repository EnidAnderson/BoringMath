/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.List.Basic

/-!
# Finite sums over `Fin n` (list-based, choice-free)

`finSum n f` computes the finite sum `∑ i : Fin n, f i` as the list sum
over `List.finRange n`; the list-sum lemmas are proved by hand by `List`
induction because the `Finset` induction/congruence lemmas route through
`Classical.choice` at the pin.  Split out of
`BoringMath.FormalPeriods.FormalPeriods`.
-/

universe u

namespace BoringMath.FormalPeriods

/-! ## Finite sums over `Fin n` (list-based, choice-free) -/

-- Reference: the P.0.4 pin-run census (docs/AUDITS/2026-10-30-axiom-lint-pin-run.md):
-- the `Finset` congruence/induction lemmas (`Finset.sum_congr`, `sum_insert`,
-- `Finset.induction`, `sum_ite_eq`) route through `Classical.choice` at the pin,
-- so finite sums over `Fin n` are computed as list sums over `List.finRange`
-- (which lints CLEAN); Axler, LADR 4th ed., Ch. 2 (the standard basis is indexed
-- by `Fin n`).
/-- The finite sum `∑ i : Fin n, f i`, computed as the list sum over
`List.finRange n` (avoiding the choice-tainted `Finset` lemmas at the pin). -/
def finSum {M : Type u} [AddCommMonoid M] (n : ℕ) (f : Fin n → M) : M :=
  ((List.finRange n).map f).sum

-- Reference: Lean 4 core, `Init/Data/List/Basic.lean` (`List.map_cons`, `List.sum_cons`);
-- peel of the `rw [List.map_cons, List.sum_cons]` step in the list-sum inductions.
/-- Peel: the sum over a cons cell is the head summand plus the tail sum. -/
theorem listMapConsSum {N : Type u} [AddCommMonoid N] {α : Type} (f : α → N) (a : α)
    (l : List α) : ((a :: l).map f).sum = f a + (l.map f).sum :=
  Eq.trans (congrArg (fun w : List N => w.sum) (List.map_cons (f := f) (a := a) (l := l)))
    (List.sum_cons (a := f a) (l := l.map f))

-- Reference: Lean 4 core, `Init/Data/List/Basic.lean` (`List.map_nil`, `List.sum_nil`);
-- peel of the `rw [List.map_nil, List.sum_nil]` step in the list-sum inductions.
/-- Peel: the sum over the empty list is `0`. -/
theorem listMapNilSum {N : Type u} [AddCommMonoid N] {α : Type} (f : α → N) :
    (([] : List α).map f).sum = (0 : N) :=
  Eq.trans (congrArg (fun w : List N => w.sum) (List.map_nil (f := f))) (List.sum_nil (α := N))

-- Reference: Lean 4 core, `Init/Data/List/Basic.lean` (`List.map_nil`, `List.sum_nil`,
-- `add_zero`); peel of the nil case of `listSum_map_add`.
/-- Peel: the empty sum distributes over addition. -/
theorem listMapNilSumAdd {N : Type u} [AddCommMonoid N] {α : Type} (f g : α → N) :
    (([] : List α).map f).sum + (([] : List α).map g).sum = (0 : N) :=
  Eq.trans (congrArg (fun w => w + (([] : List α).map g).sum) (listMapNilSum f))
    (Eq.trans (congrArg (fun w => (0 : N) + w) (listMapNilSum g)) (add_zero 0))

-- Reference: Lean 4 core, `Init/Data/List/Basic.lean` (`List.map_nil`, `List.sum_nil`,
-- `mul_zero`); peel of the nil case of `listSum_map_mul_left`.
/-- Peel: a constant factor times the empty sum is `0`. -/
theorem listMapNilMul {R : Type u} [Semiring R] {α : Type} (c : R) (f : α → R) :
    c * (([] : List α).map f).sum = (0 : R) :=
  Eq.trans (congrArg (fun w => c * w) (listMapNilSum f)) (mul_zero c)

-- Reference: Lean 4 core, `Init/Data/List/Basic.lean` (`List.rec`); the list-sum
-- lemmas below are proved by hand by `List` induction (clean at the pin).
/-- List sums respect pointwise equality of the summands. -/
theorem listSum_congr {N : Type u} [AddCommMonoid N] {n : ℕ} (l : List (Fin n))
    (f g : Fin n → N) (h : ∀ a, f a = g a) : (l.map f).sum = (l.map g).sum := by
  induction l with
  | nil => exact Eq.trans (listMapNilSum f) (listMapNilSum g).symm
  | cons a l ih =>
      exact Eq.trans (listMapConsSum f a l)
        (Eq.trans (congrArg (fun w => w + (l.map f).sum) (h a))
          (Eq.trans (congrArg (fun w => g a + w) ih) (listMapConsSum g a l).symm))


-- Reference: Lean 4 core (`List.rec`, `add_add_add_comm`).
/-- List sums distribute over addition of the summands. -/
theorem listSum_map_add {N : Type u} [AddCommMonoid N] {n : ℕ} (l : List (Fin n))
    (f g : Fin n → N) :
    (l.map (fun a => f a + g a)).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => exact Eq.trans (listMapNilSum (fun a => f a + g a)) (listMapNilSumAdd f g).symm
  | cons a l ih =>
      exact Eq.trans (listMapConsSum (fun a => f a + g a) a l)
        (Eq.trans (congrArg (fun w => (f a + g a) + w) ih)
          (Eq.trans (add_add_add_comm (f a) (g a) ((l.map f).sum) ((l.map g).sum))
            (Eq.trans (congrArg (fun w => w + ((a :: l).map g).sum) (listMapConsSum f a l))
              (congrArg (fun w => (f a + (l.map f).sum) + w) (listMapConsSum g a l))).symm))

-- Reference: Lean 4 core (`List.rec`, `mul_add`).
/-- A constant factor pulls out of a list sum on the left. -/
theorem listSum_map_mul_left {R : Type u} [Semiring R] {n : ℕ} (l : List (Fin n))
    (c : R) (f : Fin n → R) : (l.map (fun a => c * f a)).sum = c * (l.map f).sum := by
  induction l with
  | nil => exact Eq.trans (listMapNilSum (fun a => c * f a)) (listMapNilMul c f).symm
  | cons a l ih =>
      exact Eq.trans (listMapConsSum (fun a => c * f a) a l)
        (Eq.trans (congrArg (fun w => (c * f a) + w) ih)
          (Eq.trans (mul_add c (f a) ((l.map f).sum)).symm
            (congrArg (fun w => c * w) (listMapConsSum f a l)).symm))

-- Reference: Lean 4 core (`List.rec`, `Pi.add_apply`).
/-- A list sum of functions, evaluated pointwise. -/
theorem listSum_apply {n m : ℕ} {M : Type u} [AddCommMonoid M] (l : List (Fin n))
    (f : Fin n → Fin m → M) (j : Fin m) :
    ((l.map f).sum) j = (l.map (fun a => f a j)).sum := by
  induction l with
  | nil =>
      exact Eq.trans (congrArg (fun w : Fin m → M => w j) (listMapNilSum f))
        (Eq.trans (Pi.zero_apply j) (listMapNilSum (fun a => f a j)).symm)
  | cons a l ih =>
      exact Eq.trans (congrArg (fun w : Fin m → M => w j) (listMapConsSum f a l))
        (Eq.trans (Pi.add_apply (f a) ((l.map f).sum) j)
          (Eq.trans (congrArg (fun w => f a j + w) ih)
            (listMapConsSum (fun a => f a j) a l).symm))

-- Reference: Lean 4 core (`List.rec`, `add_zero`).
/-- A list sum of zeros is zero. -/
theorem listSum_zero {N : Type u} [AddCommMonoid N] {n : ℕ} (l : List (Fin n)) :
    (l.map (fun _ => (0 : N))).sum = 0 := by
  induction l with
  | nil => exact listMapNilSum (fun _ => (0 : N))
  | cons a l ih =>
      exact Eq.trans (listMapConsSum (fun _ => (0 : N)) a l)
        (Eq.trans (congrArg (fun w => (0 : N) + w) ih) (add_zero 0))

-- Reference: line 165-169 (listSum_ite_zero, cons case with `j ≠ a`).
/-- Peel: the cons step of `listSum_ite_zero` when `j ≠ a`. -/
theorem listSumIteZeroConsNe {M : Type u} [AddCommMonoid M] {n : ℕ} {a j : Fin n}
    {l : List (Fin n)} {x : Fin n → M} (h : ¬ j = a)
    (ih : j ∉ l → (l.map (fun i => if j = i then x i else 0)).sum = 0)
    (hj : j ∉ a :: l) :
    ((a :: l).map (fun i => if j = i then x i else 0)).sum = 0 :=
  Eq.trans (listMapConsSum (fun i => if j = i then x i else 0) a l)
    (Eq.trans (congrArg (fun w => w + (l.map (fun i => if j = i then x i else 0)).sum)
        (ite_eq_right h))
      (Eq.trans (zero_add (l.map (fun i => if j = i then x i else 0)).sum)
        (ih (fun hjl => hj (List.mem_cons.mpr (Or.inr hjl))))))

-- Reference: Lean 4 core (`List.rec`, `List.nodup_cons`, `ite` laws).  The
-- membership of `j` is carried as a `Prop` hypothesis (never a `Decidable`
-- instance — the list-membership instance at the pin falls back to
-- `Classical.propDecidable`, which would taint the declaration).
/-- If `j ∉ l`, the sum of `if j = i then x i else 0` over `l` is `0`. -/
theorem listSum_ite_zero {M : Type u} [AddCommMonoid M] {n : ℕ} (l : List (Fin n))
    (j : Fin n) (x : Fin n → M) (hj : j ∉ l) :
    (l.map (fun i => if j = i then x i else 0)).sum = 0 := by
  revert hj
  induction l with
  | nil => intro _; exact listMapNilSum _
  | cons a l ih =>
      intro hj
      cases (inferInstance : Decidable (j = a)) with
      | isTrue h => exact absurd (List.mem_cons.mpr (Or.inl h)) hj
      | isFalse h => exact listSumIteZeroConsNe h ih hj

-- Reference: line 186-188 (listSum_ite_mem, cons case with `j = a`).
/-- Peel: the cons step of `listSum_ite_mem` when `j = a`. -/
theorem listSumIteMemConsEq {M : Type u} [AddCommMonoid M] {n : ℕ} {a j : Fin n}
    {l : List (Fin n)} {x : Fin n → M} (ha : a ∉ l) (h : j = a) :
    ((a :: l).map (fun i => if j = i then x i else 0)).sum = x j :=
  Eq.trans (listMapConsSum (fun i => if j = i then x i else 0) a l)
    (Eq.trans (congrArg (fun w => w + (l.map (fun i => if j = i then x i else 0)).sum)
        (ite_eq_left h))
      (Eq.trans (congrArg (fun w => x a + w)
          (listSum_ite_zero l j x (fun hjl => ha (Eq.subst h hjl))))
        (Eq.trans (add_zero (x a)) (congrArg x h).symm)))

-- Reference: line 189-190 (listSum_ite_mem, cons case with `j ≠ a`).
/-- Peel: the cons step of `listSum_ite_mem` when `j ≠ a`. -/
theorem listSumIteMemConsNe {M : Type u} [AddCommMonoid M] {n : ℕ} {a j : Fin n}
    {l : List (Fin n)} {x : Fin n → M} (hnd : l.Nodup) (h : ¬ j = a)
    (ih : l.Nodup → j ∈ l → (l.map (fun i => if j = i then x i else 0)).sum = x j)
    (hj : j ∈ a :: l) :
    ((a :: l).map (fun i => if j = i then x i else 0)).sum = x j :=
  Eq.trans (listMapConsSum (fun i => if j = i then x i else 0) a l)
    (Eq.trans (congrArg (fun w => w + (l.map (fun i => if j = i then x i else 0)).sum)
        (ite_eq_right h))
      (Eq.trans (zero_add (l.map (fun i => if j = i then x i else 0)).sum)
        (ih hnd ((List.mem_cons.mp hj).resolve_left h))))

-- Reference: Lean 4 core (`List.rec`, `List.nodup_cons`, `ite` laws).
/-- If `j ∈ l` with `l` nodup, the sum of `if j = i then x i else 0` over `l`
is `x j`. -/
theorem listSum_ite_mem {M : Type u} [AddCommMonoid M] {n : ℕ} (l : List (Fin n))
    (hnd : l.Nodup) (j : Fin n) (x : Fin n → M) (hj : j ∈ l) :
    (l.map (fun i => if j = i then x i else 0)).sum = x j := by
  revert hnd hj
  induction l with
  | nil => intro _ hj; exact absurd hj List.not_mem_nil
  | cons a l ih =>
      intro hnd hj
      have hl : a ∉ l ∧ l.Nodup := List.nodup_cons.mp hnd
      cases (inferInstance : Decidable (j = a)) with
      | isTrue h => exact listSumIteMemConsEq hl.1 h
      | isFalse h => exact listSumIteMemConsNe hl.2 h ih hj

-- Reference: Axler, LADR 4th ed., Ch. 2 (the standard basis spans `F^n`);
-- mathlib (`List.mem_finRange`, `List.nodup_finRange`).
/-- The single-occurrence sum over `Fin n`: `∑ i, (if j = i then x i else 0) = x j`. -/
theorem finSum_ite {M : Type u} [AddCommMonoid M] {n : ℕ} (j : Fin n) (x : Fin n → M) :
    finSum n (fun i => if j = i then x i else 0) = x j :=
  listSum_ite_mem (List.finRange n) (List.nodup_finRange n) j x (List.mem_finRange j)


-- Reference: mathlib (`RingHom` is an `AddMonoidHomClass`; `map_add`, `map_zero`);
-- proved by hand by `List` induction (the `Finset` version `map_sum` is
-- choice-tainted at the pin).
/-- A ring homomorphism commutes with list sums. -/
theorem mapListSum {R L : Type u} [Semiring R] [Semiring L] (φ : R →+* L) {k : ℕ}
    (f : Fin k → R) (l : List (Fin k)) :
    φ ((l.map f).sum) = (l.map (fun i => φ (f i))).sum := by
  induction l with
  | nil =>
      exact Eq.trans (congrArg φ (listMapNilSum f))
        (Eq.trans (map_zero φ) (listMapNilSum (fun i => φ (f i))).symm)
  | cons a l ih =>
      exact Eq.trans (congrArg φ (listMapConsSum f a l))
        (Eq.trans (map_add φ (f a) ((l.map f).sum))
          (Eq.trans (congrArg (fun w => φ (f a) + w) ih)
            (listMapConsSum (fun i => φ (f i)) a l).symm))


end BoringMath.FormalPeriods
