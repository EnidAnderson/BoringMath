/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Group.Action.Defs

/-!
# The choice-free `List.sum` toolbox (P.2.2, part 3)

Piece 3 of `BoringMath.FormalPeriods.KernelImage`: the `List.sum` lemmas
(distributivity, congruence, `ite`-sums, splitting at a member) proved
by structural induction on `List`, since the mathlib `Finset`
big-operator API is `Classical.choice`-tainted at the pin v4.35.0-rc3.
-/

universe u

namespace BoringMath

variable {K : Type u} [Field K] {m n : ℕ}

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

end BoringMath
