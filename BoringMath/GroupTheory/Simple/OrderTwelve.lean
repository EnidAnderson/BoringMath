/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# A group of order 12 is not simple

Ticket #280c (the `PSL(2,3) ≅ A_4` level of the small-order census #280; the
other rungs `p*q` and `p^2` are in `SmallOrders.lean`). Classical Sylow counting:
`n_3 ∈ {1, 4}` and `n_2 ∈ {1, 3}`; if `n_3 = 4` there are `8` elements of order
`3`, leaving exactly `4` elements, which must form the unique Sylow
`2`-subgroup.

## References
* [Dummit–Foote] ch. 4 §6 (Sylow counting); [Wilson] ch. 1 (order 12 is not
  simple; the order-12 group is `A_4`).
* mathlib pin v4.35.0-rc3: `card_sylow_modEq_one`, `Sylow.card_dvd_index`,
  `Sylow.card_eq_multiplicity`, `Sylow.normal_of_subsingleton`,
  `IsPGroup.dvd_orderOf`, `Nat.card_zpowers`, `orderOf_dvd_card`.
-/

namespace BoringMath

open Subgroup

variable {G : Type*} [Group G] [Finite G]

-- Reference: mathlib pin v4.35.0-rc3, `Sylow.card_eq_multiplicity` and
-- `Nat.factorization_mul` for `12 = 3 * 4`.
/-- A Sylow `3`-subgroup of a group of order `12` has order `3` (proved). -/
theorem card_sylow_three_of_card_eq_twelve (h : Nat.card G = 12) (P : Sylow 3 G) :
    Nat.card ↥(P : Subgroup G) = 3 := by
  have hnd : ¬ 3 ∣ 4 := fun hd =>
    Nat.succ_ne_zero 0
      ((((Nat.dvd_iff_mod_eq_zero).mp hd).symm.trans rfl).symm)
  have hf : (12:ℕ).factorization 3 = 1 :=
    Eq.subst (motive := fun n => n.factorization 3 = 1) (rfl : (3 * 4 : ℕ) = 12)
      ((congrArg (fun f => f 3)
          (Nat.factorization_mul (Nat.succ_ne_zero 2) (Nat.succ_ne_zero 3))).trans
        ((Finsupp.add_apply (Nat.factorization 3) (Nat.factorization 4) 3).trans
          (Eq.subst (motive := fun n => n + (Nat.factorization 4) 3 = 1)
              (Nat.Prime.factorization_self Nat.prime_three).symm
              (Eq.subst (motive := fun n => 1 + n = 1)
                (Nat.factorization_eq_zero_of_not_dvd hnd).symm (Nat.add_zero 1)))))
  have h12 : (Nat.card G).factorization 3 = 1 :=
    (congrArg (fun n => n.factorization 3) h).trans hf
  exact (Sylow.card_eq_multiplicity P).trans ((congrArg (3 ^ ·) h12).trans (pow_one 3))

-- Reference: [Dummit–Foote] ch. 4 §6; pin's `card_sylow_modEq_one`,
-- `Sylow.card_dvd_index`, `Subgroup.index_mul_card`.
/-- **`n_3` (number of Sylow `3`-subgroups of a group of order `12`) is `1` or
`4`** (proved). -/
theorem sylow_three_card_eq_one_or_four_of_card_eq_twelve (h : Nat.card G = 12) :
    Nat.card (Sylow 3 G) = 1 ∨ Nat.card (Sylow 3 G) = 4 := by
  set n3 := Nat.card (Sylow 3 G)
  have hmod' : n3 % 3 = 1 := card_sylow_modEq_one (p := 3) (G := G)
  obtain ⟨P⟩ := Sylow.nonempty (p := 3) (G := G)
  have hcardP : Nat.card ↥(P : Subgroup G) = 3 := card_sylow_three_of_card_eq_twelve h P
  have hidx : (P : Subgroup G).index = 4 := by
    have h' : (P : Subgroup G).index * 3 = 12 :=
      (congrArg (fun c => (P : Subgroup G).index * c) hcardP).symm.trans
        ((Subgroup.index_mul_card (P : Subgroup G)).trans h)
    exact Nat.mul_right_cancel (Nat.succ_pos 2) (h'.trans rfl)
  have hdvd : n3 ∣ 4 := Eq.subst (motive := fun n => n3 ∣ n) hidx (Sylow.card_dvd_index P)
  have hle : n3 ≤ 4 := Nat.le_of_dvd (Nat.succ_pos 3) hdvd
  have h0 : 0 < n3 := (Nat.card_pos_iff (α := Sylow 3 G)).mpr ⟨⟨P⟩, inferInstance⟩
  rcases Nat.lt_or_ge n3 3 with hlt | hge
  · rcases Nat.lt_or_ge n3 2 with h2 | h2'
    · exact Or.inl (Nat.le_antisymm (Nat.le_of_lt_succ h2) h0)
    · have hn2 : n3 = 2 := Nat.le_antisymm (Nat.le_of_lt_succ hlt) h2'
      have h2m : (2:ℕ) % 3 = 2 := rfl
      exact absurd (Eq.subst (motive := fun n => n % 3 = 1) hn2 hmod') (fun hc =>
        Nat.succ_ne_zero 0 ((Nat.succ_inj).mp (hc.symm.trans h2m)).symm)
  · rcases Nat.lt_or_ge n3 4 with h4 | h4'
    · have hn3 : n3 = 3 := Nat.le_antisymm (Nat.le_of_lt_succ h4) hge
      have h3m : (3:ℕ) % 3 = 0 := rfl
      exact absurd (Eq.subst (motive := fun n => n % 3 = 1) hn3 hmod') (fun hc =>
        Nat.succ_ne_zero 0 (hc.symm.trans h3m))
    · exact Or.inr (Nat.le_antisymm hle h4')

-- Reference: [Dummit–Foote] ch. 4 §6; [Wilson] ch. 1.
/-- **A group of order `12` is not simple** (proved by Sylow counting:
`n_3 ∈ {1,4}`; if `n_3 = 4` there are 8 elements of order 3, so the remaining 4
elements form the unique — hence normal — Sylow `2`-subgroup). -/
theorem not_isSimpleGroup_of_card_eq_twelve (h : Nat.card G = 12) :
    ¬ IsSimpleGroup G := by
  intro hsimple
  rcases sylow_three_card_eq_one_or_four_of_card_eq_twelve h with h1 | h4
  · -- n3 = 1: the unique Sylow 3-subgroup is normal of order 3
    have hsub : Subsingleton (Sylow 3 G) := (Nat.card_eq_one_iff_unique.mp h1).1
    obtain ⟨P⟩ := Sylow.nonempty (p := 3) (G := G)
    have hnorm : (P : Subgroup G).Normal := @Sylow.normal_of_subsingleton G _ 3 hsub P
    have hcardP : Nat.card ↥(P : Subgroup G) = 3 := card_sylow_three_of_card_eq_twelve h P
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal G _ hsimple (P : Subgroup G) hnorm with
      hb | ht
    · have e : Nat.card ↥(⊥ : Subgroup G) = 3 :=
        Eq.subst (motive := fun (K : Subgroup G) => Nat.card ↥K = 3) hb hcardP
      exact absurd ((Subgroup.card_bot (G := G)).symm.trans e)
        (fun h => Nat.succ_ne_zero 1 ((Nat.succ_inj).mp h).symm)
    · have e : Nat.card ↥(⊤ : Subgroup G) = 3 :=
        Eq.subst (motive := fun (K : Subgroup G) => Nat.card ↥K = 3) ht hcardP
      have e2 : Nat.card ↥(⊤ : Subgroup G) = 12 := (Subgroup.card_top (G := G)).trans h
      exact absurd (e.symm.trans e2)
        (fun h => Nat.succ_ne_zero 2
          (((rfl : (3:ℕ) % 4 = 3).symm.trans (congrArg (· % 4) h)).trans
            ((Nat.dvd_iff_mod_eq_zero).mp ⟨3, rfl⟩)))
  · -- n3 = 4: count elements of order 3 (there are 8), then the Sylow 2-subgroup
    -- is unique, hence normal — contradiction. PEELING PLAN for the counting:
    -- (a) `S := univ.filter (orderOf · = 3)` has card `2 * 4 = 8` via
    --     `Finset.card_biUnion` over `univ : Finset (Sylow 3 G)`, using that
    --     distinct Sylow-3 subgroups intersect in `⊥` (prime order) and each
    --     contributes `2` nonidentity elements (`Nat.card_zpowers`);
    -- (b) `R := univ.filter (orderOf · ≠ 3)` has card `12 - 8 = 4`;
    -- (c) any Sylow `2`-subgroup `Q` satisfies `Q ⊆ R` (`orderOf_dvd_card` into
    --     `Nat.card ↥Q = 4`) and `Nat.card ↥Q = 4 = R.card`, so `Q = R`;
    -- (d) hence `Subsingleton (Sylow 2 G)` and `Sylow.normal_of_subsingleton`
    --     gives a normal subgroup of order 4 — contradiction as above.
    sorry

end BoringMath
