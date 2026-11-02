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

-- Reference: mathlib pin v4.35.0-rc3, `Sylow.card_eq_multiplicity` and
-- `Nat.factorization_mul` for `12 = 4 * 3` (`(4).factorization 2 = 2` via
-- `Nat.Prime.factorization_pow`, `(3).factorization 2 = 0`).
/-- A Sylow `2`-subgroup of a group of order `12` has order `4` (proved). -/
theorem card_sylow_two_of_card_eq_twelve (h : Nat.card G = 12) (Q : Sylow 2 G) :
    Nat.card ↥(Q : Subgroup G) = 4 := by
  have hnd : ¬ 2 ∣ 3 := fun hd =>
    Nat.succ_ne_zero 0 ((((Nat.dvd_iff_mod_eq_zero).mp hd).symm.trans rfl).symm)
  have hf4 : (4:ℕ).factorization 2 = 2 := Eq.subst (motive := fun n => n.factorization 2 = 2)
    (rfl : (2 ^ 2 : ℕ) = 4) (Nat.factorization_pow_self (n := 2) Nat.prime_two)
  have hf3 : (3:ℕ).factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd hnd
  have hf : (12:ℕ).factorization 2 = 2 :=
    Eq.subst (motive := fun n => n.factorization 2 = 2) (rfl : (4 * 3 : ℕ) = 12)
      ((congrArg (fun f => f 2)
          (Nat.factorization_mul (Nat.succ_ne_zero 3) (Nat.succ_ne_zero 2))).trans
        ((Finsupp.add_apply (Nat.factorization 4) (Nat.factorization 3) 2).trans
          (Eq.subst (motive := fun n => n + (Nat.factorization 3) 2 = 2) hf4.symm
            (Eq.subst (motive := fun n => 2 + n = 2) hf3.symm (Nat.add_zero 2)))))
  have h12 : (Nat.card G).factorization 2 = 2 :=
    (congrArg (fun n => n.factorization 2) h).trans hf
  exact (Sylow.card_eq_multiplicity Q).trans
    ((congrArg (2 ^ ·) h12).trans (pow_two 2))

-- Reference: [Dummit–Foote] ch. 4 §6; two distinct subgroups of prime order
-- intersect trivially (the intersection's cardinality divides the prime).
-- pin: `Subgroup.card_dvd_of_le`, `Subgroup.eq_of_le_of_card_ge`,
-- `Nat.Prime.eq_one_or_self_of_dvd`, `Sylow.ext`.
/-- Distinct Sylow `3`-subgroups of a group of order `12` intersect in `⊥`
(proved). -/
theorem sylow_three_inf_eq_bot_of_ne (h : Nat.card G = 12) {P Q : Sylow 3 G}
    (hPQ : P ≠ Q) : (P : Subgroup G) ⊓ (Q : Subgroup G) = ⊥ := by
  have hcardP : Nat.card ↥(P : Subgroup G) = 3 := card_sylow_three_of_card_eq_twelve h P
  have hcardQ : Nat.card ↥(Q : Subgroup G) = 3 := card_sylow_three_of_card_eq_twelve h Q
  have hdvd : Nat.card ↥((P : Subgroup G) ⊓ (Q : Subgroup G)) ∣ 3 :=
    Eq.subst (motive := fun n => Nat.card ↥((P : Subgroup G) ⊓ (Q : Subgroup G)) ∣ n) hcardP
      (Subgroup.card_dvd_of_le inf_le_left)
  rcases (Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three _ hdvd) with e1 | e3
  · have hle : Nat.card ↥((P : Subgroup G) ⊓ (Q : Subgroup G)) ≤
        Nat.card ↥(⊥ : Subgroup G) :=
      Eq.subst (motive := fun n => Nat.card ↥((P : Subgroup G) ⊓ (Q : Subgroup G)) ≤ n)
        (Subgroup.card_bot (G := G)).symm (Nat.le_of_eq e1)
    exact (Subgroup.eq_of_le_of_card_ge bot_le hle).symm
  · have hleP : Nat.card ↥(P : Subgroup G) ≤
        Nat.card ↥((P : Subgroup G) ⊓ (Q : Subgroup G)) :=
      Eq.subst (motive := fun n => n ≤ Nat.card ↥((P : Subgroup G) ⊓ (Q : Subgroup G)))
        hcardP.symm (Nat.le_of_eq e3.symm)
    have hleQ : Nat.card ↥(Q : Subgroup G) ≤
        Nat.card ↥((P : Subgroup G) ⊓ (Q : Subgroup G)) :=
      Eq.subst (motive := fun n => n ≤ Nat.card ↥((P : Subgroup G) ⊓ (Q : Subgroup G)))
        hcardQ.symm (Nat.le_of_eq e3.symm)
    exact absurd (Sylow.ext ((Subgroup.eq_of_le_of_card_ge inf_le_left hleP).symm.trans
        (Subgroup.eq_of_le_of_card_ge inf_le_right hleQ))) hPQ


set_option linter.style.haveILetI false in
-- Reference: [Dummit–Foote] ch. 4 §6; [Wilson] ch. 1.
/-- **A group of order `12` is not simple** (proved by Sylow counting:
`n_3 ∈ {1,4}`; if `n_3 = 4` there are 8 elements of order 3, so the remaining 4
elements form the unique — hence normal — Sylow `2`-subgroup). -/
theorem not_isSimpleGroup_of_card_eq_twelve (h : Nat.card G = 12) :
    ¬ IsSimpleGroup G := by
  intro hsimple
  classical
  letI := Fintype.ofFinite G
  letI := Fintype.ofFinite (Sylow 3 G)
  letI := Fintype.ofFinite (Sylow 2 G)
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
  · -- n3 = 4: count elements of order 3 (8 of them); the remaining 4 elements
    -- form the unique Sylow 2-subgroup, which is then normal — contradiction.
    have hcard3 : ∀ P : Sylow 3 G, Nat.card ↥(P : Subgroup G) = 3 :=
      fun P => card_sylow_three_of_card_eq_twelve h P
    have hnd34 : ¬ 3 ∣ 4 := fun hd =>
      Nat.succ_ne_zero 0 ((((Nat.dvd_iff_mod_eq_zero).mp hd).symm.trans rfl).symm)
    have hnd23 : ¬ 2 ∣ 3 := fun hd =>
      Nat.succ_ne_zero 0 ((((Nat.dvd_iff_mod_eq_zero).mp hd).symm.trans rfl).symm)
    have hf2 : (12:ℕ).factorization 2 = 2 :=
      Eq.subst (motive := fun n => n.factorization 2 = 2) (rfl : (4 * 3 : ℕ) = 12)
        ((congrArg (fun f => f 2)
            (Nat.factorization_mul (Nat.succ_ne_zero 3) (Nat.succ_ne_zero 2))).trans
          ((Finsupp.add_apply (Nat.factorization 4) (Nat.factorization 3) 2).trans
            (Eq.subst (motive := fun n => n + (Nat.factorization 3) 2 = 2)
                (Eq.subst (motive := fun n => n.factorization 2 = 2) (rfl : (2 ^ 2 : ℕ) = 4)
                  (Nat.factorization_pow_self (n := 2) Nat.prime_two)).symm
                (Eq.subst (motive := fun n => 2 + n = 2)
                  (Nat.factorization_eq_zero_of_not_dvd hnd23).symm (Nat.add_zero 2)))))
    have hcard2 : ∀ Q : Sylow 2 G, Nat.card ↥(Q : Subgroup G) = 4 := by
      intro Q
      have h12 : (Nat.card G).factorization 2 = 2 :=
        (congrArg (fun n => n.factorization 2) h).trans hf2
      exact (Sylow.card_eq_multiplicity Q).trans ((congrArg (2 ^ ·) h12).trans (pow_two 2))
    -- the order-3 elements are exactly the nonidentity elements of the Sylow 3s
    have h_eq : (Finset.univ.filter fun x : G => orderOf x = 3) =
        (Finset.univ : Finset (Sylow 3 G)).biUnion
          (fun P => Finset.univ.filter fun x : G => x ∈ (P : Subgroup G) ∧ x ≠ 1) := by
      apply Finset.ext
      intro x
      refine ⟨?_, ?_⟩
      · intro hx
        have hx3 : orderOf x = 3 := (Finset.mem_filter.mp hx).2
        have hx1 : x ≠ 1 := fun hc =>
          Nat.succ_ne_zero 1 ((Nat.succ_inj).mp
            (((congrArg orderOf hc).trans orderOf_one).symm.trans hx3)).symm
        have hpg : IsPGroup 3 (Subgroup.zpowers x) :=
          IsPGroup.of_card (n := 1)
            ((Nat.card_zpowers x).trans (hx3.trans (pow_one 3).symm))
        obtain ⟨P, hP⟩ := hpg.exists_le_sylow
        exact Finset.mem_biUnion.mpr ⟨P, Finset.mem_univ _,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hP (Subgroup.mem_zpowers x), hx1⟩⟩
      · intro hx
        obtain ⟨P, _, hxP⟩ := Finset.mem_biUnion.mp hx
        have hxP' := Finset.mem_filter.mp hxP
        have hdvd : orderOf x ∣ 3 :=
          Eq.subst (motive := fun n => orderOf x ∣ n) (hcard3 P)
            (Eq.subst (motive := fun n => n ∣ Nat.card ↥(P : Subgroup G))
              (Subgroup.orderOf_mk x hxP'.2.1)
              (orderOf_dvd_natCard (⟨x, hxP'.2.1⟩ : ↥(P : Subgroup G))))
        rcases Nat.prime_three.eq_one_or_self_of_dvd _ hdvd with h' | h'
        · exact absurd (orderOf_eq_one_iff.mp h') hxP'.2.2
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h'⟩
    -- each fiber has card 2
    have hfiber : ∀ P : Sylow 3 G,
        (Finset.univ.filter fun x : G => x ∈ (P : Subgroup G) ∧ x ≠ 1).card = 2 := by
      intro P
      have hs : (Finset.univ.filter fun x : G => x ∈ (P : Subgroup G)).card = 3 :=
        (Fintype.card_subtype (fun x => x ∈ (P : Subgroup G))).symm.trans
          ((Nat.card_eq_fintype_card (α := ↥(P : Subgroup G))).symm.trans (hcard3 P))
      have hfib : (Finset.univ.filter fun x : G => x ∈ (P : Subgroup G) ∧ x ≠ 1) =
          (Finset.univ.filter fun x : G => x ∈ (P : Subgroup G)).filter (fun x => x ≠ 1) :=
        (Finset.filter_filter _ _ _).symm
      have hsplit := Finset.card_filter_add_card_filter_not
        (s := Finset.univ.filter fun x : G => x ∈ (P : Subgroup G)) (fun x => x ≠ 1)
      have honeq : (Finset.univ.filter fun x : G => x ∈ (P : Subgroup G)).filter
          (fun x => ¬ x ≠ 1) = {1} := by
        apply Finset.ext
        intro x
        refine ⟨?_, ?_⟩
        · intro hx
          exact Finset.mem_singleton.mpr (not_not.mp (Finset.mem_filter.mp hx).2)
        · intro hx
          refine Finset.mem_filter.mpr ⟨?_, not_not.mpr (Finset.mem_singleton.mp hx)⟩
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          exact Eq.subst (motive := fun y => y ∈ (P : Subgroup G))
            (Finset.mem_singleton.mp hx).symm (Subgroup.one_mem _)
      have hone : ((Finset.univ.filter fun x : G => x ∈ (P : Subgroup G)).filter
          fun x => ¬ x ≠ 1).card = 1 :=
        (congrArg Finset.card honeq).trans (Finset.card_singleton 1)
      have hsum : ((Finset.univ.filter fun x : G => x ∈ (P : Subgroup G)).filter
          fun x => x ≠ 1).card + 1 = 3 := by
        have e : ((Finset.univ.filter fun x : G => x ∈ (P : Subgroup G)).filter
            fun x => x ≠ 1).card + 1 =
            ((Finset.univ.filter fun x : G => x ∈ (P : Subgroup G)).filter
              fun x => x ≠ 1).card +
              ((Finset.univ.filter fun x : G => x ∈ (P : Subgroup G)).filter
                fun x => ¬ x ≠ 1).card :=
          congrArg ((((Finset.univ.filter fun x : G => x ∈ (P : Subgroup G)).filter
              fun x => x ≠ 1).card + ·)) hone.symm
        exact e.trans (hsplit.trans hs)
      exact Eq.subst (motive := fun t => t.card = 2) hfib.symm
        (Nat.add_right_cancel (hsum.trans rfl))
    -- distinct Sylow 3s share no nonidentity element
    have hdisj : ((Finset.univ : Finset (Sylow 3 G)) : Set (Sylow 3 G)).PairwiseDisjoint
        (fun P => Finset.univ.filter fun x : G => x ∈ (P : Subgroup G) ∧ x ≠ 1) := by
      intro P _ Q _ hne
      refine Finset.disjoint_left.mpr fun x hxP hxQ => ?_
      have hxP' := Finset.mem_filter.mp hxP
      have hxQ' := Finset.mem_filter.mp hxQ
      have hord : orderOf x = 3 := by
        have hdvd : orderOf x ∣ 3 :=
          Eq.subst (motive := fun n => orderOf x ∣ n) (hcard3 P)
            (Eq.subst (motive := fun n => n ∣ Nat.card ↥(P : Subgroup G))
              (Subgroup.orderOf_mk x hxP'.2.1)
              (orderOf_dvd_natCard (⟨x, hxP'.2.1⟩ : ↥(P : Subgroup G))))
        rcases Nat.prime_three.eq_one_or_self_of_dvd _ hdvd with h' | h'
        · exact absurd (orderOf_eq_one_iff.mp h') hxP'.2.2
        · exact h'
      have hcardz : Nat.card ↥(Subgroup.zpowers x) = 3 := (Nat.card_zpowers x).trans hord
      have e1 : Subgroup.zpowers x = (P : Subgroup G) :=
        Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxP'.2.1)
          (Eq.le ((hcard3 P).trans hcardz.symm))
      have e2 : Subgroup.zpowers x = (Q : Subgroup G) :=
        Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxQ'.2.1)
          (Eq.le ((hcard3 Q).trans hcardz.symm))
      exact hne (Sylow.ext (e1.symm.trans e2))
    have hcardB : ((Finset.univ : Finset (Sylow 3 G)).biUnion
        (fun P => Finset.univ.filter fun x : G => x ∈ (P : Subgroup G) ∧ x ≠ 1)).card
          = 8 := by
      have e := Finset.card_biUnion hdisj
      have e5 : (Finset.univ : Finset (Sylow 3 G)).card = 4 :=
        Finset.card_univ.trans ((Nat.card_eq_fintype_card (α := Sylow 3 G)).symm.trans h4)
      have hsum : (∑ P ∈ (Finset.univ : Finset (Sylow 3 G)),
          (Finset.univ.filter fun x : G => x ∈ (P : Subgroup G) ∧ x ≠ 1).card) = 8 :=
        ((Finset.sum_congr rfl fun P _ => hfiber P).trans
          (Finset.sum_const (b := 2))).trans
          (Eq.subst (motive := fun n => n • (2:ℕ) = 8) e5.symm rfl)
      exact e.trans hsum
    have h8 : (Finset.univ.filter fun x : G => orderOf x = 3).card = 8 :=
      Eq.subst (motive := fun s => s.card = 8) h_eq.symm hcardB
    -- the remaining 4 elements
    have hR : (Finset.univ.filter fun x : G => orderOf x ≠ 3).card = 4 := by
      have e := Finset.card_filter_add_card_filter_not
        (s := Finset.univ) (fun x : G => orderOf x = 3)
      have hu : (Finset.univ : Finset G).card = 12 :=
        Finset.card_univ.trans ((Nat.card_eq_fintype_card (α := G)).symm.trans h)
      have e' : 8 + (Finset.univ.filter fun x : G => ¬ orderOf x = 3).card = 12 :=
        Eq.subst (motive := fun n =>
          n + (Finset.univ.filter fun x : G => ¬ orderOf x = 3).card = 12) h8 (e.trans hu)
      exact Nat.add_left_cancel (e'.trans rfl)
    -- every Sylow 2-subgroup is contained in the remainder, hence equals it
    have hQR : ∀ Q : Sylow 2 G, Finset.univ.filter (fun x : G => x ∈ (Q : Subgroup G)) ⊆
        Finset.univ.filter (fun x : G => orderOf x ≠ 3) := by
      intro Q x hx
      have hxQ : x ∈ (Q : Subgroup G) := (Finset.mem_filter.mp hx).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      intro h3
      have hdvd : orderOf x ∣ 4 :=
        Eq.subst (motive := fun n => orderOf x ∣ n) (hcard2 Q)
          (Eq.subst (motive := fun n => n ∣ Nat.card ↥(Q : Subgroup G))
            (Subgroup.orderOf_mk x hxQ)
            (orderOf_dvd_natCard (⟨x, hxQ⟩ : ↥(Q : Subgroup G))))
      exact hnd34 (Eq.subst (motive := fun n => n ∣ 4) h3 hdvd)
    have hcardQf : ∀ Q : Sylow 2 G,
        (Finset.univ.filter fun x : G => x ∈ (Q : Subgroup G)).card = 4 := by
      intro Q
      exact (Fintype.card_subtype (fun x => x ∈ (Q : Subgroup G))).symm.trans
        ((Nat.card_eq_fintype_card (α := ↥(Q : Subgroup G))).symm.trans (hcard2 Q))
    have hsub2 : Subsingleton (Sylow 2 G) := ⟨fun Q1 Q2 => by
      have e1 : Finset.univ.filter (fun x : G => x ∈ (Q1 : Subgroup G)) =
          Finset.univ.filter (fun x : G => orderOf x ≠ 3) :=
        Finset.eq_of_subset_of_card_le (hQR Q1) (hR.le.trans (Eq.le (hcardQf Q1).symm))
      have e2 : Finset.univ.filter (fun x : G => x ∈ (Q2 : Subgroup G)) =
          Finset.univ.filter (fun x : G => orderOf x ≠ 3) :=
        Finset.eq_of_subset_of_card_le (hQR Q2) (hR.le.trans (Eq.le (hcardQf Q2).symm))
      have hmem : ∀ x : G, x ∈ (Q1 : Subgroup G) ↔ x ∈ (Q2 : Subgroup G) := by
        intro x
        refine ⟨fun hx => ?_, fun hx => ?_⟩
        · have h1 : x ∈ Finset.univ.filter (fun x : G => x ∈ (Q1 : Subgroup G)) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
          have h2 : x ∈ Finset.univ.filter (fun x : G => orderOf x ≠ 3) :=
            Eq.subst (motive := fun s => x ∈ s) e1 h1
          have h3 : x ∈ Finset.univ.filter (fun x : G => x ∈ (Q2 : Subgroup G)) :=
            Eq.subst (motive := fun s => x ∈ s) e2.symm h2
          exact (Finset.mem_filter.mp h3).2
        · have h1 : x ∈ Finset.univ.filter (fun x : G => x ∈ (Q2 : Subgroup G)) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
          have h2 : x ∈ Finset.univ.filter (fun x : G => orderOf x ≠ 3) :=
            Eq.subst (motive := fun s => x ∈ s) e2 h1
          have h3 : x ∈ Finset.univ.filter (fun x : G => x ∈ (Q1 : Subgroup G)) :=
            Eq.subst (motive := fun s => x ∈ s) e1.symm h2
          exact (Finset.mem_filter.mp h3).2
      exact Sylow.ext (Subgroup.ext hmem)⟩
    obtain ⟨Q⟩ := Sylow.nonempty (p := 2) (G := G)
    have hnorm2 : (Q : Subgroup G).Normal := @Sylow.normal_of_subsingleton G _ 2 hsub2 Q
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal G _ hsimple (Q : Subgroup G) hnorm2 with
      hb | ht
    · have e : Nat.card ↥(⊥ : Subgroup G) = 4 :=
        Eq.subst (motive := fun K : Subgroup G => Nat.card ↥K = 4) hb (hcard2 Q)
      exact absurd ((Subgroup.card_bot (G := G)).symm.trans e) (fun h =>
        Nat.succ_ne_zero 0
          (((rfl : (1:ℕ) % 2 = 1).symm.trans (congrArg (· % 2) h)).trans
            ((Nat.dvd_iff_mod_eq_zero).mp ⟨2, rfl⟩)))
    · have e : Nat.card ↥(⊤ : Subgroup G) = 4 :=
        Eq.subst (motive := fun K : Subgroup G => Nat.card ↥K = 4) ht (hcard2 Q)
      have e2 : Nat.card ↥(⊤ : Subgroup G) = 12 := (Subgroup.card_top (G := G)).trans h
      exact absurd (e.symm.trans e2) (fun h =>
        Nat.succ_ne_zero 0
          (((rfl : (4:ℕ) % 3 = 1).symm.trans (congrArg (· % 3) h)).trans
            ((Nat.dvd_iff_mod_eq_zero).mp ⟨4, rfl⟩)))

end BoringMath
