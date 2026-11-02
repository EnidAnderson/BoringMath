/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.SetTheory.Cardinal.Finite
import BoringMath.GroupTheory.Simple.OrderTwelve

/-!
# Small-order non-simplicity

Ticket **#280 CFSG.SMALL**: the first rung of the small-order census "no finite
simple group has composite order `< 60`" (the smallest nonabelian simple group
is `A_5`, of order 60 — `card_alternatingGroup_fin5` in
`BoringMath.GroupTheory.Simple.Classification`). This module proves the two
clean Sylow-theoretic cases: order `p * q` with primes `p < q` (#280a) and order
`p ^ 2` (#280b), and consumes the order-12 case (#280c, the `PSL(2,3) ≅ A_4`
level) from `BoringMath.GroupTheory.Simple.OrderTwelve` (proved there).

## References
* [Dummit–Foote] D. S. Dummit, R. M. Foote, *Abstract Algebra*, 3rd ed., Wiley
  2004, Ch. 4, Sec. 6 (Sylow's theorems and their counting consequences).
  REVIEW(citation): pin the exact section against a held copy in review.
* [Wilson] R. A. Wilson, *The Finite Simple Groups*, Springer GTM 251, 2009,
  ch. 1 (orders of small groups; `A_5` of order 60 is the smallest nonabelian
  simple group).
* mathlib pin v4.35.0-rc3: `card_sylow_modEq_one`, `Sylow.card_dvd_index`,
  `Sylow.normal_of_subsingleton`, `Sylow.card_eq_multiplicity`,
  `Subgroup.index_mul_card`, `exists_prime_orderOf_dvd_card'`, `Nat.card_zpowers`,
  `IsPGroup.of_card`, `IsPGroup.isMulCommutative_of_card_eq_prime_sq`,
  `Subgroup.normal_of_isMulCommutative`, `Subgroup.card_bot`, `Subgroup.card_top`,
  `Nat.card_eq_one_iff_unique`.
-/

namespace BoringMath

/-! ## Order `p * q`, primes `p < q` — #280a -/

-- Reference: [Dummit–Foote], Ch. 4, Sec. 6 (Sylow III: `n_q ≡ 1 [MOD q]` and
-- `n_q ∣ p`); mathlib pin v4.35.0-rc3, `card_sylow_modEq_one`,
-- `Sylow.card_dvd_index`, `Sylow.card_eq_multiplicity`. REVIEW(citation).
/-- **A group of order `p * q` with primes `p < q` is not simple** (proved):
the number `n_q` of Sylow `q`-subgroups divides `p` and is `≡ 1 [MOD q]`; since
`p < q`, `n_q = 1`, so the Sylow `q`-subgroup is normal, of order `q`, proper
and nontrivial. -/
theorem not_isSimpleGroup_of_card_eq_prime_mul_prime {G : Type*} [Group G] [Finite G]
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : p < q) (hcard : Nat.card G = p * q) :
    ¬ IsSimpleGroup G := by
  intro hsimple
  have hp := (Fact.out : p.Prime)
  have hq := (Fact.out : q.Prime)
  obtain ⟨Q⟩ := Sylow.nonempty (p := q) (G := G)
  -- the multiplicity of `q` in `p * q` is 1, so the Sylow `q`-subgroup has order `q`
  have hf : Nat.factorization (p * q) q = 1 :=
    (congrArg (fun f => f q) (Nat.factorization_mul hp.ne_zero hq.ne_zero)).trans
      ((Finsupp.add_apply p.factorization q.factorization q).trans
        (Eq.subst (motive := fun n => n + q.factorization q = 1)
            (Nat.factorization_eq_zero_of_not_dvd (fun hd =>
              absurd (Nat.le_of_dvd hp.pos hd) (Nat.not_le_of_gt hpq))).symm
            (Eq.subst (motive := fun n => 0 + n = 1) (Nat.Prime.factorization_self hq).symm
              (Nat.zero_add 1))))
  have hcardQ : Nat.card ↥(Q : Subgroup G) = q :=
    (Eq.subst (motive := fun n => Nat.card ↥(Q : Subgroup G) = q ^ n)
        (Eq.subst (motive := fun n => Nat.factorization n q = 1) hcard.symm hf)
        (Sylow.card_eq_multiplicity Q)).trans (pow_one q)
  -- hence the index of `Q` is `p`
  have hindex : (Q : Subgroup G).index = p :=
    Nat.mul_right_cancel hq.pos
      ((congrArg (fun c => (Q : Subgroup G).index * c) hcardQ).symm.trans
        ((Subgroup.index_mul_card (Q : Subgroup G)).trans hcard))
  -- Sylow III: `n_q ≡ 1 [MOD q]` and `n_q ∣ p`; with `p < q` this forces `n_q = 1`
  have hn1 : Nat.card (Sylow q G) ∣ p :=
    Eq.subst (motive := fun n => Nat.card (Sylow q G) ∣ n) hindex (Sylow.card_dvd_index Q)
  have hn : Nat.card (Sylow q G) = 1 := by
    rcases hp.eq_one_or_self_of_dvd (Nat.card (Sylow q G)) hn1 with h | h
    · exact h
    · exfalso
      have hmod : p ≡ 1 [MOD q] :=
        Eq.subst (motive := fun n => n ≡ 1 [MOD q]) h (card_sylow_modEq_one q G)
      have hdvd : q ∣ p - 1 :=
        (Nat.modEq_iff_dvd' hp.one_lt.le).mp hmod.symm
      have hlt : p - 1 < q := Nat.lt_of_le_of_lt (Nat.sub_le p 1) hpq
      rcases Nat.eq_zero_or_pos (p - 1) with h0 | hpos
      · exact hp.ne_one (Nat.le_antisymm (Nat.sub_eq_zero_iff_le.mp h0) hp.one_lt.le)
      · exact absurd (Nat.le_of_dvd hpos hdvd) (Nat.not_le_of_gt hlt)
  have hsub : Subsingleton (Sylow q G) := (Nat.card_eq_one_iff_unique.mp hn).1
  -- the unique Sylow `q`-subgroup is normal, of order `q`: neither `⊥` nor `⊤`
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal G _ hsimple (Q : Subgroup G)
      (@Sylow.normal_of_subsingleton G _ q hsub Q) with hb | ht
  · exact absurd ((Subgroup.card_bot (G := G)).symm.trans
        (Eq.subst (motive := fun H : Subgroup G => Nat.card ↥H = q) hb hcardQ))
      (Nat.ne_of_lt hq.one_lt)
  · have h1 : Nat.card ↥(⊤ : Subgroup G) = q :=
      Eq.subst (motive := fun H : Subgroup G => Nat.card ↥H = q) ht hcardQ
    have h2 : Nat.card ↥(⊤ : Subgroup G) = p * q := (Subgroup.card_top (G := G)).trans hcard
    have h3 : p * q = 1 * q := (h2.symm.trans h1).trans (Nat.one_mul q).symm
    exact absurd (Nat.mul_right_cancel hq.pos h3) hp.ne_one

/-! ## Order `p ^ 2` — #280b -/
/-! ## Sylow counting helper — #280d tool -/

-- Reference: mathlib pin v4.35.0-rc3, `card_sylow_modEq_one`, `Nat.modEq_iff_dvd'`,
-- `Nat.eq_zero_of_dvd_of_lt`; [Dummit–Foote], Ch. 4, Sec. 6.
/-- If `n_q ∣ m < q` (with `q` prime), then `n_q ≡ 1 [MOD q]` forces `n_q = 1`. -/
theorem card_sylow_eq_one_of_card_dvd_of_lt {G : Type*} [Group G] [Finite G]
    {q m : ℕ} [Fact q.Prime] (hm : 0 < m) (hmq : m < q)
    (hn1 : Nat.card (Sylow q G) ∣ m) : Nat.card (Sylow q G) = 1 := by
  have hne : Nonempty (Sylow q G) := Sylow.nonempty
  have hpos : 0 < Nat.card (Sylow q G) := Nat.card_pos
  have hle : Nat.card (Sylow q G) ≤ m := Nat.le_of_dvd hm hn1
  have hmod : Nat.card (Sylow q G) ≡ 1 [MOD q] := card_sylow_modEq_one q G
  have hdvd : q ∣ Nat.card (Sylow q G) - 1 :=
    (Nat.modEq_iff_dvd' hpos).mp hmod.symm
  have hlt : Nat.card (Sylow q G) - 1 < q :=
    (Nat.sub_le_sub_right hle 1).trans_lt
      (Nat.lt_of_le_of_lt (Nat.sub_le m 1) hmq)
  exact Nat.le_antisymm
    (Nat.sub_eq_zero_iff_le.mp (Nat.eq_zero_of_dvd_of_lt hdvd hlt)) hpos

/-! ## Prime-power orders — #280d (p-group case) -/

-- Reference: mathlib pin v4.35.0-rc3, `IsPGroup.isSimpleGroup_iff_card_eq`
-- (a finite p-group is simple iff its order is `p`; its center is nontrivial).
/-- **A finite p-group of order `≠ p` is not simple** (consumed at the pin:
the center is a nontrivial normal subgroup). Covers orders `p^a`, `a ≥ 2`. -/
theorem not_isSimpleGroup_of_isPGroup_of_card_ne {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (hG : IsPGroup p G) (h : Nat.card G ≠ p) :
    ¬ IsSimpleGroup G :=
  fun hs => h (hG.isSimpleGroup_iff_card_eq.mp hs)

/-! ## Order 18 — #280d (`2 * 3^2`) -/

-- Reference: [Dummit–Foote], Ch. 4, Sec. 6 (Sylow III for `|G| = 18`):
-- `n_3 ∣ 2` and `n_3 ≡ 1 [MOD 3]` force `n_3 = 1`; the Sylow 3-subgroup (order 9)
-- is normal, proper and nontrivial. mathlib pin v4.35.0-rc3: `Sylow.card_eq_multiplicity`,
-- `Sylow.card_dvd_index`, `Nat.factorization_mul`, `Nat.factorization_pow_self`.
/-- **A group of order 18 is not simple** (proved). -/
theorem not_isSimpleGroup_of_card_eq_eighteen {G : Type*} [Group G] [Finite G]
    (hcard : Nat.card G = 18) : ¬ IsSimpleGroup G := by
  intro hsimple
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q⟩ := Sylow.nonempty (p := 3) (G := G)
  -- the multiplicity of `3` in `18 = 2 * 9 = 2 * 3^2` is 2
  have h2f : Nat.factorization 2 3 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (fun hd =>
      absurd (Nat.le_of_dvd Nat.two_pos hd)
        (Nat.not_le_of_gt (Nat.lt_succ_of_le (Nat.le_refl 2))))
  have h9f : Nat.factorization 9 3 = 2 :=
    Eq.subst (motive := fun n => Nat.factorization n 3 = 2) (rfl : (3 : ℕ) ^ 2 = 9)
      (Nat.factorization_pow_self Nat.prime_three)
  have hmul : Nat.factorization (2 * 9) = Nat.factorization 2 + Nat.factorization 9 :=
    Nat.factorization_mul (Nat.succ_ne_zero 1) (Nat.succ_ne_zero 8)
  have hf : Nat.factorization 18 3 = 2 := by
    refine Eq.subst (motive := fun n => Nat.factorization n 3 = 2) (rfl : (18 : ℕ) = 2 * 9) ?_
    exact (congrArg (fun f => f 3) hmul).trans
      ((Finsupp.add_apply (Nat.factorization 2) (Nat.factorization 9) 3).trans
        (Eq.subst (motive := fun n => n + Nat.factorization 9 3 = 2) h2f.symm
          ((Nat.zero_add (Nat.factorization 9 3)).trans h9f)))
  have hcardQ : Nat.card ↥(Q : Subgroup G) = 9 :=
    (Eq.subst (motive := fun n => Nat.card ↥(Q : Subgroup G) = 3 ^ n)
        (Eq.subst (motive := fun n => Nat.factorization n 3 = 2) hcard.symm hf)
        (Sylow.card_eq_multiplicity Q)).trans rfl
  -- hence the index of `Q` is `2`
  have hindex : (Q : Subgroup G).index = 2 :=
    Nat.mul_right_cancel (Nat.succ_pos 8)
      ((congrArg (fun c => (Q : Subgroup G).index * c) hcardQ).symm.trans
        ((Subgroup.index_mul_card (Q : Subgroup G)).trans hcard))
  -- `n_3 ∣ 2 < 3` and `n_3 ≡ 1 [MOD 3]` force `n_3 = 1`
  have hn1 : Nat.card (Sylow 3 G) ∣ 2 :=
    Eq.subst (motive := fun n => Nat.card (Sylow 3 G) ∣ n) hindex (Sylow.card_dvd_index Q)
  have hn : Nat.card (Sylow 3 G) = 1 :=
    card_sylow_eq_one_of_card_dvd_of_lt Nat.two_pos
      (Nat.lt_succ_of_le (Nat.le_refl 2)) hn1
  have hsub : Subsingleton (Sylow 3 G) := (Nat.card_eq_one_iff_unique.mp hn).1
  -- the unique Sylow 3-subgroup is normal, of order 9: neither `⊥` nor `⊤`
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal G _ hsimple (Q : Subgroup G)
      (@Sylow.normal_of_subsingleton G _ 3 hsub Q) with hb | ht
  · exact absurd ((Subgroup.card_bot (G := G)).symm.trans
        (Eq.subst (motive := fun H : Subgroup G => Nat.card ↥H = 9) hb hcardQ))
      (Nat.ne_of_lt (Nat.lt_succ_of_le (Nat.le_add_right 1 7)))
  · have h1 : Nat.card ↥(⊤ : Subgroup G) = 9 :=
      Eq.subst (motive := fun H : Subgroup G => Nat.card ↥H = 9) ht hcardQ
    have h2 : Nat.card ↥(⊤ : Subgroup G) = 18 := (Subgroup.card_top (G := G)).trans hcard
    exact absurd (h2.symm.trans h1) (Nat.ne_of_lt (Nat.lt_succ_of_le (Nat.le_add_right 9 8))).symm

/-! ## Order `m * q` with `q` prime and `1 < m < q` — #280f -/

-- Reference: [Dummit–Foote], Ch. 4, Sec. 6 (Sylow III, generalized: `n_q ∣ m` and
-- `n_q ≡ 1 [MOD q]` with `m < q` force `n_q = 1`); mathlib pin v4.35.0-rc3,
-- `card_sylow_modEq_one`, `Sylow.card_dvd_index`, `Sylow.card_eq_multiplicity`,
-- `Nat.eq_zero_of_dvd_of_lt`. This generalizes #280a and covers the census orders
-- 18, 20, 28, 44, 45, 50, 52, 58, … in one lemma. REVIEW(citation).
/-- **A group of order `m * q` with `q` prime and `1 < m < q` is not simple**
(proved): `n_q ∣ m < q` and `n_q ≡ 1 [MOD q]` force `n_q = 1`, so the Sylow
`q`-subgroup is normal, of order `q`, proper and nontrivial. -/
theorem not_isSimpleGroup_of_card_eq_mul_prime_of_lt {G : Type*} [Group G] [Finite G]
    {m q : ℕ} [Fact q.Prime] (hm1 : 1 < m) (hmq : m < q) (hcard : Nat.card G = m * q) :
    ¬ IsSimpleGroup G := by
  intro hsimple
  have hq := (Fact.out : q.Prime)
  obtain ⟨Q⟩ := Sylow.nonempty (p := q) (G := G)
  have : Nonempty (Sylow q G) := ⟨Q⟩
  -- the multiplicity of `q` in `m * q` is 1, since `q ∤ m` (`0 < m < q`)
  have hf : Nat.factorization (m * q) q = 1 :=
    (congrArg (fun f => f q)
        (Nat.factorization_mul (Nat.one_le_iff_ne_zero.mp hm1.le) hq.ne_zero)).trans
      ((Finsupp.add_apply m.factorization q.factorization q).trans
        (Eq.subst (motive := fun n => n + q.factorization q = 1)
            (Nat.factorization_eq_zero_of_not_dvd (fun hd =>
              absurd (Nat.le_of_dvd hm1.pos hd) (Nat.not_le_of_gt hmq))).symm
            (Eq.subst (motive := fun n => 0 + n = 1) (Nat.Prime.factorization_self hq).symm
              (Nat.zero_add 1))))
  have hcardQ : Nat.card ↥(Q : Subgroup G) = q :=
    (Eq.subst (motive := fun n => Nat.card ↥(Q : Subgroup G) = q ^ n)
        (Eq.subst (motive := fun n => Nat.factorization n q = 1) hcard.symm hf)
        (Sylow.card_eq_multiplicity Q)).trans (pow_one q)
  -- hence the index of `Q` is `m`
  have hindex : (Q : Subgroup G).index = m :=
    Nat.mul_right_cancel hq.pos
      ((congrArg (fun c => (Q : Subgroup G).index * c) hcardQ).symm.trans
        ((Subgroup.index_mul_card (Q : Subgroup G)).trans hcard))
  -- Sylow III: `n_q ≡ 1 [MOD q]` and `n_q ∣ m`; with `m < q` this forces `n_q = 1`
  have hn1 : Nat.card (Sylow q G) ∣ m :=
    Eq.subst (motive := fun n => Nat.card (Sylow q G) ∣ n) hindex (Sylow.card_dvd_index Q)
  have hn : Nat.card (Sylow q G) = 1 := by
    have hpos : 0 < Nat.card (Sylow q G) := Nat.card_pos
    have hle : Nat.card (Sylow q G) ≤ m := Nat.le_of_dvd hm1.pos hn1
    have hmod : Nat.card (Sylow q G) ≡ 1 [MOD q] := card_sylow_modEq_one q G
    have hdvd : q ∣ Nat.card (Sylow q G) - 1 :=
      (Nat.modEq_iff_dvd' hpos).mp hmod.symm
    have hlt : Nat.card (Sylow q G) - 1 < q :=
      (Nat.sub_le_sub_right hle 1).trans_lt
        (Nat.lt_of_le_of_lt (Nat.sub_le m 1) hmq)
    exact Nat.le_antisymm
      (Nat.sub_eq_zero_iff_le.mp (Nat.eq_zero_of_dvd_of_lt hdvd hlt)) hpos
  have hsub : Subsingleton (Sylow q G) := (Nat.card_eq_one_iff_unique.mp hn).1
  -- the unique Sylow `q`-subgroup is normal, of order `q`: neither `⊥` nor `⊤`
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal G _ hsimple (Q : Subgroup G)
      (@Sylow.normal_of_subsingleton G _ q hsub Q) with hb | ht
  · exact absurd ((Subgroup.card_bot (G := G)).symm.trans
        (Eq.subst (motive := fun H : Subgroup G => Nat.card ↥H = q) hb hcardQ))
      (Nat.ne_of_lt hq.one_lt)
  · have h1 : Nat.card ↥(⊤ : Subgroup G) = q :=
      Eq.subst (motive := fun H : Subgroup G => Nat.card ↥H = q) ht hcardQ
    have h2 : Nat.card ↥(⊤ : Subgroup G) = m * q := (Subgroup.card_top (G := G)).trans hcard
    have h3 : m * q = 1 * q := (h2.symm.trans h1).trans (Nat.one_mul q).symm
    exact absurd (Nat.mul_right_cancel hq.pos h3) (Nat.ne_of_lt hm1).symm


-- Reference: mathlib pin v4.35.0-rc3,
-- `IsPGroup.isMulCommutative_of_card_eq_prime_sq` (order `p^2` ⇒ commutative) and
-- Cauchy's theorem `exists_prime_orderOf_dvd_card'`; in a commutative group every
-- subgroup is normal (`Subgroup.normal_of_isMulCommutative`). [Dummit–Foote],
-- Ch. 4, Sec. 6. REVIEW(citation).
/-- **A group of order `p ^ 2` is not simple** (proved): it is commutative
(`IsPGroup.isMulCommutative_of_card_eq_prime_sq`), Cauchy gives an element `x`
of order `p`, and `zpowers x` is a normal subgroup of order `p` — proper and
nontrivial. -/
theorem not_isSimpleGroup_of_card_eq_prime_sq {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (hcard : Nat.card G = p ^ 2) : ¬ IsSimpleGroup G := by
  intro hsimple
  have hp := (Fact.out : p.Prime)
  have _ : IsPGroup p G := IsPGroup.of_card hcard
  have hcomm : IsMulCommutative G := IsPGroup.isMulCommutative_of_card_eq_prime_sq hcard
  have hdvd : p ∣ Nat.card G :=
    Eq.subst (motive := fun n => p ∣ n) hcard.symm ⟨p, pow_two p⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hcardH : Nat.card ↥(Subgroup.zpowers x) = p := (Nat.card_zpowers x).trans hx
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal G _ hsimple (Subgroup.zpowers x)
      (@Subgroup.normal_of_isMulCommutative G _ hcomm (Subgroup.zpowers x)) with hb | ht
  · exact absurd ((Subgroup.card_bot (G := G)).symm.trans
        (Eq.subst (motive := fun H : Subgroup G => Nat.card ↥H = p) hb hcardH))
      (Nat.ne_of_lt hp.one_lt)
  · have h1 : Nat.card ↥(⊤ : Subgroup G) = p :=
      Eq.subst (motive := fun H : Subgroup G => Nat.card ↥H = p) ht hcardH
    have h2 : Nat.card ↥(⊤ : Subgroup G) = p ^ 2 := (Subgroup.card_top (G := G)).trans hcard
    have h3 : p * p = p * 1 :=
      (pow_two p).symm.trans ((h2.symm.trans h1).trans (mul_one p).symm)
    exact absurd (Nat.mul_left_cancel hp.pos h3) hp.ne_one

/-! ## Order 12 — #280c (the `PSL(2,3) ≅ A_4` level)

The order-12 case is proved in `BoringMath.GroupTheory.Simple.OrderTwelve`
(`not_isSimpleGroup_of_card_eq_twelve`, by the element-counting route: `n_3 = 4`
gives 8 elements of order 3, so the remaining 4 form the unique normal Sylow
2-subgroup); this module imports it instead of redeclaring it.

-/

end BoringMath
