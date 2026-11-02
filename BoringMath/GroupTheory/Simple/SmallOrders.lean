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

/-!
# Small-order non-simplicity

Ticket **#280 CFSG.SMALL**: the first rung of the small-order census "no finite
simple group has composite order `< 60`" (the smallest nonabelian simple group
is `A_5`, of order 60 — `card_alternatingGroup_fin5` in
`BoringMath.GroupTheory.Simple.Classification`). This module proves the two
clean Sylow-theoretic cases: order `p * q` with primes `p < q` (#280a) and order
`p ^ 2` (#280b), and records the order-12 case (#280c, the `PSL(2,3) ≅ A_4`
level) as a `sorry` with a peeling plan.

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

/-! ## Order 12 — #280c (the `PSL(2,3) ≅ A_4` level) -/

-- Reference: [Dummit–Foote], Ch. 4, Sec. 6 (Sylow counting for `|G| = 12`);
-- [Wilson] GTM 251, ch. 1. REVIEW(citation): pin sections against held texts.
/-- **A group of order 12 is not simple** (e.g. `PSL(2, F_3) ≅ A_4`). TEMPORARY
SORRY with peeling plan. -/
theorem not_isSimpleGroup_of_card_eq_twelve {G : Type*} [Group G] [Finite G]
    (h : Nat.card G = 12) : ¬ IsSimpleGroup G := by
  -- TEMPORARY SORRY: the honest proof has not been instantiated yet.
  -- PEELING PLAN (ticket #280c):
  --   (1) `n_3 ∈ {1, 4}`: `Sylow.card_sylow_modEq_one` (n_3 ≡ 1 [MOD 3]) and
  --       `Sylow.card_dvd_index` with `Subgroup.index_mul_card`
  --       (a Sylow 3-subgroup has order 3, hence index 4);
  --   (2) `n_3 = 1`: the unique Sylow 3-subgroup is normal
  --       (`Sylow.normal_of_subsingleton`), of order 3 — proper nontrivial;
  --   (3) `n_3 = 4`: conjugation on `Sylow 3 G` (card 4) gives
  --       `φ : G →* Equiv.Perm (Sylow 3 G)`; transitivity (Sylow conjugacy,
  --       `Sylow.isPretransitive`) gives `4 ∣ Nat.card φ.range`, Lagrange gives
  --       `Nat.card φ.range ∣ 12`, so `|im| ∈ {4, 12}`;
  --   (4) `|im| = 4`: `ker φ` has order 3, is normal, proper nontrivial;
  --   (5) `|im| = 12`: `φ` is injective and `G` is an order-12 subgroup of
  --       `S_4`, hence `A_4` (subgroup census in `BoringMath/Symmetry/S4Census.lean`);
  --       `kleinFour` pulled back along `φ` is a normal subgroup of order 4.
  sorry

end BoringMath
