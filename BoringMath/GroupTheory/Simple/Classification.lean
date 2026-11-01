/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Algebra.Field.ZMod
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.GroupTheory.Coset.Card
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# The classification of finite simple groups (CFSG) — sector decomposition

This module is the entry point of the CFSG program: the master statement
`classification_of_finite_simple_groups` broken into the four classical
sectors, with the sectors filled in one at a time.

* **Sector A (abelian)** — proved below by consuming mathlib at the pin:
  a finite simple abelian group is cyclic of prime order.
* **Sector B (alternating)** — consumed from mathlib at the pin:
  `A_n` is simple for `n ≥ 5`.
* **Sector C (Lie type)** — the `A`-family `PSL(n, F_q)` is built as the
  concrete mathlib object `PSL(n, R) = SL(n, R) / Z(SL(n, R))`; the cardinality
  split is proved below; the simplicity theorem (Iwasawa criterion) is the
  main open lemma of this sector, with a peeling plan. The remaining 15
  families (B/C/D classical, twisted Steinberg/Suzuki/Ree, exceptional
  `^2E_6`, `E_6`-`E_9`, `F_4`, `G_2`, `^3D_4`) join this sector as they are
  constructed.
* **Sector D (sporadic)** — the 26 sporadic groups as data (ATLAS names and
  orders); the concrete constructions (Mathieu groups as permutation groups,
  Monster via a presentation) are the peeling plan of this sector.

Honesty note: the master theorem is currently a `sorry` with a peeling plan
(§7 protocol) — the full CFSG is a multi-year formalization project; this
module is its skeleton and its proved-so-far content.

## References
* [GLS] D. Gorenstein, R. Lyons, R. Solomon, *The Classification of the Finite
  Simple Groups*, Number 1–3, AMS 1994–2005 (the theorem and its sector
  decomposition).
* [ATLAS] J. H. Conway et al., *ATLAS of Finite Groups*, OUP 1985 (the 26
  sporadic names and orders, pp. xvi–xvii).
* [Wilson] R. A. Wilson, *The Finite Simple Groups*, Springer GTM 2009
  (graduate-level account; PSL simplicity via Iwasawa, ch. 5).
* mathlib pin v4.35.0-rc3: `IsSimpleGroup`, `isSimpleGroup_of_prime_card`,
  `IsSimpleGroup.prime_card`, `alternatingGroup.isSimpleGroup`,
  `Matrix.ProjectiveSpecialLinearGroup` (`PSL`), `Matrix.card_SL_field`,
  `Matrix.center_equiv_rootsOfUnity'`, `Subgroup.isSimpleGroup` (Iwasawa
  criterion, `Mathlib/GroupTheory/GroupAction/Iwasawa.lean`).
-/

namespace BoringMath

open Matrix
open scoped MatrixGroups

/-! ## Sector A: abelian — proved (consume mathlib) -/

-- Reference: mathlib pin v4.35.0-rc3, `Mathlib/GroupTheory/SpecificGroups/Cyclic.lean`
-- (`isSimpleGroup_of_prime_card`, `IsSimpleGroup.prime_card`,
-- `IsSimpleGroup.isCyclic`); [GLS] Number 1, §1 (simple abelian = prime cyclic).
/-- **Sector A (abelian case of the CFSG), proved at the pin**: a finite
abelian group is simple iff its order is prime (and then it is cyclic). -/
theorem finite_comm_simple_iff_prime_card {G : Type*} [CommGroup G] [Finite G] :
    IsSimpleGroup G ↔ (Nat.card G).Prime :=
  ⟨fun h => @IsSimpleGroup.prime_card G _ h,
    fun h => @isSimpleGroup_of_prime_card G _ (Nat.card G) ⟨h⟩ rfl⟩

-- Reference: mathlib pin v4.35.0-rc3, `Cyclic.lean` (`IsSimpleGroup.isCyclic`,
-- `IsSimpleGroup.prime_card`, `zmodCyclicMulEquiv`); [GLS] Number 1, §1.
/-- **Sector A to isomorphism level (proved)**: a finite simple abelian group
is isomorphic to `Multiplicative (ZMod p)` for a prime `p` (its order). -/
theorem finite_simple_abelian_classification {G : Type*} [CommGroup G] [Finite G]
    [IsSimpleGroup G] :
    ∃ p : ℕ, p.Prime ∧ Nat.card G = p ∧ Nonempty (G ≃* Multiplicative (ZMod p)) :=
  ⟨Nat.card G, IsSimpleGroup.prime_card, rfl,
    ⟨(zmodCyclicMulEquiv (inferInstance : IsCyclic G)).symm⟩⟩

/-! ## Sector B: alternating — consumed from mathlib at the pin -/

-- Reference: mathlib pin v4.35.0-rc3,
-- `Mathlib/GroupTheory/SpecificGroups/Alternating/Simple.lean`
-- (`alternatingGroup.isSimpleGroup`); [GLS] Number 1; [Wilson] ch. 5.
/-- **Sector B (alternating sector), consumed at the pin**: `A_n` is simple
for `n ≥ 5`. -/
theorem alternating_isSimpleGroup (n : ℕ) (hn : 5 ≤ n) :
    IsSimpleGroup (alternatingGroup (Fin n)) :=
  alternatingGroup.isSimpleGroup
    (Eq.subst (motive := fun k => 5 ≤ k) (Nat.card_fin n).symm hn)

-- Reference: reconstructed from first principles at the pin — no external text
-- needed: the Klein four subgroup of `A_4` is normal (mathlib
-- `alternatingGroup.normal_kleinFour`), and proper nontrivial by cardinality
-- (`kleinFour_card_of_card_eq_four` vs `card_of_card_eq_four` +
-- `Subgroup.card_bot`/`card_top`), contradicting `IsSimpleGroup`. This is the
-- `A_4 ≅ PSL(2,3)` exception of sector C, proved directly.
/-- **The small alternating exception, reconstructed from first principles**:
`A_4` is not simple — its Klein four subgroup is a proper nontrivial normal
subgroup (matching the `PSL(2,3)` exception clause of sector C). -/
theorem not_isSimpleGroup_alternatingGroup_fin4 :
    ¬ IsSimpleGroup (alternatingGroup (Fin 4)) := by
  intro h
  have h4 : Nat.card (Fin 4) = 4 := Nat.card_fin 4
  have hc : Nat.card ↥(alternatingGroup.kleinFour (Fin 4)) = 4 :=
    alternatingGroup.kleinFour_card_of_card_eq_four h4
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ h
      (alternatingGroup.kleinFour (Fin 4)) (alternatingGroup.normal_kleinFour h4) with hb | ht
  · have h1 : Nat.card ↥(⊥ : Subgroup (alternatingGroup (Fin 4))) = 4 :=
      Eq.subst (motive := fun (H : Subgroup (alternatingGroup (Fin 4))) => Nat.card ↥H = 4) hb hc
    exact absurd ((Subgroup.card_bot (G := alternatingGroup (Fin 4))).symm.trans h1)
      (Nat.ne_of_lt (Nat.lt_add_of_pos_right (k := 3) (Nat.succ_pos 2)))
  · have h1 : Nat.card ↥(⊤ : Subgroup (alternatingGroup (Fin 4))) = 4 :=
      Eq.subst (motive := fun (H : Subgroup (alternatingGroup (Fin 4))) => Nat.card ↥H = 4) ht hc
    have h2 : Nat.card ↥(⊤ : Subgroup (alternatingGroup (Fin 4))) = 12 :=
      (Subgroup.card_top (G := alternatingGroup (Fin 4))).trans
        (alternatingGroup.card_of_card_eq_four h4)
    exact absurd (h1.symm.trans h2)
      (Nat.ne_of_lt (Nat.lt_add_of_pos_right (k := 8) (Nat.succ_pos 7)))

/-! ## Sector C: Lie type — the `A`-family `PSL(n, F_q)` -/

-- Reference: mathlib pin v4.35.0-rc3, `Mathlib/LinearAlgebra/Matrix/
-- ProjectiveSpecialLinearGroup.lean` (`ProjectiveSpecialLinearGroup`,
-- notation `PSL(n, R)` = `SL(n, R) ⧸ center`); [Wilson] ch. 5 (definition).
/-- **The `A`-family of Lie type as a concrete object**: `PSL(n, R)` is
`SL(n, R)` modulo its center (mathlib abbrev; notation `PSL(n, R)`). -/
abbrev psl (n : ℕ) (R : Type*) [CommRing R] : Type _ := PSL(n, R)

-- Reference: mathlib pin v4.35.0-rc3, `Mathlib/GroupTheory/Coset/Card.lean`
-- (`card_eq_card_quotient_mul_card_subgroup`); [Wilson] ch. 5 (order formula).
/-- **Cardinality split for PSL** (proved): `|PSL(n,R)| * |Z(SL(n,R))| =
|SL(n,R)|`. -/
theorem card_PSL_mul_card_center (n : ℕ) (R : Type*) [CommRing R] :
    Nat.card (PSL(n, R)) * Nat.card (Subgroup.center (SpecialLinearGroup (Fin n) R)) =
      Nat.card (SpecialLinearGroup (Fin n) R) :=
  (Subgroup.card_eq_card_quotient_mul_card_subgroup _).symm

-- Reference: mathlib pin v4.35.0-rc3, `Matrix.card_SL_field`,
-- `Matrix.center_equiv_rootsOfUnity'`; [Wilson] ch. 5: over `F_q` the center of
-- `SL(n, q)` is the `n`-th roots of unity, of order `gcd(n, q - 1)`.
/-- **Cardinality of PSL over a finite field** (proved up to the center count):
`|PSL(n, F_q)| * |μ_n(F_q)| = (∏_{i<n} (q^n - q^i)) / (q - 1)`. -/
theorem card_PSL_finiteField_mul_card_rootsOfUnity {n : ℕ} [NeZero n] {𝔽 : Type*}
    [Field 𝔽] [Fintype 𝔽] :
    Nat.card (PSL(n, 𝔽)) * Nat.card (rootsOfUnity n 𝔽) =
      (∏ i : Fin n, (Fintype.card 𝔽 ^ n - Fintype.card 𝔽 ^ (i : ℕ))) / (Fintype.card 𝔽 - 1) := by
  have h1 := card_PSL_mul_card_center n 𝔽
  have h2 := Matrix.card_SL_field (𝔽 := 𝔽) (n := n)
  have h3 : Nat.card (Subgroup.center (SpecialLinearGroup (Fin n) 𝔽)) =
      Nat.card (rootsOfUnity n 𝔽) :=
    Eq.subst (motive := fun k =>
        Nat.card (Subgroup.center (SpecialLinearGroup (Fin n) 𝔽)) = Nat.card (rootsOfUnity k 𝔽))
      (Fintype.card_fin n)
      (Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (0 : Fin n)).toEquiv)
  exact (congrArg (fun x => Nat.card (PSL(n, 𝔽)) * x) h3).symm.trans (h1.trans h2)

-- Reference: mathlib pin v4.35.0-rc3, `Matrix.card_SL_field` + `ZMod.card` +
-- `Fin.prod_univ_two`; [ATLAS]/[Wilson]: `|SL(2,2)| = 6`. The product and the
-- division are literal `Nat` computations, closed by `rfl`.
/-- **Exception order `|SL(2, F_2)| = 6`** (proved; `PSL(2,2)` has trivial
center, so `|PSL(2,2)| = 6` too — the `S_3` exception of sector C). -/
theorem card_SL_2_2 [Fact (Nat.Prime 2)] [NeZero 2] :
    Nat.card (SpecialLinearGroup (Fin 2) (ZMod 2)) = 6 :=
  (Matrix.card_SL_field (𝔽 := ZMod 2) (n := 2)).trans
    ((congrArg (fun c => (∏ i : Fin 2, (c ^ 2 - c ^ (i : ℕ))) / (c - 1)) (ZMod.card 2)).trans
      ((congrArg (fun P => P / (2 - 1))
        (Fin.prod_univ_two fun i : Fin 2 => (2:ℕ)^2 - (2:ℕ)^(i:ℕ))).trans rfl))

-- Reference: as `card_SL_2_2`; `|SL(2,3)| = 24`, so `|PSL(2,3)| = 12` (center
-- of order 2) — the `A_4` exception of sector C.
/-- **Exception order `|SL(2, F_3)| = 24`** (proved). -/
theorem card_SL_2_3 [Fact (Nat.Prime 3)] [NeZero 3] :
    Nat.card (SpecialLinearGroup (Fin 2) (ZMod 3)) = 24 :=
  (Matrix.card_SL_field (𝔽 := ZMod 3) (n := 2)).trans
    ((congrArg (fun c => (∏ i : Fin 2, (c ^ 2 - c ^ (i : ℕ))) / (c - 1)) (ZMod.card 3)).trans
      ((congrArg (fun P => P / (3 - 1))
        (Fin.prod_univ_two fun i : Fin 2 => (3:ℕ)^2 - (3:ℕ)^(i:ℕ))).trans rfl))

-- Reference: [Wilson] ch. 5 (Iwasawa's criterion applied to `SL(n,q)` acting on
-- projective space); mathlib pin v4.35.0-rc3,
-- `Mathlib/GroupTheory/GroupAction/Iwasawa.lean` (`isSimpleGroup`).
/-- **Sector C main theorem (A-family)**: `PSL(n, F_q)` is simple except
`(n, q) ∈ {(2,2), (2,3)}`. TEMPORARY SORRY with peeling plan. -/
theorem PSL_isSimpleGroup {n p k : ℕ} [NeZero n] [Fact p.Prime] (hk : 1 ≤ k)
    (h : (n, p ^ k) ≠ (2, 2) ∧ (n, p ^ k) ≠ (2, 3)) :
    IsSimpleGroup (PSL(n, GaloisField p k)) := by
  -- TEMPORARY SORRY: the honest proof has not been instantiated yet.
  -- PEELING PLAN:
  --   (1) `commutator_SL_eq_top`: `SL(n, F_q)` is perfect except `(n,q) ∈
  --       {(2,2),(2,3)}` (elementary matrices; mathlib has
  --       `commutator_alternatingGroup_eq_top` as a model);
  --   (2) the action of `SL(n, F_q)` on the projective space `P^{n-1}(F_q)`
  --       is quasiprimitive (`IsQuasiPreprimitive`) — point stabilizers are
  --       maximal parabolics;
  --   (3) the kernel of the action is exactly the center, so `PSL` acts
  --       faithfully;
  --   (4) apply the Iwasawa criterion (`Subgroup.isSimpleGroup` in
  --       `Mathlib/GroupTheory/GroupAction/Iwasawa.lean`) to conclude.
  sorry

/-! ## Sector D: sporadic — the 26 sporadic groups as data -/

-- Reference: [ATLAS], pp. xvi–xvii (the list of 26 sporadic groups and their
-- orders). REVIEW(citation): orders re-verified against the ATLAS in review.
/-- The 26 sporadic simple groups, by ATLAS name. -/
inductive SporadicName
  | M11 | M12 | M22 | M23 | M24
  | J1 | J2 | J3 | J4
  | HS | McL | Suz | Ru | He | Ly | ON
  | Co1 | Co2 | Co3
  | Fi22 | Fi23 | Fi24 | HN | Th
  | B | M
  deriving DecidableEq, Repr

-- Reference: [ATLAS], pp. xvi–xvii (orders of the sporadic groups).
-- REVIEW(citation): re-verify each order against the ATLAS in review.
/-- The order of each sporadic group (ATLAS). -/
def sporadicOrder : SporadicName → ℕ
  | .M11 => 7920
  | .M12 => 95040
  | .M22 => 443520
  | .M23 => 10200960
  | .M24 => 244823040
  | .J1 => 175560
  | .J2 => 604800
  | .J3 => 50232960
  | .J4 => 86775571046077562880
  | .HS => 44352000
  | .McL => 898128000
  | .Suz => 448345497600
  | .Ru => 145926144000
  | .He => 4030387200
  | .Ly => 51765179004000000
  | .ON => 460815505920
  | .Co1 => 4157776806543360000
  | .Co2 => 42305421312000
  | .Co3 => 495766656000
  | .Fi22 => 64561751654400
  | .Fi23 => 4089470473293004800
  | .Fi24 => 1255205709190661721292800
  | .HN => 273030912000000
  | .Th => 90745943887872000
  | .B => 4154781481226426191177580544000000
  | .M => 808017424794512875886459904961710757005754368000000000

-- Reference: [ATLAS], p. xvi; [GLS] Number 3 (the sporadic sector of the CFSG).
/-- **The sporadic sector at order level**: `G` has the order of one of the 26
sporadic groups. The isomorphism-level version (`∃ s, Nonempty (G ≃*
sporadicGroup s)`) is the peeling target: the Mathieu groups `M11`–`M24` are
to be constructed as permutation groups on `≤ 24` points from their ATLAS
generators, the Monster and the other large sporadics from presentations. -/
def IsSporadic (G : Type*) [Group G] [Finite G] : Prop :=
  ∃ s : SporadicName, Nat.card G = sporadicOrder s

/-! ## Master statement -/

-- Reference: [GLS] Number 1–3 (the CFSG); [ATLAS]; [Wilson].
/-- **The classification of finite simple groups**: every finite simple group
is (A) cyclic of prime order, or (B) alternating `A_n` (`n ≥ 5`), or
(C) of Lie type (here: the `A`-family `PSL(n, F_p)` over prime fields outside
the two small exceptions; prime-power fields `F_{p^k}` via `GaloisField` and
the other 15 families join this clause as they are constructed — see
`PSL_isSimpleGroup` below),
or (D) sporadic (order-level shadow; isomorphism-level in the plan).

TEMPORARY SORRY with peeling plan. -/
theorem classification_of_finite_simple_groups {G : Type*} [Group G] [Finite G]
    [IsSimpleGroup G] :
    (∃ p : ℕ, p.Prime ∧ Nat.card G = p) ∨
    (∃ n : ℕ, 5 ≤ n ∧ Nonempty (G ≃* alternatingGroup (Fin n))) ∨
    (∃ n p : ℕ, 2 ≤ n ∧ p.Prime ∧ (n, p) ≠ (2, 2) ∧ (n, p) ≠ (2, 3) ∧
      Nonempty (G ≃* PSL(n, ZMod p))) ∨
    IsSporadic G := by
  -- TEMPORARY SORRY: the full CFSG proof is a multi-year project; this is the
  -- master skeleton. PEELING PLAN (sectors, in order):
  --   A. abelian case — PROVED above (`finite_comm_simple_iff_prime_card`):
  --      if `G` is abelian, clause A holds;
  --   B. alternating — `A_n` simple for `n ≥ 5` consumed above;
  --   C. Lie type — `PSL_isSimpleGroup` (Iwasawa, plan above) plus the other
  --      15 families (B/C/D, twisted, exceptional) as their own modules;
  --   D. sporadic — construct the 26 groups (Mathieu as permutation groups,
  --      rest from presentations) and prove the completeness of the list;
  --   the reduction "every finite simple group lies in A–D" is the deep part
  --   (odd-order theorem, local analysis), planned sector by sector.
  sorry

end BoringMath
