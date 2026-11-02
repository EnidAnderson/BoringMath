import BoringMath.GroupTheory.Simple.PSLCard
import BoringMath.GroupTheory.Simple.PSLSimple
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/

/-!
# Exceptional isomorphisms — ticket #256: `A_5 ≅ PSL(2, F_4)`

`PSL(2, F_4)` acts faithfully on the projective line `ℙ F_4 (Fin 2 → F_4)`, which
has `4 + 1 = 5` points (`card_projectiveLine_galoisField_2_2`), giving an injective
homomorphism `PSL(2, F_4) →* Perm (Fin 5)` (`psl24ToPerm5`). Since `PSL(2, F_4)` is
perfect (`SL2Simple.PSL_commutator_eq_top`, using that `F_4` has an element `a ≠ 0`
with `a² ≠ 1`), its image lies in the alternating group
(`alternatingGroup.commutator_perm_le`). Both `PSL(2, F_4)` and `A_5` have order 60
(`card_PSL_2_galoisField_2_2`, `card_alternatingGroup_fin5`), so the image is all of
`A_5`, yielding the isomorphism.

## References
* [Wilson] GTM 251, ch. 1 (the exceptional isomorphism `A_5 ≅ PSL(2,4) ≅ PSL(2,5)`);
  [ATLAS] p. 2.
* mathlib pin v4.35.0-rc3: `Projectivization.card`, `Projectivization.PSLAction.toPermHom`,
  `Matrix.ProjectiveSpecialLinearGroup.toPermHom_injective`,
  `SL2Simple.PSL_commutator_eq_top`, `alternatingGroup.commutator_perm_le`,
  `Subgroup.eq_of_le_of_card_ge`, `MonoidHom.ofInjective`, `MulEquiv.subgroupCongr`,
  `Equiv.permCongrHom`, `Fintype.equivFinOfCardEq`, `GaloisField.card`,
  `Nat.card_eq_card_units_add_one`, `IsCyclic.exists_generator`,
  `orderOf_eq_card_of_forall_mem_zpowers`, `orderOf_dvd_of_pow_eq_one`,
  `mem_rootsOfUnity`.
-/


namespace BoringMath

open Matrix
open scoped MatrixGroups

open scoped LinearAlgebra.Projectivization

/-! ## Roots of unity over a finite field — #283 (general finite field) -/

set_option linter.style.haveILetI false in
-- Reference: [Wilson] GTM 251, ch. 5 (`μ_n(F_q)` has order `gcd n (q-1)`);
-- mathlib pin v4.35.0-rc3: `mem_rootsOfUnity`, `IsCyclic.card_pow_eq_one_eq_gcd`
-- (PSLCard.lean), `Nat.card_eq_card_units_add_one`, and the `IsCyclic Fˣ`
-- instance for finite fields.
/-- **The `n`-th roots of unity in a finite field `F` number `gcd n (|F| - 1)`**
(proved: `Fˣ` is cyclic, and the `n`-torsion of a cyclic group of order `m` has
order `gcd n m`). -/
theorem card_rootsOfUnity_finiteField {n : ℕ} {F : Type*} [Field F] [Finite F] :
    Nat.card (rootsOfUnity n F) = Nat.gcd n (Nat.card F - 1) := by
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fintype Fˣ := Fintype.ofFinite Fˣ
  have hequiv : ↥(rootsOfUnity n F) ≃ {x : Fˣ // x ^ n = 1} :=
    Equiv.subtypeEquivRight (fun ζ => mem_rootsOfUnity n ζ)
  have hcard : Fintype.card Fˣ = Nat.card F - 1 :=
    (Nat.card_eq_fintype_card (α := Fˣ)).symm.trans
      (Nat.eq_sub_of_add_eq (Nat.card_eq_card_units_add_one F).symm)
  exact (Nat.card_congr hequiv).trans
    ((IsCyclic.card_pow_eq_one_eq_gcd n).trans
      ((congrArg (fun m => Nat.gcd m n) hcard).trans (Nat.gcd_comm (Nat.card F - 1) n)))

/-! ## Order of `PSL(2, F_4)` — #284 -/

set_option linter.style.haveILetI false in
-- Reference: [Wilson] GTM 251, ch. 5; `card_PSL_finiteField_mul_card_rootsOfUnity`
-- (Classification.lean) + `card_rootsOfUnity_finiteField` + `GaloisField.card`.
/-- **`|PSL(2, F_4)| = 60`** (proved: `|PSL(2,q)| * gcd(2, q-1) = q(q²-1)` with
`q = 4`, and `gcd(2, 3) = 1`). -/
theorem card_PSL_2_galoisField_2_2 : Nat.card (PSL(2, GaloisField 2 2)) = 60 := by
  haveI : NeZero 2 := ⟨Nat.succ_ne_zero 1⟩
  haveI : Fintype (GaloisField 2 2) := Fintype.ofFinite _
  have hk : Nat.card (GaloisField 2 2) = 4 :=
    (GaloisField.card (p := 2) (n := 2) (Nat.succ_ne_zero 1)).trans rfl
  have hroots : Nat.card (rootsOfUnity 2 (GaloisField 2 2)) = 1 :=
    (card_rootsOfUnity_finiteField (n := 2) (F := GaloisField 2 2)).trans
      (Eq.subst (motive := fun c => Nat.gcd 2 (c - 1) = 1) hk.symm rfl)
  have hkF : Fintype.card (GaloisField 2 2) = 4 :=
    (Nat.card_eq_fintype_card (α := GaloisField 2 2)).symm.trans hk
  have h := card_PSL_finiteField_mul_card_rootsOfUnity (n := 2) (𝔽 := GaloisField 2 2)
  have hprod : (∏ i : Fin 2, ((4 : ℕ) ^ 2 - (4 : ℕ) ^ (i : ℕ))) / (4 - 1) = 60 :=
    (congrArg (fun x => x / (4 - 1))
      (Fin.prod_univ_two (fun i : Fin 2 => ((4 : ℕ) ^ 2 - (4 : ℕ) ^ (i : ℕ))))).trans rfl
  have h' : Nat.card (PSL(2, GaloisField 2 2)) * Nat.card (rootsOfUnity 2 (GaloisField 2 2)) = 60 :=
    (Eq.subst (motive := fun c => Nat.card (PSL(2, GaloisField 2 2)) *
        Nat.card (rootsOfUnity 2 (GaloisField 2 2)) =
          (∏ i : Fin 2, (c ^ 2 - c ^ (i : ℕ))) / (c - 1)) hkF h).trans hprod
  have h'' : Nat.card (PSL(2, GaloisField 2 2)) * 1 = 60 :=
    Eq.subst (motive := fun c => Nat.card (PSL(2, GaloisField 2 2)) * c = 60) hroots h'
  exact Eq.subst (motive := fun n => n = 60) (Nat.mul_one _) h''

/-! ## The projective line over `F_4` has 5 points -/

-- Reference: mathlib pin v4.35.0-rc3, `Projectivization.card`
-- (`|V| - 1 = |ℙ V| * (|k| - 1)`), `GaloisField.card`, `Nat.card_pi`,
-- `Fin.prod_univ_two`.
/-- The projective line over `F_4` has `4 + 1 = 5` points (proved). -/
theorem card_projectiveLine_galoisField_2_2 :
    Nat.card (ℙ (GaloisField 2 2) (Fin 2 → GaloisField 2 2)) = 5 := by
  have hk : Nat.card (GaloisField 2 2) = 4 :=
    (GaloisField.card (p := 2) (n := 2) (Nat.succ_ne_zero 1)).trans rfl
  have hV : Nat.card (Fin 2 → GaloisField 2 2) = 16 :=
    (Nat.card_pi (α := Fin 2) (β := fun _ => GaloisField 2 2)).trans
      ((Fin.prod_univ_two (fun _ : Fin 2 => Nat.card (GaloisField 2 2))).trans
        ((congrArg (fun c => c * c) hk).trans rfl))
  have h := Projectivization.card (k := GaloisField 2 2) (V := Fin 2 → GaloisField 2 2)
  have h2 : Nat.card (ℙ (GaloisField 2 2) (Fin 2 → GaloisField 2 2)) * 3 = 15 := by
    have e1 : (16 : ℕ) - 1 = Nat.card (ℙ (GaloisField 2 2) (Fin 2 → GaloisField 2 2)) * (4 - 1) :=
      Eq.subst (motive := fun c => (16 : ℕ) - 1 =
          Nat.card (ℙ (GaloisField 2 2) (Fin 2 → GaloisField 2 2)) * (c - 1)) hk
        (Eq.subst (motive := fun v => (v : ℕ) - 1 =
            Nat.card (ℙ (GaloisField 2 2) (Fin 2 → GaloisField 2 2)) *
              (Nat.card (GaloisField 2 2) - 1)) hV h)
    exact e1.symm
  exact Nat.mul_right_cancel (Nat.succ_pos 2) (h2.trans rfl)

/-! ## `F_4` has an element `a ≠ 0` with `a² ≠ 1` -/

set_option linter.style.haveILetI false in
-- Reference: mathlib pin v4.35.0-rc3, `IsCyclic.exists_generator`,
-- `orderOf_eq_card_of_forall_mem_zpowers`, `orderOf_dvd_of_pow_eq_one`,
-- `Nat.card_eq_card_units_add_one`, `GaloisField.card`; a cyclic group of order 3
-- has no nontrivial element squaring to 1.
/-- **There is `a ∈ F_4` with `a ≠ 0` and `a² ≠ 1`** (proved: `F_4ˣ` is cyclic of
order 3, so its generator does not square to 1). -/
theorem exists_sq_ne_one_galoisField_2_2 :
    ∃ a : GaloisField 2 2, a ≠ 0 ∧ a ^ 2 ≠ 1 := by
  haveI : Fintype (GaloisField 2 2) := Fintype.ofFinite _
  haveI : Fintype (GaloisField 2 2)ˣ := Fintype.ofFinite _
  have hk : Nat.card (GaloisField 2 2) = 4 :=
    (GaloisField.card (p := 2) (n := 2) (Nat.succ_ne_zero 1)).trans rfl
  have hcu : Nat.card (GaloisField 2 2)ˣ = 3 :=
    Nat.succ_inj.mp ((Nat.card_eq_card_units_add_one (GaloisField 2 2)).symm.trans hk)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (GaloisField 2 2)ˣ)
  refine ⟨g.1, Units.ne_zero g, fun hsq => ?_⟩
  have h2 : g ^ 2 = 1 := Units.ext hsq
  have hdvd : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  have hord : orderOf g = 3 :=
    ((orderOf_eq_card_of_forall_mem_zpowers hg).trans Nat.card_eq_fintype_card).trans
      ((Nat.card_eq_fintype_card (α := (GaloisField 2 2)ˣ)).symm.trans hcu)
  exact absurd (Nat.le_of_dvd Nat.two_pos (Eq.subst (motive := fun n => n ∣ 2) hord hdvd))
    (Nat.not_le_of_gt (Nat.lt_succ_of_le (Nat.le_refl 2)))

-- Reference: `card_projectiveLine_galoisField_2_2` + `Fintype.equivFinOfCardEq`
-- (noncomputable: the `Fin 5`-equivalence of a 5-element type is chosen).
noncomputable def psl24LineEquiv : ℙ (GaloisField 2 2) (Fin 2 → GaloisField 2 2) ≃ Fin 5 := by
  haveI : Fintype (ℙ (GaloisField 2 2) (Fin 2 → GaloisField 2 2)) := Fintype.ofFinite _
  exact Fintype.equivFinOfCardEq
    ((Nat.card_eq_fintype_card (α := ℙ (GaloisField 2 2) (Fin 2 → GaloisField 2 2))).symm.trans
      card_projectiveLine_galoisField_2_2)

-- Reference: `Projectivization.PSLAction.toPermHom` (Projectivization/Action.lean)
-- transported along `psl24LineEquiv` via `Equiv.permCongrHom`.
noncomputable def psl24ToPerm5 : PSL(2, GaloisField 2 2) →* Equiv.Perm (Fin 5) :=
  (Equiv.permCongrHom psl24LineEquiv).toMonoidHom.comp Projectivization.PSLAction.toPermHom

/-- The action of `PSL(2, F_4)` on the projective line is faithful (proved). -/
-- Reference: mathlib pin v4.35.0-rc3, `Matrix.ProjectiveSpecialLinearGroup.toPermHom_injective`
-- (faithful action on the projective line) + `Equiv.permCongrHom` injectivity.
theorem psl24ToPerm5_injective : Function.Injective psl24ToPerm5 := by
  intro x y h
  apply Matrix.ProjectiveSpecialLinearGroup.toPermHom_injective
  apply (Equiv.permCongrHom psl24LineEquiv).injective
  exact h

set_option linter.style.haveILetI false in
-- Reference: [Wilson] GTM 251, ch. 1; `A_5 ≅ PSL(2, F_4)`: the faithful action on
-- the 5 points of the projective line embeds `PSL(2, F_4)` into `S_5`; perfectness
-- puts the image in `A_5`; both have order 60.
/-- **The exceptional isomorphism `A_5 ≅ PSL(2, F_4)`** (proved). -/
theorem PSL_2_4_iso_alternatingGroup_fin5 :
    Nonempty (PSL(2, GaloisField 2 2) ≃* alternatingGroup (Fin 5)) := by
  haveI : NeZero 2 := ⟨Nat.succ_ne_zero 1⟩
  haveI : Fintype (GaloisField 2 2) := Fintype.ofFinite _
  have hperf : commutator (PSL(2, GaloisField 2 2)) = ⊤ :=
    SL2Simple.PSL_commutator_eq_top exists_sq_ne_one_galoisField_2_2
  have hrange : psl24ToPerm5.range ≤ alternatingGroup (Fin 5) := by
    have h1 : psl24ToPerm5.range =
        Subgroup.map psl24ToPerm5 (⊤ : Subgroup (PSL(2, GaloisField 2 2))) :=
      MonoidHom.range_eq_map psl24ToPerm5
    have h2 : Subgroup.map psl24ToPerm5 (⊤ : Subgroup (PSL(2, GaloisField 2 2))) =
        Subgroup.map psl24ToPerm5 (commutator (PSL(2, GaloisField 2 2))) :=
      Eq.subst (motive := fun H => Subgroup.map psl24ToPerm5
          (⊤ : Subgroup (PSL(2, GaloisField 2 2))) = Subgroup.map psl24ToPerm5 H)
        hperf.symm rfl
    have h3 : Subgroup.map psl24ToPerm5 (commutator (PSL(2, GaloisField 2 2))) =
        ⁅psl24ToPerm5.range, psl24ToPerm5.range⁆ :=
      (Subgroup.map_commutator ⊤ ⊤ psl24ToPerm5).trans
        (congrArg (fun H => ⁅H, H⁆) (MonoidHom.range_eq_map psl24ToPerm5).symm)
    have h4 : ⁅psl24ToPerm5.range, psl24ToPerm5.range⁆ ≤
        commutator (Equiv.Perm (Fin 5)) :=
      Subgroup.commutator_mono le_top le_top
    exact (h1.trans (h2.trans h3)).le.trans
      (h4.trans alternatingGroup.commutator_perm_le)
  have hcard : Nat.card ↥psl24ToPerm5.range = Nat.card ↥(alternatingGroup (Fin 5)) :=
    ((Nat.card_congr (MonoidHom.ofInjective psl24ToPerm5_injective).toEquiv).symm.trans
      card_PSL_2_galoisField_2_2).trans card_alternatingGroup_fin5.symm
  have heq : psl24ToPerm5.range = alternatingGroup (Fin 5) :=
    Subgroup.eq_of_le_of_card_ge hrange
      (Eq.subst (motive := fun n => n ≤ Nat.card ↥psl24ToPerm5.range) hcard (Nat.le_refl _))
  exact ⟨(MonoidHom.ofInjective psl24ToPerm5_injective).trans
    (MulEquiv.subgroupCongr heq)⟩

end BoringMath


