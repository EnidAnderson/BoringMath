/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
import Mathlib.AlgebraicGeometry.Limits
import BoringMath.AlgebraicGeometry.Scheme.Hom

/-!
# Rational equivalence of cycles (I.1, part 1)

The structure-of-record for **rational equivalence** on cycles of a scheme
`X` (ticket I.1, #281) is the A¹-family presentation: two cycles `c, d` are
rationally equivalent iff `c - d = i₀*γ - i₁*γ` for some cycle `γ` on
`X × 𝔸¹`, where `i₀, i₁ : X → X × 𝔸¹` are the zero/one sections and `i_t*`
is pullback along the section (precomposition on points — well defined
because the section has a retraction, so supports stay locally finite).

The equivalence with Fulton's div-of-rational-functions definition
(Fulton, ch. 1, §1.3) is a NAMED Tier-2 peel (multiple-presentations
directive, cf. the ratified C.1 ruling): recorded in the PR note, not built
here.

This module provides: the affine line `𝔸¹ = Spec ℤ[t]` and its structure
morphism to the terminal scheme, the zero/one sections, the product
`X × 𝔸¹`, the section inclusions, the pullback of a cycle along a section
(as an `AddMonoidHom`), the difference hom `γ ↦ i₀*γ - i₁*γ`, and the
**rational-equivalence subgroup** of the cycle group (its range).

## References
* W. Fulton, *Intersection Theory*, 2nd ed., Springer 1998, ch. 1, §1.3
  (rational equivalence; the family-over-P¹ characterization in ch. 10 —
  REVIEW(citation): pin Prop. 10.3? in review; the A¹-sections form is the
  structure-of-record here).
* Stacks Project, Chow Homology, Def. 42.8.1 (tag 02QR) and the
  rational-equivalence section (tags 02R9 ff.).
  REVIEW(citation): pin the tags in review.
* Hartshorne, *Algebraic Geometry*, GTM 52, App. A (Chow groups).
  REVIEW(citation): pin the section.
-/

universe u

namespace AlgebraicGeometry

open CategoryTheory Limits

-- Reference: Stacks Project, Schemes, the terminal object `Spec ℤ`
-- (tag 01J? — REVIEW(citation): pin); mathlib pins it as `specULiftZIsTerminal`.
-- `noncomputable`: `Spec` is choice-backed at the pin.
/-- The terminal scheme `Spec ℤ` in `Scheme.{u}` (via `ULift ℤ`). -/
noncomputable def specZ : Scheme.{u} := Spec (CommRingCat.of (ULift.{u} ℤ))

-- Reference: the affine line `𝔸¹ = Spec ℤ[t]` (Fulton ch. 1, §1.3 uses
-- `X × 𝔸¹`; Stacks tag 01J? — REVIEW(citation)).
-- `noncomputable`: `Spec` is choice-backed at the pin.
/-- The **affine line** `𝔸¹ = Spec ℤ[t]`. -/
noncomputable def affineLine : Scheme.{u} :=
  Spec (CommRingCat.of (MvPolynomial (ULift.{u} Unit) (ULift.{u} ℤ)))

-- Reference: the structure morphism `𝔸¹ → Spec ℤ` (the terminal map).
/-- The structure morphism `𝔸¹ ⟶ Spec ℤ` (the terminal map; equal to
`Spec.map` of the inclusion `ℤ → ℤ[t]`, see `affineLineProj_eq_specMap`). -/
noncomputable def affineLineProj : affineLine ⟶ specZ := specULiftZIsTerminal.from affineLine

-- Reference: the structure morphism as contravariant `Spec` of the inclusion
-- `ℤ → ℤ[t]` (`MvPolynomial.C`); uniqueness of maps into the terminal.
/-- The structure morphism `𝔸¹ ⟶ Spec ℤ` is `Spec.map` of `MvPolynomial.C`. -/
theorem affineLineProj_eq_specMap : affineLineProj =
    Spec.map (CommRingCat.ofHom (MvPolynomial.C (R := ULift.{u} ℤ) (σ := ULift.{u} Unit))) :=
  specULiftZIsTerminal.hom_ext _ _

-- Reference: the zero/one sections of the affine line (Fulton ch. 1, §1.3:
-- the points `0, 1 ∈ 𝔸¹`).
/-- The **zero section** `Spec ℤ ⟶ 𝔸¹` (ring map `ℤ[t] → ℤ`, `t ↦ 0`). -/
noncomputable def affineLineZero : specZ ⟶ affineLine :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.eval (fun _ => (0 : ULift.{u} ℤ))))

-- Reference: as above, `t ↦ 1`.
/-- The **one section** `Spec ℤ ⟶ 𝔸¹` (ring map `ℤ[t] → ℤ`, `t ↦ 1`). -/
noncomputable def affineLineOne : specZ ⟶ affineLine :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.eval (fun _ => (1 : ULift.{u} ℤ))))

-- Reference: Fulton ch. 1, §1.3 (sections of the affine line are sections of
-- the structure morphism); uniqueness of endomaps of the terminal scheme.
-- REVIEW(citation): pin.
/-- The zero section is a section of the structure morphism. -/
theorem affineLineZero_proj : affineLineZero ≫ affineLineProj = 𝟙 specZ :=
  specULiftZIsTerminal.hom_ext _ _

-- Reference: as above.
/-- The one section is a section of the structure morphism. -/
theorem affineLineOne_proj : affineLineOne ≫ affineLineProj = 𝟙 specZ :=
  specULiftZIsTerminal.hom_ext _ _

-- Reference: `X × 𝔸¹` over the terminal base `Spec ℤ` (Fulton ch. 1, §1.3).
/-- The product `X × 𝔸¹` over `Spec ℤ`. `noncomputable`: the fiber product
carries chosen limit data. -/
noncomputable def prodAffineLine (X : Scheme.{u}) : Scheme.{u} :=
  pullback (specULiftZIsTerminal.from X) (specULiftZIsTerminal.from affineLine)

-- Reference: the section inclusion `X ≅ X × {t} → X × 𝔸¹` (Fulton ch. 1,
-- §1.3: the maps `i₀, i₁`).
-- REVIEW(citation): pin.
/-- The inclusion `X × {t} ≅ X ⟶ X × 𝔸¹` induced by a section `t` of the
affine line: the lift of `(𝟙 X, X → Spec ℤ ≫ t)` against the projections of
the fiber product. `noncomputable`: the fiber product carries chosen limit
data. -/
noncomputable def sectionIncl (X : Scheme.{u}) (t : specZ ⟶ affineLine)
    (ht : t ≫ affineLineProj = 𝟙 specZ) : X ⟶ prodAffineLine X :=
  pullback.lift (𝟙 X) (specULiftZIsTerminal.from X ≫ t)
    (Eq.trans (Category.id_comp _)
      (Eq.trans (Category.comp_id _).symm
        (Eq.trans (congrArg (specULiftZIsTerminal.from X ≫ ·) ht.symm)
          (Category.assoc _ _ _).symm)))

-- Reference: the section inclusion is a section of the first projection
-- (the pullback lift law).
/-- The section inclusion composed with the first projection is the
identity. -/
theorem sectionIncl_fst (X : Scheme.{u}) (t : specZ ⟶ affineLine)
    (ht : t ≫ affineLineProj = 𝟙 specZ) :
    sectionIncl X t ht ≫ pullback.fst (specULiftZIsTerminal.from X)
      (specULiftZIsTerminal.from affineLine) = 𝟙 X := by
  change pullback.lift (𝟙 X) (specULiftZIsTerminal.from X ≫ t) _ ≫
    pullback.fst (specULiftZIsTerminal.from X) (specULiftZIsTerminal.from affineLine) = 𝟙 X
  exact pullback.lift_fst _ _ _

-- Reference: the section inclusion composed with the second projection is
-- the terminal map of `X` composed with `t` (the pullback lift law).
/-- The section inclusion composed with the second projection is
`X → Spec ℤ` composed with `t`. -/
theorem sectionIncl_snd (X : Scheme.{u}) (t : specZ ⟶ affineLine)
    (ht : t ≫ affineLineProj = 𝟙 specZ) :
    sectionIncl X t ht ≫ pullback.snd (specULiftZIsTerminal.from X)
      (specULiftZIsTerminal.from affineLine) =
      specULiftZIsTerminal.from X ≫ t := by
  change pullback.lift (𝟙 X) (specULiftZIsTerminal.from X ≫ t) _ ≫
    pullback.snd (specULiftZIsTerminal.from X) (specULiftZIsTerminal.from affineLine) =
      specULiftZIsTerminal.from X ≫ t
  exact pullback.lift_snd _ _ _

variable {X W : Scheme.{u}}

-- Reference: a section of a morphism is injective on points (the retraction
-- law, applied through `Scheme.Hom.comp_apply` and `Scheme.Hom.id_apply`).
/-- The underlying point map of a section `i` (with retraction `r`) is
injective. -/
theorem section_injective (i : X ⟶ W) (r : W ⟶ X) (h : i ≫ r = 𝟙 X) :
    Function.Injective i.base := by
  have h1 : ∀ x : ↥X, r.base (i.base x) = x := by
    intro x
    have h2 := congrFun (congrArg (fun (g : X ⟶ X) => (g : ↥X → ↥X)) h) x
    exact Eq.trans (Scheme.Hom.comp_apply i r x) (Eq.trans h2 (Scheme.Hom.id_apply x))
  intro a b hab
  exact Eq.trans (h1 a).symm (Eq.trans (congrArg r.base hab) (h1 b))

-- Reference: Fulton ch. 1, §1.3 (pullback of a cycle along the section
-- `i_t : X → X × 𝔸¹`); here as precomposition on points, which is well
-- defined because the section is injective (has a retraction), so the support
-- stays locally finite.
-- REVIEW(citation): pin.
/-- The **pullback of a cycle along a section** `i` with retraction `r`:
precomposition on points, `x ↦ γ (i x)`. -/
def sectionPullback (i : X ⟶ W) (r : W ⟶ X) (h : i ≫ r = 𝟙 X) (γ : AlgebraicCycle W ℤ) :
    AlgebraicCycle X ℤ :=
  { toFun := fun x => γ (i.base x)
    supportWithinDomain' := Set.subset_univ _
    supportLocallyFiniteWithinDomain' := by
      intro z _
      obtain ⟨t, ht, hfin⟩ := γ.supportLocallyFiniteWithinDomain' (i.base z) (Set.mem_univ _)
      refine ⟨i.base ⁻¹' t, (Scheme.Hom.continuous i).continuousAt.preimage_mem_nhds ht, ?_⟩
      refine Set.Finite.subset
        (Set.Finite.preimage_embedding ⟨i.base, section_injective i r h⟩ hfin) ?_
      intro w hw
      exact Set.mem_preimage.mpr
        ((Set.mem_inter_iff _ _ _).mpr ⟨hw.1, Function.mem_support.mpr hw.2⟩) }

-- Reference: Fulton ch. 1, §1.3 (the pullback along a section preserves
-- zero); pointwise (`Pi.zero_apply`).
/-- The pullback of the zero cycle along a section is the zero cycle. -/
theorem sectionPullback_zero (i : X ⟶ W) (r : W ⟶ X) (h : i ≫ r = 𝟙 X) :
    sectionPullback i r h 0 = 0 := by
  apply Function.locallyFinsuppWithin.ext
  intro x
  exact Eq.trans (Pi.zero_apply (M := fun _ => ℤ) (i.base x))
    (Pi.zero_apply (M := fun _ => ℤ) x).symm

-- Reference: Fulton ch. 1, §1.3; pointwise addition (`Pi.add_apply`).
/-- The pullback of a sum of cycles along a section is the sum of the
pullbacks. -/
theorem sectionPullback_add (i : X ⟶ W) (r : W ⟶ X) (h : i ≫ r = 𝟙 X)
    (γ δ : AlgebraicCycle W ℤ) :
    sectionPullback i r h (γ + δ) = sectionPullback i r h γ + sectionPullback i r h δ := by
  apply Function.locallyFinsuppWithin.ext
  intro x
  exact Pi.add_apply (γ : ↥W → ℤ) (δ : ↥W → ℤ) (i.base x)

-- Reference: Fulton ch. 1, §1.3 (pullback along a section as a group hom).
/-- The pullback along a section, bundled as an `AddMonoidHom`. -/
def sectionPullbackHom (i : X ⟶ W) (r : W ⟶ X) (h : i ≫ r = 𝟙 X) :
    AlgebraicCycle W ℤ →+ AlgebraicCycle X ℤ where
  toFun := sectionPullback i r h
  map_zero' := sectionPullback_zero i r h
  map_add' := fun γ δ => sectionPullback_add i r h γ δ

-- Reference: Fulton ch. 1, §1.3 (rational equivalence via `X × 𝔸¹`: the
-- difference `i₀*γ - i₁*γ`).
-- REVIEW(citation): pin the family characterization (ch. 10 — REVIEW).
/-- The **rational-equivalence hom**: `γ ↦ i₀*γ - i₁*γ` from the cycles on
`X × 𝔸¹` to the cycles on `X`. `noncomputable`: the product `X × 𝔸¹` carries
chosen limit data. -/
noncomputable def rationalEquivalenceHom (X : Scheme.{u}) :
    AlgebraicCycle (prodAffineLine X) ℤ →+ AlgebraicCycle X ℤ :=
  sectionPullbackHom (sectionIncl X affineLineZero affineLineZero_proj)
      (pullback.fst _ _) (sectionIncl_fst X affineLineZero affineLineZero_proj) -
    sectionPullbackHom (sectionIncl X affineLineOne affineLineOne_proj)
      (pullback.fst _ _) (sectionIncl_fst X affineLineOne affineLineOne_proj)

-- Reference: computation step (the difference hom applied); `rfl` only in
-- this primitive definitional lemma (`AddMonoidHom.sub_apply`).
/-- The rational-equivalence hom applied to `γ` is `i₀*γ - i₁*γ`. -/
theorem rationalEquivalenceHom_apply (X : Scheme.{u}) (γ : AlgebraicCycle (prodAffineLine X) ℤ) :
    rationalEquivalenceHom X γ =
      sectionPullbackHom (sectionIncl X affineLineZero affineLineZero_proj)
          (pullback.fst _ _) (sectionIncl_fst X affineLineZero affineLineZero_proj) γ -
        sectionPullbackHom (sectionIncl X affineLineOne affineLineOne_proj)
          (pullback.fst _ _) (sectionIncl_fst X affineLineOne affineLineOne_proj) γ :=
  rfl

-- Reference: Fulton ch. 1, §1.3 (rational equivalence as a subgroup of the
-- cycle group); the range of the difference hom.
-- REVIEW(citation): pin.
/-- The **rational-equivalence subgroup** of the cycle group of `X`: the
range of `γ ↦ i₀*γ - i₁*γ`. `noncomputable`: via the noncomputable product. -/
noncomputable def rationalEquivalenceAddSubgroup (X : Scheme.{u}) :
    AddSubgroup (AlgebraicCycle X ℤ) :=
  (rationalEquivalenceHom X).range

end AlgebraicGeometry
