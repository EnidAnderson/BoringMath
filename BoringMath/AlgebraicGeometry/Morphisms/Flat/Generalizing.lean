/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Specialization lifting for flat maps of affine schemes

A flat map of affine schemes lifts specializations: every specialization
of the image of a point lifts to a specialization of the point. This is
the affine case of the going-down property of flat ring maps.

## References
* Stacks Project, tags 00HV–00HX (going down for flat ring maps).
  REVIEW(citation): pin down the exact tag.
-/

universe u

namespace AlgebraicGeometry

-- Reference: Stacks Project, tags 00HV–00HX (going down for flat ring
-- maps: flat maps lift specializations of primes).
-- REVIEW(citation): pin down the exact tag.
/-- **Flat maps of affine schemes lift specializations**: for a flat map
of affine schemes, every specialization of the image of a point lifts to
a specialization of the point. -/
theorem exists_specializes_of_flat_specMap {R S : CommRingCat.{u}}
    {φ : R ⟶ S} [Flat (Spec.map φ)] (Q : Spec S) (P₀ : Spec R)
    (h : P₀ ⤳ (Spec.map φ) Q) :
    ∃ Q₀ : Spec S, Q₀ ⤳ Q ∧ (Spec.map φ) Q₀ = P₀ :=
  RingHom.Flat.generalizingMap_comap (Flat.SpecMap_iff.mp inferInstance) h

-- Reference: Stacks Project, tags 00HV–00HX (going down for flat ring
-- maps, transported along the isomorphism of an affine scheme with the
-- spectrum of its ring of sections).
-- REVIEW(citation): pin down the exact tag.
/-- **A flat morphism of affine schemes lifts specializations**: for a
flat morphism between affine schemes, every specialization of the image
of a point lifts to a specialization of the point. -/
theorem exists_specializes_of_flat_affine {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Flat f] [IsAffine X] [IsAffine Y] {x : X} {y' : Y}
    (h : y' ⤳ f x) : ∃ x' : X, x' ⤳ x ∧ f x' = y' := by
  have hf : (f.appTop).hom.Flat :=
    Eq.subst (motive := fun φ => φ.hom.Flat)
      (Scheme.Hom.app_eq_appLE f (U := ⊤)).symm
      (Flat.flat_appLE f (isAffineOpen_top Y) (isAffineOpen_top X) le_rfl)
  have hflat : Flat (Spec.map f.appTop) := Flat.SpecMap_iff.mpr hf
  have hnatur : ∀ z : X, (Spec.map f.appTop) ((X.isoSpec).hom.base z) =
      (Y.isoSpec).hom.base (f z) :=
    fun z => congrArg (fun φ => φ.base z) (Scheme.isoSpec_hom_naturality f)
  have hy : (Y.isoSpec).hom.base y' ⤳ (Spec.map f.appTop) ((X.isoSpec).hom.base x) :=
    Eq.subst (motive := fun q => (Y.isoSpec).hom.base y' ⤳ q)
      (hnatur x).symm
      (Specializes.map h (Y.isoSpec).hom.continuous)
  obtain ⟨Q₀, hQ₀spec, hQ₀img⟩ :=
    exists_specializes_of_flat_specMap (φ := f.appTop) ((X.isoSpec).hom.base x)
      ((Y.isoSpec).hom.base y') hy
  have hinv : (X.isoSpec).inv.base ((X.isoSpec).hom.base x) = x :=
    congrArg (fun φ => φ.base x) (X.isoSpec.hom_inv_id)
  refine ⟨(X.isoSpec).inv.base Q₀, ?_, ?_⟩
  · exact Eq.subst (motive := fun z => (X.isoSpec).inv.base Q₀ ⤳ z) hinv
      (Specializes.map hQ₀spec (X.isoSpec).inv.continuous)
  · have hx'hom : (X.isoSpec).hom.base ((X.isoSpec).inv.base Q₀) = Q₀ :=
      congrArg (fun φ => φ.base Q₀) (X.isoSpec.inv_hom_id)
    have h1 : (Y.isoSpec).hom.base (f ((X.isoSpec).inv.base Q₀)) =
        (Y.isoSpec).hom.base y' :=
      Eq.trans (Eq.symm (hnatur _))
        (Eq.trans (congrArg (Spec.map f.appTop) hx'hom) hQ₀img)
    refine Eq.trans (Eq.symm
      (congrArg (fun φ => φ.base (f ((X.isoSpec).inv.base Q₀)))
        (Y.isoSpec.hom_inv_id))) ?_
    refine Eq.trans (congrArg (Y.isoSpec).inv.base h1) ?_
    exact congrArg (fun φ => φ.base y') (Y.isoSpec.hom_inv_id)

end AlgebraicGeometry
