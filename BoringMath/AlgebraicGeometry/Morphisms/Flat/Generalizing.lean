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

end AlgebraicGeometry
