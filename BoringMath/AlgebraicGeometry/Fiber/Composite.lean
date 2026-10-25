/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.AlgebraicGeometry.Fiber

/-!
# The fiber of a composite

The fiber of a composite at a point is the preimage of the fiber of the
second morphism under the first: the comparison map from the fiber of the
composite to the fiber of the second morphism lies over the first morphism,
the square of the comparison map is cartesian, and the fiber of the
composite is the fiber product of the first morphism with the embedding of
the fiber.

## References
* [EGA I] A. Grothendieck, J. A. Dieudonné, *Éléments de géométrie
  algébrique I: Le langage des schémas*, ch. 1 (the fiber of a composite
  is the preimage of the fiber).
  REVIEW(citation): pin down the section.
-/

universe u

namespace AlgebraicGeometry

open CategoryTheory Limits

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (P : Z)

-- Reference: [EGA I], ch. 1 (the fiber of a composite is the preimage of
-- the fiber of the second morphism under the first).
-- REVIEW(citation): pin down the section.
-- The comparison map assembles from limit data; the map is noncomputable.
/-- **The comparison map of the fiber of a composite**: the map from the
fiber of the composite at a point to the fiber of the second morphism at
the point, induced by the first morphism. -/
noncomputable def fiberComposite :
    Scheme.Hom.fiber (f ≫ g) P ⟶ Scheme.Hom.fiber g P :=
  ((IsPullback.of_hasPullback g (Z.fromSpecResidueField P)).flip).lift
    ((f ≫ g).fiberToSpecResidueField P) ((f ≫ g).fiberι P ≫ f)
    (Eq.trans
      (Eq.symm (IsPullback.of_hasPullback (f ≫ g)
        (Z.fromSpecResidueField P)).w)
      (Eq.symm (Category.assoc ((f ≫ g).fiberι P) f g)))

-- Reference: [EGA I], ch. 1 (the comparison map of the fiber of a
-- composite restricts the first morphism to the fibers).
-- REVIEW(citation): pin down the section.
/-- The comparison map of the fiber of a composite restricts the first
morphism to the fibers. -/
theorem fiberComposite_fiberι :
    fiberComposite f g P ≫ (g.fiberι P) = (f ≫ g).fiberι P ≫ f :=
  ((IsPullback.of_hasPullback g (Z.fromSpecResidueField P)).flip).lift_snd
    _ _ _

-- Reference: [EGA I], ch. 1 (the comparison map of the fiber of a
-- composite lies over the point).
-- REVIEW(citation): pin down the section.
/-- The comparison map of the fiber of a composite lies over the point. -/
theorem fiberComposite_fiberToSpecResidueField :
    fiberComposite f g P ≫ (g.fiberToSpecResidueField P) =
      (f ≫ g).fiberToSpecResidueField P :=
  ((IsPullback.of_hasPullback g (Z.fromSpecResidueField P)).flip).lift_fst
    _ _ _

-- Reference: [EGA I], ch. 1 (the square of the comparison map of the
-- fiber of a composite is cartesian).
-- REVIEW(citation): pin down the section.
/-- **The fiber of a composite is the preimage of the fiber**: the square
of the comparison map of the fibers over the first morphism is a pullback
square. -/
theorem isPullback_fiberComposite :
    IsPullback (fiberComposite f g P) ((f ≫ g).fiberι P) (g.fiberι P) f :=
  IsPullback.of_right'
    ((IsPullback.of_hasPullback (f ≫ g) (Z.fromSpecResidueField P)).flip)
    ((IsPullback.of_hasPullback g (Z.fromSpecResidueField P)).flip)

-- Reference: [EGA I], ch. 1 (the fiber of a composite is the fiber
-- product of the first morphism with the embedding of the fiber).
-- REVIEW(citation): pin down the section.
-- The iso assembles from limit data; it is noncomputable.
/-- **The fiber of a composite is the preimage of the fiber**, as an
isomorphism: the fiber of the composite at a point is the fiber product
of the first morphism with the embedding of the fiber of the second
morphism. -/
noncomputable def fiberCompositeIso :
    Scheme.Hom.fiber (f ≫ g) P ≅ pullback f (g.fiberι P) :=
  (isPullback_fiberComposite f g P).isoPullback ≪≫ pullbackSymmetry _ _

end AlgebraicGeometry
