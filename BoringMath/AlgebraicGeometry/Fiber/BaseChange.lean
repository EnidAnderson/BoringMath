/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.AlgebraicGeometry.Fiber

/-!
# The base change of the scheme-theoretic fiber

Given a cartesian square and a point of the base, the fibers base-change: the
fiber of the vertical morphism at the point maps to the fiber of the given
morphism at the image point, over the map of the spectra of the residue
fields, and the square of the base change is cartesian. The base-changed
fiber is the fiber product of the fiber with the spectrum of the residue
field of the point.

## References
* [EGA I] A. Grothendieck, J. A. Dieudonné, *Éléments de géométrie
  algébrique I: Le langage des schémas*, ch. 1 (base change of fibers).
  REVIEW(citation): pin down the section.
-/

universe u

namespace AlgebraicGeometry

open CategoryTheory Limits

variable {P X Y Z : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}

-- Reference: [EGA I], ch. 1 (the fibers of a cartesian square base-change).
-- REVIEW(citation): pin down the section.
-- The base change of the fiber assembles the fiber from limit data; the map
-- is noncomputable.
/-- **The base-change map of the fibers**: for a cartesian square and a
point of the base, the map from the fiber of the vertical morphism at the
point to the fiber of the given morphism at the image point, induced by
the cartesian map. -/
noncomputable def fiberBaseChange (h : IsPullback fst snd f g) (y : Y) :
    Scheme.Hom.fiber snd y ⟶ Scheme.Hom.fiber f (g y) :=
  pullback.map snd (Y.fromSpecResidueField y) f (Z.fromSpecResidueField (g y))
    fst (Spec.map (g.residueFieldMap y)) g h.w.symm
    (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField g y).symm

-- Reference: [EGA I], ch. 1 (the base-change map of the fibers restricts
-- the cartesian map).
-- REVIEW(citation): pin down the section.
/-- The base-change map of the fibers restricts the cartesian map: the
fiber of the base change embeds into the base-changed scheme. -/
theorem fiberBaseChange_fiberι (h : IsPullback fst snd f g) (y : Y) :
    fiberBaseChange h y ≫ (f.fiberι (g y)) = (snd.fiberι y) ≫ fst :=
  pullback.lift_fst _ _ _

-- Reference: [EGA I], ch. 1 (the base-change map of the fibers lies over
-- the map of the spectra of the residue fields).
-- REVIEW(citation): pin down the section.
/-- The base-change map of the fibers lies over the map of the spectra of
the residue fields. -/
theorem fiberBaseChange_fiberToSpecResidueField (h : IsPullback fst snd f g)
    (y : Y) :
    fiberBaseChange h y ≫ (f.fiberToSpecResidueField (g y)) =
      (snd.fiberToSpecResidueField y) ≫ Spec.map (g.residueFieldMap y) :=
  pullback.lift_snd _ _ _

-- Reference: [EGA I], ch. 1 (the square of the base change of the fibers
-- is cartesian).
-- REVIEW(citation): pin down the section.
/-- **The base change of the fiber is cartesian**: the square of the
base-change map of the fibers over the map of the spectra of the residue
fields is a pullback square. -/
theorem isPullback_fiberBaseChange (h : IsPullback fst snd f g) (y : Y) :
    IsPullback (fiberBaseChange h y) (snd.fiberToSpecResidueField y)
      (f.fiberToSpecResidueField (g y)) (Spec.map (g.residueFieldMap y)) :=
  isPullback_fiberToSpecResidueField_of_isPullback h y

-- Reference: [EGA I], ch. 1 (the base-changed fiber is the fiber product
-- of the fiber with the spectrum of the residue field of the point).
-- REVIEW(citation): pin down the section.
-- The iso assembles from limit data; it is noncomputable.
/-- **The base-change iso of the fibers**: the fiber of the vertical
morphism at the point is the fiber product of the fiber of the given
morphism at the image point with the spectrum of the residue field of the
point. -/
noncomputable def fiberBaseChangeIso (h : IsPullback fst snd f g) (y : Y) :
    Scheme.Hom.fiber snd y ≅
      pullback (f.fiberToSpecResidueField (g y))
        (Spec.map (g.residueFieldMap y)) :=
  (isPullback_fiberBaseChange h y).isoPullback

end AlgebraicGeometry
