/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringMath.AlgebraicGeometry.Morphisms.Flat.Generalizing
import BoringMath.Topology.Sober.GenericPoints
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# The base change of the scheme-theoretic fiber

Given a cartesian square and a point of the base, the fibers base-change: the
fiber of the vertical morphism at the point maps to the fiber of the given
morphism at the image point, over the map of the spectra of the residue
fields, and the square of the base change is cartesian. The base-changed
fiber is the fiber product of the fiber with the spectrum of the residue
field of the point. The base-change map of the fibers is flat and
surjective: the base change is by the map of the spectra of the residue
fields.

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

-- Reference: [EGA IV] A. Grothendieck, J. A. Dieudonné, *Éléments de
-- géométrie algébrique IV: Étude locale des schémas et des morphismes de
-- schémas*, ch. 2 (flatness is stable under base change; a field
-- extension is flat).
-- REVIEW(citation): pin down the section.
-- The flatness instance assembles from limit data and the instance for
-- isomorphisms; it is noncomputable.
/-- **The base-change map of the fibers is flat**: the base change is by a
field extension — the map of the spectra of the residue fields — and
flatness is stable under base change. -/
noncomputable instance flat_fiberBaseChange (h : IsPullback fst snd f g)
    (y : Y) : Flat (fiberBaseChange h y) :=
  Eq.subst (motive := fun φ => Flat φ)
    (IsPullback.isoPullback_hom_fst (isPullback_fiberBaseChange h y))
    (Flat.comp
      ((IsPullback.isoPullback (isPullback_fiberBaseChange h y)).hom)
      (pullback.fst (f.fiberToSpecResidueField (g y))
        (Spec.map (g.residueFieldMap y))))

-- Reference: [EGA IV], ch. 2 (surjectivity is stable under base change;
-- the map of the spectra of the residue fields is surjective).
-- REVIEW(citation): pin down the section.
/-- **The base-change map of the fibers is surjective**: the base change
is by the map of the spectra of the residue fields, a surjective map of
one-point spectra, and surjectivity is stable under base change. -/
theorem surjective_fiberBaseChange (h : IsPullback fst snd f g) (y : Y) :
    Function.Surjective (fiberBaseChange h y).base := by
  intro ξ
  have hc : (f.fiberToSpecResidueField (g y)).base ξ =
      (Spec.map (g.residueFieldMap y)).base
        (IsLocalRing.closedPoint (Y.residueField y)) :=
    Subsingleton.elim _ _
  obtain ⟨p, hp, -⟩ := Scheme.exists_preimage_of_isPullback
    (isPullback_fiberBaseChange h y) ξ
    (IsLocalRing.closedPoint (Y.residueField y)) hc
  exact ⟨p, hp⟩

-- Reference: [EGA IV], ch. 2 (the base change by a field extension
-- preserves generic points of irreducible components).
-- REVIEW(citation): pin down the section.
/-- **The base-change map of the fibers carries generic points to
generic points**: the image of a generic point of an irreducible
component of the fiber of the vertical morphism is a generic point of an
irreducible component of the fiber of the given morphism. The image
point lies in an irreducible component; the generic point of that
component specializes to the image point; the flat base-change map lifts
the specialization, and the lifted specialization into a generic point
is the generic point. -/
theorem mem_genericPoints_fiberBaseChange (h : IsPullback fst snd f g)
    (y : Y) {η : ↥(Scheme.Hom.fiber snd y)}
    (hη : η ∈ genericPoints ↥(Scheme.Hom.fiber snd y)) :
    (fiberBaseChange h y).base η ∈
      genericPoints ↥(Scheme.Hom.fiber f (g y)) := by
  have hspec : (genericPoints.ofComponent
      (⟨irreducibleComponent ((fiberBaseChange h y).base η),
        irreducibleComponent_mem_irreducibleComponents _⟩ :
        irreducibleComponents ↥(Scheme.Hom.fiber f (g y)))).1 ⤳
      (fiberBaseChange h y).base η :=
    (genericPoints.isGenericPoint_ofComponent _).specializes mem_irreducibleComponent
  obtain ⟨ρ, hρspec, hρimg⟩ :=
    exists_specializes_of_flat (fiberBaseChange h y) hspec
  have hρε : ρ = η :=
    eq_of_specializes_of_mem_genericPoints hη hρspec
  exact Eq.subst (motive := fun q =>
      q ∈ genericPoints ↥(Scheme.Hom.fiber f (g y)))
    (Eq.trans (congrArg (fiberBaseChange h y).base hρε.symm) hρimg).symm
    (genericPoints.ofComponent
      (⟨irreducibleComponent ((fiberBaseChange h y).base η),
        irreducibleComponent_mem_irreducibleComponents _⟩ :
        irreducibleComponents ↥(Scheme.Hom.fiber f (g y)))).2

end AlgebraicGeometry
