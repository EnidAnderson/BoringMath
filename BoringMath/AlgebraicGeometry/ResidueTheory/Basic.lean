/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.AlgebraicGeometry.ResidueField
import BoringMath.AlgebraicGeometry.Scheme.Hom

/-!
# Residue theory: residue fields of sections and residue degrees (W.1)

The residue-field/residue-degree layer for sections: a section `i` with
retraction `r` (`i ≫ r = 𝟙`) has `residueFieldMap` an isomorphism, hence
`residueDegree = 1`. This is the base-change input for
`pushforward_sectionPullback` (I.2, #283) — the residue degree of `f × 𝔸¹`
at a section point equals that of `f`.

The algebraic residue *map* (residues of differentials, Serre duality) is the
W.4 station (#359); the analytic residue of a function at a pole is the D-line
(D.13, #366); the cap/cup yoga tying them to duality is CAPCUP.1 (#369).

## References
* Stacks Project, tag 01HX? (residue fields of morphisms of schemes),
  tag 01HW? — REVIEW(citation): pin the tags.
* Hartshorne, *Algebraic Geometry*, GTM 52, ch. I, §3? — REVIEW(citation).
* Serre, *Local Fields*, ch. II (residue field extensions). REVIEW(citation).
-/

universe u

namespace AlgebraicGeometry

open CategoryTheory

variable {X W : Scheme.{u}}

-- Reference: a section composed with its retraction is the identity, applied
-- at a point (the laws `Scheme.Hom.comp_apply`, `Scheme.Hom.id_apply`).
/-- The retraction of a section acts as the identity on points:
`r (i x) = x`. -/
theorem section_point_retraction (i : X ⟶ W) (r : W ⟶ X) (h : i ≫ r = 𝟙 X) (x : ↥X) :
    r (i x) = x :=
  Eq.trans (Scheme.Hom.comp_apply i r x).symm
    (Eq.trans (congrFun (congrArg (fun g : X ⟶ X => (g : ↥X → ↥X)) h) x)
      (Scheme.Hom.id_apply x))

-- Reference: the residue-field split of a section: `i.map (r.map y) = y`
-- (the comp law `residueFieldMap_comp` with `i ≫ r = 𝟙` and
-- `residueFieldMap_id`, cast along `section_point_retraction`'s index
-- `X.residueField (r (i x)) = X.residueField x`). Stacks tag 01HX? —
-- REVIEW(citation): pin.
/-- The residue-field map of a section is split-surjective: for every
`y : κ(x)`, `i.residueFieldMap x (r.residueFieldMap (i x) ((X.residueFieldCongr …).inv y)) = y`.
Proved from `Scheme.residueFieldMap_comp i r x` + `Scheme.Hom.residueFieldMap_congr h x`
+ `Scheme.residueFieldMap_id`, with the point identity `residueFieldCongr_trans_hom`
closing the cast roundtrip (proof irrelevance + `residueFieldCongr_refl`). -/
theorem residueFieldMap_section_split (i : X ⟶ W) (r : W ⟶ X) (h : i ≫ r = 𝟙 X) (x : ↥X)
    (y : X.residueField x) :
    i.residueFieldMap x (r.residueFieldMap (i x)
      ((X.residueFieldCongr (section_point_retraction i r h x)).inv y)) = y := by
  have hxx := section_point_retraction i r h x
  -- the point equation transported along `h : i ≫ r = 𝟙 X`
  have hp : (i ≫ r) x = (𝟙 X) x :=
    congrFun (congrArg (fun g : X ⟶ X => (g : ↥X → ↥X)) h) x
  -- the composite residue-field map computes as `r.residueFieldMap (i x) ≫ i.residueFieldMap x`
  have hcomp := Scheme.residueFieldMap_comp i r x
  have hpt : ∀ z : ↥(X.residueField (r (i x))),
      (i ≫ r).residueFieldMap x z =
        i.residueFieldMap x (r.residueFieldMap (i x) z) := by
    intro z
    exact congrFun (congrArg (fun q : X.residueField ((i ≫ r) x) ⟶ X.residueField x =>
      (q : ↥(X.residueField ((i ≫ r) x)) → ↥(X.residueField x))) hcomp) z
  -- along `h`, the composite residue-field map is the identity up to the point cast
  have hcong := Scheme.Hom.residueFieldMap_congr h x
  have hid := Scheme.residueFieldMap_id x
  have hpt2 : ∀ z : ↥(X.residueField (r (i x))),
      (i ≫ r).residueFieldMap x z = (X.residueFieldCongr hp).hom z := by
    intro z
    exact (congrFun (congrArg (fun q : X.residueField ((i ≫ r) x) ⟶ X.residueField x =>
      (q : ↥(X.residueField ((i ≫ r) x)) → ↥(X.residueField x))) hcong) z).trans
      (congrFun (congrArg (fun q : X.residueField ((i ≫ r) x) ⟶ X.residueField x =>
        (q : ↥(X.residueField ((i ≫ r) x)) → ↥(X.residueField x)))
        (congrArg (fun q : X.residueField x ⟶ X.residueField x =>
          (X.residueFieldCongr hp).hom ≫ q) hid)) z)
  -- hence the split equation up to the point congruence
  have hfinal : ∀ z : ↥(X.residueField (r (i x))),
      i.residueFieldMap x (r.residueFieldMap (i x) z) =
        (X.residueFieldCongr hp).hom z :=
    fun z => (hpt z).symm.trans (hpt2 z)
  -- the point congruence composed with its inverse is the identity
  have hkey : (X.residueFieldCongr hp).hom ((X.residueFieldCongr hxx).inv y) = y := by
    exact congrFun (congrArg (fun q : X.residueField x ⟶ X.residueField x =>
      (q : ↥(X.residueField x) → ↥(X.residueField x)))
      (Scheme.residueFieldCongr_trans_hom X hxx.symm hp)) y
  exact (hfinal _).trans hkey

-- Reference: a section's `residueFieldMap` is an isomorphism (field homs are
-- injective; the split gives surjectivity; `ConcreteCategory.isIso_iff_bijective`).
-- Stacks tag 01HX? — REVIEW(citation): pin.
/-- The residue-field map of a section is an isomorphism. -/
theorem isIso_residueFieldMap_section (i : X ⟶ W) (r : W ⟶ X) (h : i ≫ r = 𝟙 X) (x : ↥X) :
    IsIso (i.residueFieldMap x) := by
  have hxx := section_point_retraction i r h x
  have hinj : Function.Injective (i.residueFieldMap x) := RingHom.injective _
  have hsurj : Function.Surjective (i.residueFieldMap x) := by
    intro y
    refine ⟨r.residueFieldMap (i x) ((X.residueFieldCongr hxx).inv y),
      residueFieldMap_section_split i r h x y⟩
  exact (ConcreteCategory.isIso_iff_bijective _).mpr ⟨hinj, hsurj⟩

-- Reference: the residue degree of an isomorphism is 1 (the extension
-- κ(x)/κ(f x) is trivial); finrank transport `LinearEquiv.finrank_eq` +
-- `CommSemiring.finrank_self`. Stacks tag 01HX? — REVIEW(citation): pin.
set_option linter.style.haveILetI false in
/-- The finrank of the residue-field extension is 1 when the residue-field map
is an isomorphism. -/
theorem finrank_residueField_of_residueFieldMap_isIso (f : X ⟶ W) (x : ↥X)
    (hi : IsIso (f.residueFieldMap x)) :
    letI := (f.residueFieldMap x).hom.toAlgebra
    Module.finrank (W.residueField (f x)) (X.residueField x) = 1 := by
  letI := (f.residueFieldMap x).hom.toAlgebra
  have hbij : Function.Bijective (algebraMap (W.residueField (f x)) (X.residueField x)) :=
    (ConcreteCategory.isIso_iff_bijective (f.residueFieldMap x)).mp hi
  have he : (X.residueField x) ≃ₗ[W.residueField (f x)] (W.residueField (f x)) :=
    (LinearEquiv.ofBijective
      (Algebra.linearMap (W.residueField (f x)) (X.residueField x)) hbij).symm
  calc Module.finrank (W.residueField (f x)) (X.residueField x)
      = Module.finrank (W.residueField (f x)) (W.residueField (f x)) :=
        LinearEquiv.finrank_eq he
    _ = 1 := CommSemiring.finrank_self _

-- Reference: as above, stated for `residueDegree` itself (the instance passed
-- is the one `residueDegree` uses internally).
-- REVIEW(citation): pin.
/-- The residue degree of a morphism whose residue-field map is an isomorphism
is 1. -/
theorem residueDegree_of_residueFieldMap_isIso (f : X ⟶ W) (x : ↥X)
    (hi : IsIso (f.residueFieldMap x)) : f.residueDegree x = 1 :=
  finrank_residueField_of_residueFieldMap_isIso f x hi

-- Reference: the residue degree of a section is 1 (the residue-field extension
-- is trivial — `isIso_residueFieldMap_section` + `residueDegree_of_residueFieldMap_isIso`).
-- Stacks tag 01HX? — REVIEW(citation): pin.
/-- The residue degree of a section is 1. -/
theorem residueDegree_section (i : X ⟶ W) (r : W ⟶ X) (h : i ≫ r = 𝟙 X) (x : ↥X) :
    i.residueDegree x = 1 :=
  residueDegree_of_residueFieldMap_isIso i x (isIso_residueFieldMap_section i r h x)

end AlgebraicGeometry
