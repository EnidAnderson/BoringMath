/-
Copyright (c) 2026 Enid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.CategoryTheory.Triangulated.Triangulated
import Mathlib.CategoryTheory.Triangulated.LocalizingSubcategory
import Mathlib.CategoryTheory.Localization.Triangulated
import Mathlib.CategoryTheory.Localization.Predicate

/-!
# The Verdier quotient, pinned at the mathlib API (statement layer)

T.1 (#23) audit result: mathlib at the pin `v4.35.0-rc3` already carries the
triangulated substrate and the Verdier localization: `CategoryTheory.Pretriangulated`,
`CategoryTheory.IsTriangulated` (octahedron axiom TR4),
`CategoryTheory.ObjectProperty.IsVerdierRightLocalizing` /
`IsVerdierLeftLocalizing` (the thick-subcategory side), and
`CategoryTheory.Triangulated.Localization.pretriangulated` (a localization
functor inverting a triangulation-compatible class of morphisms yields a
pretriangulated target). This module pins that API as named statement-layer
declarations for the program, with the universal property of the quotient via
`CategoryTheory.Localization.lift` and `CategoryTheory.Localization.Lifting.iso`.

## References
* [Verdier] J.-L. Verdier, *Des catégories dérivées des catégories abéliennes*,
  Astérisque 239, Société Mathématique de France, 1996 (the reference used by
  mathlib's own `CategoryTheory/Localization/Triangulated.lean`).
* [Neeman] A. Neeman, *Triangulated Categories*, Annals of Math. Studies 148,
  Princeton University Press, 2001, ch. 9 (Verdier quotients).
* [Weibel] C. Weibel, *An Introduction to Homological Algebra*, Cambridge
  University Press, 1994, ch. 10 (the derived category as a Verdier quotient).
-/

universe u

namespace BoringMath

open CategoryTheory

-- Reference: [Verdier], Astérisque 239, ch. II (the quotient category C/S).
-- REVIEW(citation): pin the exact chapter/section in review.
/-- A **Verdier localization datum**: a category `C`, a class `W` of morphisms,
and a localization functor `L : C ⥤ D` at `W`. -/
structure VerdierLocalization (C D : Type u) [Category.{u} C] [Category.{u} D]
    (W : MorphismProperty C) (L : C ⥤ D) [L.IsLocalization W] : Type u where

-- Reference: [Neeman], ch. 9 (the Verdier quotient of a triangulated category
-- by a thick subcategory is triangulated).
/-- The target of a Verdier localization of a pretriangulated category is
pretriangulated — mathlib's `Triangulated.Localization.pretriangulated` pinned
as a named declaration. -/
@[instance_reducible]
def verdierQuotient_pretriangulated {C D : Type u} [Category.{u} C] [Category.{u} D]
    {W : MorphismProperty C} {L : C ⥤ D} [L.IsLocalization W]
    [HasShift C ℤ] [Preadditive C] [Limits.HasZeroObject C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [W.IsCompatibleWithTriangulation] [W.HasLeftCalculusOfFractions]
    [HasShift D ℤ] [L.CommShift ℤ] [Limits.HasZeroObject D] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [L.Additive] :
    Pretriangulated D :=
  Triangulated.Localization.pretriangulated L W

-- Reference: [Verdier], Astérisque 239, ch. II (universal property of the
-- quotient functor).
-- REVIEW(citation): pin the exact proposition in review.
/-- **Universal property of the Verdier quotient, existence part.** Any functor
out of `C` that inverts `W` lifts through the quotient functor `L`.
`noncomputable`: mathlib's `Localization.lift` is choice-backed at the pin
(chosen localization construction), flagged per STYLE §2.3. -/
noncomputable def verdierQuotient_lift {C D E : Type u} [Category.{u} C] [Category.{u} D]
    [Category.{u} E] {W : MorphismProperty C} {L : C ⥤ D} [L.IsLocalization W]
    (F : C ⥤ E) (hF : W.IsInvertedBy F) : D ⥤ E :=
  Localization.lift F hF L

-- Reference: [Verdier], Astérisque 239, ch. II (universal property, the
-- factorization isomorphism).
/-- The lift factors `F` through `L` up to canonical isomorphism. -/
theorem verdierQuotient_fac {C D E : Type u} [Category.{u} C] [Category.{u} D]
    [Category.{u} E] {W : MorphismProperty C} {L : C ⥤ D} [L.IsLocalization W]
    (F : C ⥤ E) (hF : W.IsInvertedBy F) :
    Nonempty (L ⋙ Localization.lift F hF L ≅ F) :=
  ⟨Localization.Lifting.iso L W F (Localization.lift F hF L)⟩

end BoringMath
