/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringMath.CategoryTheory.Abelian.GrothendieckGroup
import Mathlib.CategoryTheory.Abelian.Basic

/-!
# `K₀` functoriality — ticket #520 (TREE K.0/K.1)

`BoringMath.CategoryTheory.Abelian.GrothendieckGroup` landed `K0 A` for an
abelian category `A` with `K0.of`, `K0.of_shortExact`, and `K0.map`. The
K-line (TREE K.0–K.4) extends this to exact categories, Milnor K-theory, and
the Grothendieck–Witt/Witt rings. This module seeds the functoriality ring
of `K0`.

## References
* [Weibel] C. A. Weibel, *The K-book*, GSM 145, AMS 2013, ch. II §2
  (functoriality of `K₀`: `K₀(G ∘ F) = K₀(G) ∘ K₀(F)`).
* mathlib pin v4.35.0-rc3 + BoringMath pin: `CategoryTheory.K0.map`.
-/

namespace BoringMath

universe u v

open CategoryTheory

-- Reference: [Weibel], ch. II, Proposition 2.4 (`K₀` is functorial:
-- `K₀(GF) = K₀(G) K₀(F)`). TEMPORARY SORRY with peeling plan.
-- PEELING PLAN (#520): unfold `K0.map` to `freeAbelianMap` on isomorphism
-- classes; the composite law follows from `(F ⋙ G).isoClassesMap` factoring
-- through the two `isoClassesMap`s (each step is a `refine` of the
-- `liftEquiv` universal property already proved in `GrothendieckGroup.lean`).
/-- **`K₀` is functorial**: `K0.map (F ⋙ G) = (K0.map G) ∘ (K0.map F)`. -/
theorem K0.map_comp {A B C : Type u} [Category.{v} A] [Category.{v} B] [Category.{v} C]
    [Abelian A] [Abelian B] [Abelian C]
    (F : A ⥤ B) (G : B ⥤ C)
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] [(F ⋙ G).PreservesZeroMorphisms]
    (hF : ∀ S : ShortComplex A, S.ShortExact → (S.map F).ShortExact)
    (hG : ∀ S : ShortComplex B, S.ShortExact → (S.map G).ShortExact)
    (hFG : ∀ S : ShortComplex A, S.ShortExact → (S.map (F ⋙ G)).ShortExact) :
    K0.map (F ⋙ G) hFG = (K0.map G hG).comp (K0.map F hF) := by
  sorry

end BoringMath
