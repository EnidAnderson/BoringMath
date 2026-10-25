/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Square

/-!
# Base change of commutative squares

Given a commutative square `sq : Square C` in a category `C` with pullbacks
and a morphism `h : Y ⟶ sq.X₄` into its lower-right corner, this module
constructs the **base change** `sq.baseChange h : Square C`: the commutative
square over `Y` whose two legs are the base changes of `sq.f₂₄` and
`sq.f₃₄` along `h`, and whose corner is the fiber product of the two new
legs.

This is the API substrate of the cd-structure program (the completeness
condition of Voevodsky — stability of distinguished squares under base
change — is its first consumer), and of the scheme-level Nisnevich layer.
The base change of any commutative square is a pullback square, by
construction; and base change composes, up to the canonical isomorphism of
squares (statement-only here, per the sorry law).

## References
* V. Voevodsky, *cd-structures*, unpublished notes (2010) — the
  motivating consumer.
-/

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace Square

-- Reference: V. Voevodsky, *cd-structures*, unpublished notes (2010), §1
-- (distinguished squares and their base changes; the completeness
-- condition is the first consumer). REVIEW(citation): pin down the exact
-- section in review.
/-- The **base change** of a commutative square `sq` along a morphism
`h : Y ⟶ sq.X₄` into its lower-right corner: the square over `Y` whose
legs are the base changes of `sq.f₂₄` and `sq.f₃₄` along `h` and whose
corner is the fiber product of the two new legs.

The name `baseChange` (rather than `pullback`) avoids shadowing
`Limits.pullback` within the `Square` namespace and matches the
terminology of the scheme-level consumers. -/
noncomputable def baseChange [Limits.HasPullbacks C] (sq : Square C) {Y : C} (h : Y ⟶ sq.X₄) :
    Square C where
  X₁ := Limits.pullback (Limits.pullback.snd (f := sq.f₂₄) (g := h))
    (Limits.pullback.snd (f := sq.f₃₄) (g := h))
  X₂ := Limits.pullback sq.f₂₄ h
  X₃ := Limits.pullback sq.f₃₄ h
  X₄ := Y
  f₁₂ := Limits.pullback.fst
    (f := Limits.pullback.snd (f := sq.f₂₄) (g := h))
    (g := Limits.pullback.snd (f := sq.f₃₄) (g := h))
  f₁₃ := Limits.pullback.snd
    (f := Limits.pullback.snd (f := sq.f₂₄) (g := h))
    (g := Limits.pullback.snd (f := sq.f₃₄) (g := h))
  f₂₄ := Limits.pullback.snd (f := sq.f₂₄) (g := h)
  f₃₄ := Limits.pullback.snd (f := sq.f₃₄) (g := h)
  fac := Limits.pullback.condition
    (f := Limits.pullback.snd (f := sq.f₂₄) (g := h))
    (g := Limits.pullback.snd (f := sq.f₃₄) (g := h))

-- Reference: V. Voevodsky, *cd-structures*, unpublished notes (2010), §1
-- (the squares of a complete cd-structure are pullback squares; here the
-- statement is unconditional: the corner IS the chosen fiber product).
-- REVIEW(citation): pin down the exact section in review.
/-- The base change of a commutative square is a pullback square —
unconditionally: the corner of `sq.baseChange h` is the chosen fiber
product of its two legs by construction, so the attached pullback cone is
the chosen limit cone. The `IsPullback` preservation clause for base
changes of pullback squares is the special case with no hypothesis to
consume. -/
theorem isPullback_baseChange [Limits.HasPullbacks C] (sq : Square C) {Y : C}
    (h : Y ⟶ sq.X₄) : (sq.baseChange h).IsPullback :=
  -- Direct term: `Square.IsPullback` unfolds to the four-arrow
  -- `IsPullback Limits.pullback.fst Limits.pullback.snd _ _`, which is
  -- `Limits.pullbackIsPullback` (`Limits/Shapes/Pullback/HasPullback.lean:228`)
  -- for the two base-changed legs. Linear: each input is used exactly
  -- once.
  Square.IsPullback.mk (sq := sq.baseChange h) (Limits.pullbackIsPullback _ _)

-- Reference: V. Voevodsky, *cd-structures*, unpublished notes (2010), §1
-- (stability of the cd-structure under base change). The associativity
-- input is `pullbackAssoc` (`Limits/Shapes/Pullback/Assoc.lean:143`).
-- REVIEW(citation): pin down the exact section in review.
/-- Base change along a composite is base change along the second
morphism, then base change along the first, up to the canonical
isomorphism of squares. -/
def baseChangeCompIso [Limits.HasPullbacks C] (sq : Square C) {Y Z : C}
    (h₁ : Y ⟶ Z) (h₂ : Z ⟶ sq.X₄) :
    sq.baseChange (h₁ ≫ h₂) ≅ (sq.baseChange h₂).baseChange h₁ := by
  -- TEMPORARY SORRY: the honest construction has not been instantiated yet.
  -- PEELING PLAN: the two leg objects are canonically isomorphic by the
  -- pasting law for pullbacks
  -- (`pullbackPullbackRightIsPullback`-style,
  -- `Limits/Shapes/Pullback/Assoc.lean:127`), and the corner objects by
  -- `pullbackAssoc` (`Assoc.lean:143`); assemble the component isos into
  -- an isomorphism of squares via the morphism structure of `Square C`
  -- (verify the exact Square Hom/iso API at the pin: `Square.Hom` and its
  -- commutativity fields), using named lemmas only.
  sorry

end Square

end CategoryTheory
