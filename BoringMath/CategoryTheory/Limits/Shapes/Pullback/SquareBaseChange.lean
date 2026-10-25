/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Square

/-!
# Base change of commutative squares

Given a commutative square `sq : Square C` in a category `C` and a morphism
`h : Y ⟶ sq.X₄` into its lower-right corner, this module constructs the
**base change** of `sq` along `h` on explicit pullback-cone data: the two
base-changed legs (cones over the cospans `(sq.f₂₄, h)` and `(sq.f₃₄, h)`)
and the corner cone over the induced cospan of legs.

This is the API substrate of the cd-structure program (the completeness
condition of Voevodsky — stability of distinguished squares under base
change — is its first consumer), and of the scheme-level Nisnevich layer.

The construction is **computable** (per the computability discipline of
`docs/STYLE.md`): the pullback data is an explicit parameter, not
instance-chosen — mathlib's `Limits.pullback` data is `Classical.choice`-
backed and would force `noncomputable`. Callers with a `HasPullbacks C`
instance obtain cone data at their own call sites; the library bakes no
choice into its definitions.

The base change of any commutative square, on limit corner data, is a
pullback square (the preservation clause is the special case that consumes
no hypothesis beyond the corner's limit witness).

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
`h : Y ⟶ sq.X₄` into its lower-right corner, on explicit pullback-cone
data: `c₂` and `c₃` are cones over the base-change cospans of the two
legs, and `c₁` is a cone over the induced cospan of the two new legs.
The square over `Y` assembles from the cone points and projections.

Computable by construction: the cone data is a parameter. -/
def baseChange (sq : Square C) {Y : C} (h : Y ⟶ sq.X₄)
    (c₂ : Limits.PullbackCone sq.f₂₄ h)
    (c₃ : Limits.PullbackCone sq.f₃₄ h)
    (c₁ : Limits.PullbackCone c₂.snd c₃.snd) : Square C where
  X₁ := c₁.pt
  X₂ := c₂.pt
  X₃ := c₃.pt
  X₄ := Y
  f₁₂ := c₁.fst
  f₁₃ := c₁.snd
  f₂₄ := c₂.snd
  f₃₄ := c₃.snd
  fac := c₁.condition

-- Reference: V. Voevodsky, *cd-structures*, unpublished notes (2010), §1
-- (the squares of a complete cd-structure are pullback squares; here the
-- statement consumes only the corner's limit witness).
-- REVIEW(citation): pin down the exact section in review.
/-- The base change of a commutative square, on limit corner data, is a
pullback square: the corner cone `c₁` being a limit says exactly that
the assembled square is a pullback square. The `IsPullback` preservation
clause for base changes of pullback squares is the special case with no
hypothesis to consume beyond the corner's limit witness. -/
theorem isPullback_baseChange (sq : Square C) {Y : C} (h : Y ⟶ sq.X₄)
    (c₂ : Limits.PullbackCone sq.f₂₄ h)
    (c₃ : Limits.PullbackCone sq.f₃₄ h)
    (c₁ : Limits.PullbackCone c₂.snd c₃.snd)
    (hc₁ : Limits.IsLimit c₁) : (sq.baseChange h c₂ c₃ c₁).IsPullback :=
  -- Direct term: `Square.IsPullback` unfolds to the four-arrow
  -- `IsPullback c₁.fst c₁.snd c₂.snd c₃.snd`, whose commutativity is
  -- `c₁.condition` and whose limit witness is `hc₁` transported along
  -- the cone isomorphism `PullbackCone.eta c₁`
  -- (`IsLimit.ofIsoLimit`, `Limits/IsLimit.lean:181`). Linear: each input
  -- is used exactly once.
  ⟨⟨c₁.condition⟩, ⟨Limits.IsLimit.ofIsoLimit hc₁ (Limits.PullbackCone.eta c₁)⟩⟩

end Square

end CategoryTheory
