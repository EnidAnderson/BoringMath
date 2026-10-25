/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
import BoringMath.AlgebraicGeometry.AlgebraicCycle.Zero

/-!
# Pushforward of zero-cycles

The pushforward of a zero-cycle along a quasicompact morphism: the
coefficient at a point is the sum over the fiber of the coefficients
weighted by the residue degrees. This module introduces the
pushforward, its value at a point, the support law (the pushforward is
supported on the image of the support), and the finiteness of the
pushforward of a finitely supported cycle.

## References
* W. Fulton, *Intersection Theory*, ch. 1 (the pushforward of
  zero-cycles: `f_* [x] = [κ(x) : κ(f x)] · [f x]`).
  REVIEW(citation): pin down the section.
* Stacks Project, *Chow Homology*, tag 02R3 (pushforward of cycles).
-/

universe u v

namespace AlgebraicGeometry

open CategoryTheory

variable {X Y : Scheme.{u}}

namespace AlgebraicCycle

-- Reference: W. Fulton, *Intersection Theory*, ch. 1 (the pushforward of
-- zero-cycles: the coefficient at a point is the fiber sum of the
-- coefficients weighted by the residue degrees).
-- REVIEW(citation): pin down the section.
/-- The **pushforward** of a zero-cycle along a quasicompact morphism
`g`: the coefficient at a point `z` is the sum over the fiber of `z` of
the coefficients weighted by the residue degrees of their points over
`g`.

The pushforward is a fiber-wise finite sum, which is nonconstructive in
general (the fibers are summed via a choice of enumeration). -/
noncomputable def pushforward (g : X ⟶ Y) [QuasiCompact g]
    (D : AlgebraicCycle X ℤ) : AlgebraicCycle Y ℤ :=
  AlgebraicCycle.map g (fun _ => (0 : ℕ)) (fun _ => (0 : ℕ)) D

-- Reference: W. Fulton, *Intersection Theory*, ch. 1 (the coefficient
-- of the pushforward at a point: the fiber sum of the weighted
-- coefficients).
-- REVIEW(citation): pin down the section.
/-- The coefficient of the pushforward at a point is the sum over the
fiber of the coefficients weighted by the residue degrees. -/
theorem pushforward_apply (g : X ⟶ Y) [QuasiCompact g]
    (D : AlgebraicCycle X ℤ) (z : ↥Y) :
    pushforward g D z = ∑ᶠ (x : ↥X) (_ : x ∈ g.base ⁻¹' {z}),
      D x * (g.residueDegree x : ℤ) := rfl

-- Reference: W. Fulton, *Intersection Theory*, ch. 1 (the pushforward
-- is supported on the image of the support).
-- REVIEW(citation): pin down the section.
/-- The support of the pushforward is contained in the image of the
support. -/
theorem support_pushforward_subset_image (g : X ⟶ Y) [QuasiCompact g]
    (D : AlgebraicCycle X ℤ) :
    (pushforward g D).support ⊆ g.base '' D.support := by
  refine Function.locallyFinsupp.support_map_subset_of_forall_mem g.isSpectralMap _ _
    D.support (g.base '' D.support) Set.Subset.rfl
    (fun _ hx _ => Set.mem_image_of_mem _ hx)

-- Reference: W. Fulton, *Intersection Theory*, ch. 1 (the pushforward
-- of a cycle with finite support has finite support).
-- REVIEW(citation): pin down the section.
/-- The pushforward of a cycle with finite support has finite support. -/
theorem IsFinite.pushforward (g : X ⟶ Y) [QuasiCompact g]
    {D : AlgebraicCycle X ℤ} (hD : IsFinite D) :
    IsFinite (pushforward g D) :=
  (hD.image g.base).subset (support_pushforward_subset_image g D)

end AlgebraicCycle

end AlgebraicGeometry
