/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringMath.AlgebraicGeometry.AlgebraicCycle.FundamentalCycle
import Mathlib.AlgebraicGeometry.Fiber

/-!
# The fiber cycle

The fiber cycle of a morphism at a point: the fundamental cycle of the
scheme-theoretic fiber, pushed forward along the fiber embedding. For a
flat morphism this is the flat pullback of the point cycle, with
multiplicity one — the reduced case; the local lengths of the fiber
(Serre's intersection multiplicities) are the named extension for the
general flat pullback.

## References
* W. Fulton, *Intersection Theory*, ch. 1 (the flat pullback of a
  cycle: for a flat morphism, the pullback of a point is the fundamental
  cycle of the fiber).
  REVIEW(citation): pin down the section.
* Stacks Project, tag 02R4 (the flat pullback of cycles).
  REVIEW(citation): pin down the exact tag.
-/

universe u

namespace AlgebraicGeometry

open CategoryTheory

namespace AlgebraicCycle

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (P : ↥Y)

-- Reference: W. Fulton, *Intersection Theory*, ch. 1 (the flat
-- pullback of a point cycle: the fundamental cycle of the fiber).
-- REVIEW(citation): pin down the section.
-- The fiber's generic points are chosen and the fiber sums are
-- enumerated by choice; the cycle is noncomputable.
open scoped Classical in
/-- **The fiber cycle** of a morphism at a point: the fundamental cycle
of the scheme-theoretic fiber, pushed forward along the fiber
embedding. For a flat morphism this is the flat pullback of the point
cycle, with multiplicity one — the reduced case. -/
noncomputable def fiberCycle [IsNoetherian (Scheme.Hom.fiber f P)] :
    AlgebraicCycle X ℤ :=
  pushforward (Scheme.Hom.fiberι f P)
    (Scheme.fundamentalCycle (Scheme.Hom.fiber f P))

-- Reference: W. Fulton, *Intersection Theory*, ch. 1 (the support of
-- the fiber cycle lies on the generic points of the fiber).
-- REVIEW(citation): pin down the section.
/-- The support of the fiber cycle is contained in the image of the
generic points of the fiber. -/
theorem support_fiberCycle [IsNoetherian (Scheme.Hom.fiber f P)] :
    (fiberCycle f P).support ⊆
      (Scheme.Hom.fiberι f P).base ''
        (Scheme.fundamentalCycle (Scheme.Hom.fiber f P)).support :=
  support_pushforward_subset_image _ _

-- Reference: W. Fulton, *Intersection Theory*, ch. 1 (the fiber cycle
-- of a Noetherian fiber has finite support).
-- REVIEW(citation): pin down the section.
/-- The fiber cycle of a Noetherian fiber has finite support. -/
theorem isFinite_fiberCycle [IsNoetherian (Scheme.Hom.fiber f P)] :
    IsFinite (fiberCycle f P) :=
  IsFinite.pushforward (Scheme.Hom.fiberι f P)
    (Scheme.isFinite_fundamentalCycle (Scheme.Hom.fiber f P))

-- Reference: W. Fulton, *Intersection Theory*, ch. 1 (the flat
-- pullback of a point cycle is supported on the fiber).
-- REVIEW(citation): pin down the section.
/-- The fiber cycle is supported on the set-theoretic fiber: every
point of the support maps to the given point. -/
theorem support_fiberCycle_subset_preimage
    [IsNoetherian (Scheme.Hom.fiber f P)] :
    (fiberCycle f P).support ⊆ f.base ⁻¹' ({P} : Set ↥Y) := by
  intro x hx
  obtain ⟨η', _, rfl⟩ := (Set.mem_image (Scheme.Hom.fiberι f P).base
      (Scheme.fundamentalCycle (Scheme.Hom.fiber f P)).support x).mp
      (support_fiberCycle f P hx)
  refine Set.mem_preimage.mpr ?_
  refine Eq.trans
    (congrArg (fun φ => φ η') (Scheme.Hom.fiber_fac f P)) ?_
  refine Eq.trans
    (congrArg (Y.fromSpecResidueField P)
      (Scheme.Hom.fiberToSpecResidueField_apply f P η')) ?_
  exact Scheme.fromSpecResidueField_apply P
    (IsLocalRing.closedPoint (Y.residueField P))

end AlgebraicCycle

end AlgebraicGeometry
