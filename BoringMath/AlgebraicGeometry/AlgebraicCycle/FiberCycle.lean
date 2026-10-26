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

-- Reference: W. Fulton, *Intersection Theory*, ch. 1 (the flat
-- pullback of a point cycle vanishes off the fiber).
-- REVIEW(citation): pin down the section.
/-- The fiber cycle vanishes at points outside the fiber: a point
whose image differs from the given point has coefficient zero. -/
theorem fiberCycle_apply_of_ne [IsNoetherian (Scheme.Hom.fiber f P)]
    (x : ↥X) (hx : f.base x ≠ P) :
    fiberCycle f P x = 0 :=
  Function.notMem_support.mp fun hmem =>
    hx (Set.mem_singleton_iff.mp
      (support_fiberCycle_subset_preimage f P hmem))

-- Reference: W. Fulton, *Intersection Theory*, ch. 1 (the multiplicity of
-- the flat pullback of a point cycle: the residue degrees of the generic
-- points of the fiber over the point).
-- REVIEW(citation): pin down the section.
open scoped Classical in
/-- **The multiplicity of the fiber cycle**: the coefficient of the
fiber cycle at a point is the sum over the generic points of the fiber
over the point of the residue degrees. -/
theorem fiberCycle_multiplicity [IsNoetherian (Scheme.Hom.fiber f P)]
    (z : ↥X) :
    fiberCycle f P z =
      ∑ᶠ (ξ : ↥(Scheme.Hom.fiber f P))
        (_ : (f.fiberι P).base ξ = z),
        (if ξ ∈ genericPoints ↥(Scheme.Hom.fiber f P)
          then ((f.fiberι P).residueDegree ξ : ℤ) else 0) := by
  have hg : (genericPoints ↥(Scheme.Hom.fiber f P) : Set ↥(Scheme.Hom.fiber f P)).Finite :=
    genericPoints.finite (α := ↥(Scheme.Hom.fiber f P))
      (finite_irreducibleComponents_of_isNoetherian (X := Scheme.Hom.fiber f P))
  refine Eq.trans (pushforward_apply _ _ _) ?_
  refine finsum_mem_congr rfl fun ξ _ => ?_
  rcases Classical.em
      (ξ ∈ Scheme.genericPointsFinset (Scheme.Hom.fiber f P)) with hmem | hmem
  · calc Scheme.fundamentalCycle (Scheme.Hom.fiber f P) ξ *
          ((f.fiberι P).residueDegree ξ : ℤ)
        = (1 : ℤ) * ((f.fiberι P).residueDegree ξ : ℤ) := by
          refine congrArg₂ HMul.hMul ?_ rfl
          refine Eq.trans (Scheme.fundamentalCycle_apply (Scheme.Hom.fiber f P) ξ)
            (ite_eq_left hmem)
      _ = ((f.fiberι P).residueDegree ξ : ℤ) := one_mul _
      _ = (if ξ ∈ genericPoints ↥(Scheme.Hom.fiber f P)
            then ((f.fiberι P).residueDegree ξ : ℤ) else 0) :=
          Eq.symm (ite_eq_left ((Set.Finite.mem_toFinset hg).mp hmem))
  · calc Scheme.fundamentalCycle (Scheme.Hom.fiber f P) ξ *
          ((f.fiberι P).residueDegree ξ : ℤ)
        = (0 : ℤ) * ((f.fiberι P).residueDegree ξ : ℤ) := by
          refine congrArg₂ HMul.hMul ?_ rfl
          refine Eq.trans (Scheme.fundamentalCycle_apply (Scheme.Hom.fiber f P) ξ)
            (ite_eq_right hmem)
      _ = (0 : ℤ) := zero_mul _
      _ = (if ξ ∈ genericPoints ↥(Scheme.Hom.fiber f P)
            then ((f.fiberι P).residueDegree ξ : ℤ) else 0) :=
          Eq.symm (ite_eq_right
            (show ¬(ξ ∈ genericPoints ↥(Scheme.Hom.fiber f P)) from fun hmem' => by
              have hfin : ξ ∈ Scheme.genericPointsFinset (Scheme.Hom.fiber f P) :=
                (Set.Finite.mem_toFinset hg).mpr hmem'
              exact hmem hfin))

end AlgebraicCycle

end AlgebraicGeometry
