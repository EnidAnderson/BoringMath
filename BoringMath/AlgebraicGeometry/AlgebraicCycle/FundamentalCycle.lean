/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringMath.AlgebraicGeometry.AlgebraicCycle.Zero
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# The fundamental cycle

The fundamental cycle of a Noetherian scheme: the formal sum of its
irreducible components, each with multiplicity one — the cycle-theoretic
avatar of the scheme itself. The support is the set of generic points.

## References
* W. Fulton, *Intersection Theory*, ch. 1 (the cycle of a variety: the
  sum of its irreducible components, each with multiplicity one for a
  reduced scheme).
  REVIEW(citation): pin down the section.
* Stacks Project, tag 0BA8 (a Noetherian scheme has finitely many
  irreducible components).
-/

universe u

namespace AlgebraicGeometry

open CategoryTheory

namespace Scheme

-- Reference: Stacks Project, tag 0BA8 (a Noetherian scheme has finitely
-- many irreducible components).
-- REVIEW(citation): pin down the exact tag.
/-- The generic points of a Noetherian scheme, as a finite set. -/
noncomputable def genericPointsFinset (X : Scheme.{u}) [IsNoetherian X] :
    Finset ↥X :=
  (genericPoints.finite (α := ↥X)
    (finite_irreducibleComponents_of_isNoetherian (X := X))).toFinset

-- Reference: W. Fulton, *Intersection Theory*, ch. 1 (the cycle of a
-- variety is the sum of its irreducible components).
-- REVIEW(citation): pin down the section.
-- The generic points are chosen, and the point cycles are enumerated by
-- choice; the cycle is noncomputable.
open scoped Classical in
/-- The **fundamental cycle** of a Noetherian scheme: the formal sum of
its irreducible components, each with multiplicity one — the
cycle-theoretic avatar of the scheme itself. -/
noncomputable def fundamentalCycle (X : Scheme.{u}) [IsNoetherian X] :
    AlgebraicCycle X ℤ :=
  ∑ η ∈ genericPointsFinset X, Function.locallyFinsuppWithin.single η 1

-- Reference: W. Fulton, *Intersection Theory*, ch. 1 (the coefficients
-- of the fundamental cycle: one at each generic point).
-- REVIEW(citation): pin down the section.
open scoped Classical in
/-- The coefficient of the fundamental cycle is one at each generic
point and zero elsewhere. -/
theorem fundamentalCycle_apply (X : Scheme.{u}) [IsNoetherian X] (x : ↥X) :
    fundamentalCycle X x = if x ∈ genericPointsFinset X then (1 : ℤ) else 0 := by
  change (∑ η ∈ genericPointsFinset X,
      Function.locallyFinsuppWithin.single η (1 : ℤ)) x = _
  calc (∑ η ∈ genericPointsFinset X,
          Function.locallyFinsuppWithin.single η (1 : ℤ)) x
      = (∑ η ∈ genericPointsFinset X,
          (Function.locallyFinsuppWithin.single η (1 : ℤ) :
            ↥X → ℤ)) x :=
        congrFun Function.locallyFinsuppWithin.coe_sum x
    _ = ∑ η ∈ genericPointsFinset X,
          (Function.locallyFinsuppWithin.single η (1 : ℤ) :
            ↥X → ℤ) x :=
        Finset.sum_apply x _ _
    _ = ∑ η ∈ genericPointsFinset X,
          (if x = η then (1 : ℤ) else 0) :=
        Finset.sum_congr rfl fun _ _ =>
          Function.locallyFinsuppWithin.single_apply
    _ = if x ∈ genericPointsFinset X then (1 : ℤ) else 0 :=
        Finset.sum_ite_eq _ _ _

-- Reference: W. Fulton, *Intersection Theory*, ch. 1 (the support of
-- the fundamental cycle is the set of generic points).
-- REVIEW(citation): pin down the section.
open scoped Classical in
/-- The support of the fundamental cycle is the set of generic points. -/
theorem support_fundamentalCycle (X : Scheme.{u}) [IsNoetherian X] :
    (fundamentalCycle X).support = (genericPoints ↥X : Set ↥X) := by
  have hg : (genericPoints ↥X : Set ↥X).Finite :=
    genericPoints.finite (α := ↥X)
      (finite_irreducibleComponents_of_isNoetherian (X := X))
  refine Set.Subset.antisymm ?_ ?_
  · intro x hx
    have hne := Function.mem_support.mp hx
    rcases Classical.em (x ∈ genericPointsFinset X) with h | h
    · exact (Set.Finite.mem_toFinset hg).mp h
    · exact absurd
        (Eq.trans (fundamentalCycle_apply X x) (ite_eq_right h)) hne
  · intro x hx
    have hval : fundamentalCycle X x = (1 : ℤ) :=
      Eq.trans (fundamentalCycle_apply X x)
        (ite_eq_left ((Set.Finite.mem_toFinset hg).mpr hx))
    exact fun hzero =>
      one_ne_zero (Eq.trans hval.symm hzero)

-- Reference: W. Fulton, *Intersection Theory*, ch. 1 (the fundamental
-- cycle has finite support).
-- REVIEW(citation): pin down the section.
/-- The fundamental cycle has finite support. -/
theorem isFinite_fundamentalCycle (X : Scheme.{u}) [IsNoetherian X] :
    AlgebraicCycle.IsFinite (fundamentalCycle X) :=
  (genericPoints.finite (α := ↥X)
    (finite_irreducibleComponents_of_isNoetherian (X := X))).subset
    (Eq.subset (support_fundamentalCycle X))

end Scheme

end AlgebraicGeometry
