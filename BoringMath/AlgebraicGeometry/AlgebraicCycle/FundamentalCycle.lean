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

-- Reference: Stacks Project, tag 0BA8 (the generic points of the
-- irreducible components; homeomorphisms transport components).
-- REVIEW(citation): pin down the exact tag.
/-- The generic points transport along homeomorphisms of the underlying
spaces: the image of the closure of a generic point is the closure of
the image, and the image of an irreducible component is an irreducible
component. -/
theorem image_genericPoints_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIso f] :
    f.base '' (genericPoints ↥X) = (genericPoints ↥Y) := by
  have key : ∀ {A B : Scheme.{u}} (h : ↥A ≃ₜ ↥B) (η : ↥A),
      η ∈ genericPoints ↥A → h η ∈ genericPoints ↥B := by
    intro _A _B h η hη
    have hclo : closure ({h η} : Set ↥_B) =
        ⇑h '' closure ({η} : Set ↥_A) :=
      Eq.trans (congrArg closure (Set.image_singleton).symm)
        (Homeomorph.image_closure h _).symm
    have hpre : ⇑h '' closure ({η} : Set ↥_A) =
        ⇑h.symm ⁻¹' closure ({η} : Set ↥_A) := by
      refine Set.ext fun y => Iff.intro (fun hy => ?_) (fun hy => ?_)
      · obtain ⟨z, hz, rfl⟩ := hy
        exact Set.mem_preimage.mpr
          (Eq.subst (Homeomorph.symm_apply_apply h z).symm hz)
      · exact ⟨h.symm y, Set.mem_preimage.mp hy,
          Homeomorph.apply_symm_apply h y⟩
    have hcomp : ⇑h.symm ⁻¹' closure ({η} : Set ↥_A) ∈
        irreducibleComponents ↥_B :=
      preimage_mem_irreducibleComponents_of_isPreirreducible_fiber hη
        (Homeomorph.continuous h.symm) (Homeomorph.isOpenMap h.symm)
        (fun x => Set.Subsingleton.isPreirreducible
          fun y hy y' hy' => h.symm.injective
            (Eq.trans (Set.mem_singleton_iff.mp (Set.mem_preimage.mp hy))
              (Eq.symm (Set.mem_singleton_iff.mp
                (Set.mem_preimage.mp hy')))))
        ⟨η, subset_closure rfl,
          Set.mem_range.mpr ⟨h η, Homeomorph.symm_apply_apply h η⟩⟩
    change closure ({h η} : Set ↥_B) ∈ irreducibleComponents ↥_B
    exact Eq.subst (Eq.trans hclo hpre).symm hcomp
  refine Set.Subset.antisymm ?_ ?_
  · intro y hy
    obtain ⟨η, hη, rfl⟩ := hy
    exact key (Scheme.Hom.homeomorph f) η hη
  · intro y hy
    exact ⟨(Scheme.Hom.homeomorph f).symm y,
      key (Scheme.Hom.homeomorph f).symm y hy,
      Homeomorph.apply_symm_apply (Scheme.Hom.homeomorph f) y⟩

end Scheme

end AlgebraicGeometry
