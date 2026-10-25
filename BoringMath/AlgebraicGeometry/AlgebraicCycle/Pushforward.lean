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

-- Reference: Stacks Project, tag 02R3 (the pushforward of the zero cycle
-- is the zero cycle).
-- REVIEW(citation): pin down the exact tag.
/-- The pushforward of the zero cycle is the zero cycle. -/
theorem pushforward_zero (g : X ⟶ Y) [QuasiCompact g] :
    pushforward g (0 : AlgebraicCycle X ℤ) = 0 := by
  refine Function.locallyFinsuppWithin.ext (fun z => ?_)
  refine Eq.trans (pushforward_apply g (0 : AlgebraicCycle X ℤ) z) ?_
  exact finsum_mem_of_eqOn_zero (fun _ _ => zero_mul _)

-- Reference: Stacks Project, tag 02R3 (the pushforward along the
-- identity is the identity).
-- REVIEW(citation): pin down the exact tag.
/-- The pushforward along the identity is the identity on cycles. -/
theorem pushforward_id (D : AlgebraicCycle X ℤ) :
    pushforward (𝟙 X) D = D :=
  AlgebraicCycle.map_id (fun _ => (0 : ℕ)) D

-- Reference: Stacks Project, tag 02R3 (the fiber sums of the
-- pushforward are finite sums).
-- REVIEW(citation): pin down the exact tag.
/-- The support of a cycle meets a fiber of a quasicompact morphism in
a finite set. -/
theorem finite_support_inter_fiber (g : X ⟶ Y) [QuasiCompact g]
    (D : AlgebraicCycle X ℤ) (z : ↥Y) :
    (g.base ⁻¹' {z} ∩ D.support).Finite := by
  obtain ⟨U, hU⟩ :=
    (PrespectralSpace.isTopologicalBasis (X := ↥Y)).exists_subset_of_mem_open
      (Set.mem_univ z) isOpen_univ
  refine Set.Finite.subset
    (LocallyFiniteSupport.finite_inter_support_of_isCompact
      (Function.locallyFinsupp.locallyFiniteSupport D)
      (IsCompact.preimage_of_isOpen g.isSpectralMap hU.1.2 hU.1.1)) ?_
  intro x hx
  exact ⟨Set.mem_preimage.mpr
      (Eq.subst (Set.mem_singleton_iff.mp (Set.mem_preimage.mp hx.1)).symm hU.2.1),
    hx.2⟩

-- Reference: Stacks Project, tag 02R3 (the pushforward is additive).
-- REVIEW(citation): pin down the exact tag.
/-- The pushforward is additive: the pushforward of a sum of cycles is
the sum of the pushforwards. -/
theorem pushforward_add (g : X ⟶ Y) [QuasiCompact g]
    (D E : AlgebraicCycle X ℤ) :
    pushforward g (D + E) = pushforward g D + pushforward g E := by
  refine Function.locallyFinsuppWithin.ext (fun z => ?_)
  calc (pushforward g (D + E)) z
      = ∑ᶠ (x : ↥X) (_ : x ∈ g.base ⁻¹' {z}),
          (D + E) x * (g.residueDegree x : ℤ) :=
        pushforward_apply g (D + E) z
    _ = (pushforward g D + pushforward g E) z := by
      refine Eq.trans (finsum_mem_congr rfl fun x _ =>
        Eq.trans (congrArg₂ HMul.hMul (multiplicity_add D E x) rfl)
          (add_mul (D x) (E x) (g.residueDegree x))) ?_
      refine Eq.trans (finsum_mem_add_distrib'
        (Set.Finite.subset (finite_support_inter_fiber g D z) fun x hx =>
          ⟨hx.1, Function.mem_support.mpr
            (mul_ne_zero_iff.mp (Function.mem_support.mp hx.2)).1⟩)
        (Set.Finite.subset (finite_support_inter_fiber g E z) fun x hx =>
          ⟨hx.1, Function.mem_support.mpr
            (mul_ne_zero_iff.mp (Function.mem_support.mp hx.2)).1⟩)) ?_
      exact Eq.symm (congrArg₂ HAdd.hAdd (pushforward_apply g D z)
        (pushforward_apply g E z))

-- Reference: W. Fulton, *Intersection Theory*, ch. 1 (the pushforward of
-- a point cycle: `g_* (r · [x]) = (r · [κ(x) : κ(g x)]) · [g x]`).
-- REVIEW(citation): pin down the section.
/-- The pushforward of a point cycle is the point cycle at the image
point, with the coefficient weighted by the residue degree. -/
theorem pushforward_single (g : X ⟶ Y) [QuasiCompact g] [DecidableEq ↥X]
    [DecidableEq ↥Y] (x : ↥X) (r : ℤ) :
    pushforward g (Function.locallyFinsuppWithin.single x r) =
      Function.locallyFinsuppWithin.single (g.base x)
        (r * (g.residueDegree x : ℤ)) := by
  refine Function.locallyFinsuppWithin.ext (fun z => ?_)
  rcases Classical.em (z = g.base x) with hz | hz
  · subst hz
    have key : ∀ {a : ↥X},
        Function.locallyFinsuppWithin.single x r a *
            (g.residueDegree a : ℤ) ≠ 0 →
        a = x :=
      fun ha => eq_of_multiplicity_ne_zero x r (mul_ne_zero_iff.mp ha).1
    calc pushforward g (Function.locallyFinsuppWithin.single x r) (g.base x)
        = ∑ᶠ (a : ↥X) (_ : a ∈ g.base ⁻¹' {g.base x}),
            Function.locallyFinsuppWithin.single x r a *
              (g.residueDegree a : ℤ) :=
          pushforward_apply g _ _
      _ = ∑ a ∈ ({x} : Finset ↥X),
            Function.locallyFinsuppWithin.single x r a *
              (g.residueDegree a : ℤ) :=
          finsum_cond_eq_sum_of_cond_iff _
            (fun ha => Iff.intro
              (fun _ => Finset.mem_singleton.mpr (key ha))
              (fun hmem => Set.mem_preimage.mpr
                (Set.mem_singleton_iff.mpr
                  (congrArg g.base (Finset.mem_singleton.mp hmem)))))
      _ = Function.locallyFinsuppWithin.single x r x *
            (g.residueDegree x : ℤ) :=
          Finset.sum_singleton _ x
      _ = r * (g.residueDegree x : ℤ) :=
          congrArg₂ HMul.hMul (multiplicity_single x r) rfl
      _ = Function.locallyFinsuppWithin.single (g.base x)
            (r * (g.residueDegree x : ℤ)) (g.base x) :=
          (multiplicity_single (g.base x) (r * (g.residueDegree x : ℤ))).symm
  · have key : ∀ {a : ↥X},
        Function.locallyFinsuppWithin.single x r a *
            (g.residueDegree a : ℤ) ≠ 0 →
        a = x :=
      fun ha => eq_of_multiplicity_ne_zero x r (mul_ne_zero_iff.mp ha).1
    calc pushforward g (Function.locallyFinsuppWithin.single x r) z
        = ∑ᶠ (a : ↥X) (_ : a ∈ g.base ⁻¹' {z}),
            Function.locallyFinsuppWithin.single x r a *
              (g.residueDegree a : ℤ) :=
          pushforward_apply g _ _
      _ = ∑ a ∈ (∅ : Finset ↥X),
            Function.locallyFinsuppWithin.single x r a *
              (g.residueDegree a : ℤ) :=
          finsum_cond_eq_sum_of_cond_iff _
            (fun ha => Iff.intro
              (fun hmem => absurd
                (Eq.trans (congrArg g.base (key ha)).symm
                  (Set.mem_singleton_iff.mp (Set.mem_preimage.mp hmem)))
                (Ne.symm hz))
              (fun hmem => absurd hmem (Finset.notMem_empty _)))
      _ = 0 := Finset.sum_empty
      _ = Function.locallyFinsuppWithin.single (g.base x)
            (r * (g.residueDegree x : ℤ)) z :=
          Eq.symm (Eq.trans Function.locallyFinsuppWithin.single_apply
            (ite_eq_right hz))

end AlgebraicCycle

end AlgebraicGeometry
