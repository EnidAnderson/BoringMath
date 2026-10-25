/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
import BoringMath.AlgebraicGeometry.AlgebraicCycle.Zero
import BoringMath.AlgebraicGeometry.ResidueField.Tower

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

-- Reference: Stacks Project, tag 02R3 (the pushforward is a homomorphism
-- of the groups of cycles).
-- REVIEW(citation): pin down the exact tag.
/-- The **pushforward homomorphism**: the pushforward along a
quasicompact morphism is a homomorphism of the additive monoids of
zero-cycles. The pushforward is noncomputable (the fiber sums are
enumerated by choice). -/
noncomputable def pushforwardHom (g : X ⟶ Y) [QuasiCompact g] :
    AlgebraicCycle X ℤ →+ AlgebraicCycle Y ℤ where
  toFun := pushforward g
  map_zero' := pushforward_zero g
  map_add' := pushforward_add g

-- Reference: Stacks Project, tag 02R3.
-- REVIEW(citation): pin down the exact tag.
/-- The pushforward homomorphism is the pushforward. -/
theorem pushforwardHom_apply (g : X ⟶ Y) [QuasiCompact g]
    (D : AlgebraicCycle X ℤ) :
    pushforwardHom g D = pushforward g D := rfl

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

-- Reference: W. Fulton, *Intersection Theory*, ch. 1 (the pushforward is
-- functorial: the pushforward along a composite is the composite of the
-- pushforwards).
-- REVIEW(citation): pin down the section.
open scoped Classical in
/-- **The composition law for the pushforward**: the pushforward along a
composite is the pushforward of the pushforward. -/
theorem pushforward_comp {Z : Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ Z)
    [QuasiCompact g] [QuasiCompact h] (D : AlgebraicCycle X ℤ) :
    pushforward (g ≫ h) D = pushforward h (pushforward g D) := by
  refine Function.locallyFinsuppWithin.ext (fun w => ?_)
  have hS : ((g ≫ h).base ⁻¹' {w} ∩ D.support).Finite :=
    finite_support_inter_fiber (g ≫ h) D w
  have hV : (h.base ⁻¹' {w} ∩ (pushforward g D).support).Finite :=
    finite_support_inter_fiber h (pushforward g D) w
  have hTy : ∀ y, (g.base ⁻¹' {y} ∩ D.support).Finite := fun y =>
    finite_support_inter_fiber g D y
  -- each coefficient of the pushforward is a finite sum over the fiber
  have coeff_red : ∀ y, (pushforward g D) y =
      ∑ x ∈ (hTy y).toFinset, D x * (g.residueDegree x : ℤ) := fun y =>
    finsum_cond_eq_sum_of_cond_iff _ fun ha => Iff.intro
      (fun hmem =>
        (Set.Finite.mem_toFinset (hTy y)).mpr
          ⟨Set.mem_preimage.mpr
            (Eq.trans (Set.mem_singleton_iff.mp (Set.mem_preimage.mp hmem))
              rfl),
          Function.mem_support.mpr
            (mul_ne_zero_iff.mp ha).1⟩)
      (fun hmem => ((Set.Finite.mem_toFinset (hTy y)).mp hmem).1)
  -- multiplying a coefficient by a weight is a finite weighted fiber sum
  have fiber_red : ∀ y, (pushforward g D) y * (h.residueDegree y : ℤ) =
      ∑ x ∈ (hTy y).toFinset,
        (D x * (g.residueDegree x : ℤ)) * (h.residueDegree y : ℤ) := fun y =>
    Eq.trans (congrArg₂ HMul.hMul (coeff_red y) rfl) (Finset.sum_mul _ _ _)
  -- the left side: the composite fiber sum, weighted by the tower
  have tower : ∀ x, D x * ((g ≫ h).residueDegree x : ℤ) =
      (D x * (g.residueDegree x : ℤ)) *
        (h.residueDegree (g.base x) : ℤ) := fun x =>
    Eq.trans (congrArg₂ HMul.hMul rfl
      (Eq.trans (congrArg ((Nat.cast (R := ℤ)))
        (Scheme.Hom.residueDegree_comp g h x))
        (Nat.cast_mul _ _)))
      (Eq.trans (congrArg₂ HMul.hMul rfl (mul_comm _ _))
        (mul_assoc _ _ _).symm)
  have left_red : (pushforward (g ≫ h) D) w =
      ∑ x ∈ hS.toFinset, (D x * (g.residueDegree x : ℤ)) *
        (h.residueDegree (g.base x) : ℤ) := by
    refine Eq.trans (Eq.trans (pushforward_apply (g ≫ h) D w)
      (finsum_mem_congr rfl fun x _ => tower x)) ?_
    refine finsum_cond_eq_sum_of_cond_iff _ fun ha => Iff.intro
      (fun hmem =>
        (Set.Finite.mem_toFinset hS).mpr
          ⟨hmem, Function.mem_support.mpr
            (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp ha).1).1⟩)
      (fun hmem => ((Set.Finite.mem_toFinset hS).mp hmem).1)
  -- the right side: the outer fiber sum, then the inner fiber sums
  have right_red : (pushforward h (pushforward g D)) w =
      ∑ y ∈ hV.toFinset, ∑ x ∈ (hTy y).toFinset,
        (D x * (g.residueDegree x : ℤ)) * (h.residueDegree y : ℤ) := by
    refine Eq.trans (Eq.trans (pushforward_apply h (pushforward g D) w)
      (finsum_cond_eq_sum_of_cond_iff _ fun ha => Iff.intro
        (fun hmem =>
          (Set.Finite.mem_toFinset hV).mpr
            ⟨hmem, Function.mem_support.mpr (mul_ne_zero_iff.mp ha).1⟩)
        (fun hmem => ((Set.Finite.mem_toFinset hV).mp hmem).1))) ?_
    exact Finset.sum_congr rfl fun y _ => fiber_red y
  -- the fibers of g over the image of the composite fiber carry the left sum
  have part : ∑ x ∈ hS.toFinset, (D x * (g.residueDegree x : ℤ)) *
        (h.residueDegree (g.base x) : ℤ) =
      ∑ y ∈ hV.toFinset, ∑ x ∈ (hTy y).toFinset,
        (D x * (g.residueDegree x : ℤ)) * (h.residueDegree y : ℤ) := by
    have maps_to : ∀ x ∈ hS.toFinset,
        g.base x ∈ hS.toFinset.image g.base :=
      fun _ hx => Finset.mem_image_of_mem _ hx
    have step1 : ∑ x ∈ hS.toFinset, (D x * (g.residueDegree x : ℤ)) *
          (h.residueDegree (g.base x) : ℤ) =
        ∑ y ∈ hS.toFinset.image g.base,
          ∑ x ∈ hS.toFinset.filter (fun a => g.base a = y),
            (D x * (g.residueDegree x : ℤ)) *
              (h.residueDegree (g.base x) : ℤ) :=
      Eq.symm (Finset.sum_fiberwise_of_maps_to maps_to _)
    -- an image point lies over w
    have himg : ∀ y, y ∈ hS.toFinset.image g.base → h.base y = w := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      exact Eq.trans (congrArg h.base rfl)
        (Set.mem_singleton_iff.mp
          (Set.mem_preimage.mp ((Set.Finite.mem_toFinset hS).mp hx).1))
    -- on a fiber of g, the residue degree of the image point is constant,
    -- and the fiber sum is the coefficient of the pushforward
    have step2 : ∀ y, y ∈ hS.toFinset.image g.base →
        ∑ x ∈ hS.toFinset.filter (fun a => g.base a = y),
            (D x * (g.residueDegree x : ℤ)) *
              (h.residueDegree (g.base x) : ℤ) =
          (pushforward g D) y * (h.residueDegree y : ℤ) := by
      intro y hy
      have fil_eq : hS.toFinset.filter (fun a => g.base a = y) =
          (hTy y).toFinset := by
        refine Finset.ext fun a => ?_
        refine Iff.trans (Finset.mem_filter) ?_
        refine Iff.trans ?_ (Set.Finite.mem_toFinset (hTy y)).symm
        refine Iff.intro (fun hmem => ?_) (fun hmem => ?_)
        · exact Set.mem_inter
            (Set.mem_preimage.mpr
              (Set.mem_singleton_iff.mpr hmem.2))
            ((Set.Finite.mem_toFinset hS).mp hmem.1).2
        · refine ⟨(Set.Finite.mem_toFinset hS).mpr
              (Set.mem_inter ?_ hmem.2), ?_⟩
          · exact Set.mem_preimage.mpr
              (Eq.trans (congrArg h.base
                (Set.mem_singleton_iff.mp (Set.mem_preimage.mp hmem.1)))
                (himg y hy))
          · exact Set.mem_preimage.mp hmem.1
      refine Eq.trans (Finset.sum_congr rfl fun x hx =>
        congrArg₂ HMul.hMul rfl
          (congrArg ((Nat.cast (R := ℤ)))
            (congrArg (h.residueDegree)
              (Finset.mem_filter.mp hx).2))) ?_
      refine Eq.trans (Eq.symm (Finset.sum_mul _ _ _)) ?_
      refine Eq.trans (congrArg₂ HMul.hMul
        (congrArg (Finset.sum · (fun x => D x * (g.residueDegree x : ℤ)))
          fil_eq) rfl) ?_
      exact congrArg₂ HMul.hMul (coeff_red y).symm rfl
    -- the support of the pushforward lies in the image, and the
    -- extension to the image vanishes off the support
    have Vsub : hV.toFinset ⊆ hS.toFinset.image g.base := by
      intro y hy
      have hyV := (Set.Finite.mem_toFinset hV).mp hy
      obtain ⟨x, hx, hxne⟩ := exists_ne_zero_of_finsum_mem_ne_zero
        (Function.mem_support.mp hyV.2)
      refine Finset.mem_image.mpr ⟨x, ?_, ?_⟩
      · refine (Set.Finite.mem_toFinset hS).mpr ⟨?_, ?_⟩
        · exact Set.mem_preimage.mpr
            (Eq.trans (congrArg h.base
              (Set.mem_singleton_iff.mp (Set.mem_preimage.mp hx)))
              (Set.mem_singleton_iff.mp (Set.mem_preimage.mp hyV.1)))
        · exact Function.mem_support.mpr (mul_ne_zero_iff.mp hxne).1
      · exact Set.mem_singleton_iff.mp (Set.mem_preimage.mp hx)
    have hext : ∑ y ∈ hS.toFinset.image g.base,
        (pushforward g D) y * (h.residueDegree y : ℤ) =
      ∑ y ∈ hV.toFinset, (pushforward g D) y * (h.residueDegree y : ℤ) :=
      Eq.symm (Finset.sum_subset Vsub
        (fun y hy hyV => Eq.trans (congrArg₂ HMul.hMul
          (Function.notMem_support.mp (fun hmem => hyV
            ((Set.Finite.mem_toFinset hV).mpr
              ⟨Set.mem_preimage.mpr (himg y hy), hmem⟩)))
          rfl)
          (zero_mul _)))
    exact Eq.trans step1
      (Eq.trans (Finset.sum_congr rfl fun y hy => step2 y hy)
        (Eq.trans hext (Finset.sum_congr rfl fun y _ => fiber_red y)))
  exact Eq.trans left_red (Eq.trans part right_red.symm)

-- Reference: W. Fulton, *Intersection Theory*, ch. 1 (the pushforward is
-- functorial).
-- REVIEW(citation): pin down the section.
/-- The pushforward homomorphism is functorial: the homomorphism of a
composite is the composite of the homomorphisms. -/
theorem pushforwardHom_comp {Z : Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ Z)
    [QuasiCompact g] [QuasiCompact h] :
    pushforwardHom (g ≫ h) = (pushforwardHom h).comp (pushforwardHom g) :=
  AddMonoidHom.ext fun D => pushforward_comp g h D

end AlgebraicCycle

end AlgebraicGeometry
