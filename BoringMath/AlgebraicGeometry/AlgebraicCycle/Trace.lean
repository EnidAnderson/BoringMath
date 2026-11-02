/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringMath.AlgebraicGeometry.AlgebraicCycle.Zero
import BoringMath.AlgebraicGeometry.AlgebraicCycle.Pushforward
import BoringMath.AlgebraicGeometry.ResidueField.Tower

/-!
# The trace formula for zero-cycles

The degree of a pushforward is the degree along the composite: for a
quasicompact morphism `g`, a morphism `h`, and a zero-cycle `D` with
finite containing sets, the degree of the pushforward `g_* D` along `h`
equals the degree of `D` along the composite `g ≫ h`. The pointwise
content is the tower law for residue degrees: on a fiber, the
multiplicity weighted by both residue degrees is the local degree along
the composite.

## References
* W. Fulton, *Intersection Theory*, ch. 1 (the pushforward of
  zero-cycles and the degree: the degree of a pushforward is the degree
  along the composite).
  REVIEW(citation): pin down the section.
* S. Lang, *Algebra*, revised 3rd ed., Springer, 2002 (the tower law
  for the degrees of field extensions).
  REVIEW(citation): pin down the section.
-/

universe u

namespace AlgebraicGeometry

open CategoryTheory

variable {X Y Z : Scheme.{u}}

namespace AlgebraicCycle

-- Reference: S. Lang, *Algebra* (the tower law: the degree of a tower of
-- field extensions is the product of the degrees).
-- REVIEW(citation): pin down the section.
/-- **The local degree along a composite**: on the fiber over `z`, the
multiplicity weighted by the residue degree over `g` and by the residue
degree of `z` over `h` is the local degree along the composite — the
tower law at the point. -/
theorem localDegree_comp (g : X ⟶ Y) (h : Y ⟶ Z) (D : AlgebraicCycle X ℤ)
    {z : ↥Y} {x : ↥X} (hx : x ∈ g.base ⁻¹' {z}) :
    (D x * (g.residueDegree x : ℤ)) * (h.residueDegree z : ℤ) =
      localDegree (g ≫ h) D x := by
  have gz : g.base x = z := Set.mem_singleton_iff.mp (Set.mem_preimage.mp hx)
  calc (D x * (g.residueDegree x : ℤ)) * (h.residueDegree z : ℤ)
      = (D x * (g.residueDegree x : ℤ)) *
          (h.residueDegree (g.base x) : ℤ) :=
        congrArg₂ HMul.hMul rfl
          (congrArg ((Nat.cast (R := ℤ)))
            (Eq.symm (congrArg (h.residueDegree) gz)))
    _ = D x * ((g.residueDegree x : ℤ) *
          (h.residueDegree (g.base x) : ℤ)) :=
        mul_assoc _ _ _
    _ = D x * ((h.residueDegree (g.base x) : ℤ) *
          (g.residueDegree x : ℤ)) :=
        congrArg₂ HMul.hMul rfl (mul_comm _ _)
    _ = D x * ((h.residueDegree (g.base x) * g.residueDegree x : ℕ)) :=
        congrArg₂ HMul.hMul rfl (Eq.symm (Nat.cast_mul _ _))
    _ = D x * ((g ≫ h).residueDegree x : ℤ) :=
        congrArg₂ HMul.hMul rfl
          (congrArg ((Nat.cast (R := ℤ)))
            (Scheme.Hom.residueDegree_comp g h x).symm)
    _ = localDegree (g ≫ h) D x := rfl

-- Reference: W. Fulton, *Intersection Theory*, ch. 1, §1.4 (the degree is
-- the sum of the local degrees over the containing set — definitional).
-- REVIEW(citation): pin down the section.
/-- **The degree is the sum of the local degrees** over the containing
finset (definitional unfolding, peeled as a named lemma in place of a
`change`). -/
theorem degree_eq_sum (g : X ⟶ Y) (D : AlgebraicCycle X ℤ) (s : Finset ↥X)
    (hs : D.support ⊆ ↑s) :
    degree g D s hs = ∑ x ∈ s, localDegree g D x := rfl

-- Reference: W. Fulton, *Intersection Theory*, ch. 1 (the local degree of
-- a pushforward at a point: the fiber sum of the weighted coefficients;
-- here in composite-local-degree form via the tower law).
-- REVIEW(citation): pin down the section.
/-- **The local degree of a pushforward**: the local degree of `g_* D` at
`z` along `h` is the fiber finsum of the local degrees along `g ≫ h`. -/
theorem localDegree_pushforward (g : X ⟶ Y) [QuasiCompact g] (h : Y ⟶ Z)
    (D : AlgebraicCycle X ℤ) (z : ↥Y) :
    localDegree h (pushforward g D) z =
      ∑ᶠ (x : ↥X) (_ : x ∈ g.base ⁻¹' {z}), localDegree (g ≫ h) D x :=
  Eq.trans (Eq.trans (congrArg₂ HMul.hMul (pushforward_apply g D z) rfl)
      (finsum_mem_mul _ _))
    (finsum_mem_congr rfl fun _ hx => localDegree_comp g h D hx)

-- Reference: [program] boring peel: the sum over `t` of the pointwise
-- identity is stated at a fixed type, so no `Finset.sum_congr` lambda is
-- elaborated inside the main `calc`.
/-- **Sum of the local degrees of a pushforward**: summing
`localDegree_pushforward` over the containing finset `t`. -/
theorem sum_localDegree_pushforward (g : X ⟶ Y) [QuasiCompact g] (h : Y ⟶ Z)
    (D : AlgebraicCycle X ℤ) (t : Finset ↥Y) :
    ∑ z ∈ t, localDegree h (pushforward g D) z =
      ∑ z ∈ t, ∑ᶠ (x : ↥X) (_ : x ∈ g.base ⁻¹' {z}), localDegree (g ≫ h) D x :=
  Finset.sum_congr rfl fun z _ => localDegree_pushforward g h D z

-- Reference: [program] boring peel of the fiber-sum re-indexing step of the
-- trace formula: stated once at a fixed type, so the finsum-to-filtered-sum
-- conversion happens in its own declaration instead of inside the main
-- proof (the inlined version needed a raised `maxHeartbeats`).
open scoped Classical in
/-- **Fiber finsum re-indexing**: the fiber finsum of the composite local
degrees over `z` equals the sum over the doubly filtered containing
finset. -/
theorem finsum_fiber_localDegree (g : X ⟶ Y) (h : Y ⟶ Z) (D : AlgebraicCycle X ℤ)
    (s : Finset ↥X) (t : Finset ↥Y) (hs : D.support ⊆ ↑s)
    (ht : g.base '' D.support ⊆ ↑t) (z : ↥Y) :
    ∑ᶠ (x : ↥X) (_ : x ∈ g.base ⁻¹' {z}), localDegree (g ≫ h) D x =
      ∑ x ∈ (s.filter (fun y => g.base y ∈ ↑t)).filter (fun y => g.base y = z),
        localDegree (g ≫ h) D x := by
  refine finsum_cond_eq_sum_of_cond_iff _ fun ha => Iff.intro ?_ ?_
  · intro hmem
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · exact hs (Function.mem_support.mpr (mul_ne_zero_iff.mp ha).1)
      · exact ht (Set.mem_image_of_mem g.base
          (Function.mem_support.mpr (mul_ne_zero_iff.mp ha).1))
    · exact Set.mem_singleton_iff.mp (Set.mem_preimage.mp hmem)
  · intro hmem
    exact Set.mem_preimage.mpr
      (Set.mem_singleton_iff.mpr (Finset.mem_filter.mp hmem).2)

-- Reference: [program] boring peel: the sum over `t` of the re-indexed
-- fiber sums, stated at a fixed type.
open scoped Classical in
/-- **Sum of the fiber finsums**: summing `finsum_fiber_localDegree` over
the containing finset `t`. -/
theorem sum_finsum_fiber_localDegree (g : X ⟶ Y) (h : Y ⟶ Z) (D : AlgebraicCycle X ℤ)
    (s : Finset ↥X) (t : Finset ↥Y) (hs : D.support ⊆ ↑s)
    (ht : g.base '' D.support ⊆ ↑t) :
    ∑ z ∈ t, ∑ᶠ (x : ↥X) (_ : x ∈ g.base ⁻¹' {z}), localDegree (g ≫ h) D x =
      ∑ z ∈ t, ∑ x ∈ (s.filter (fun y => g.base y ∈ ↑t)).filter
        (fun y => g.base y = z), localDegree (g ≫ h) D x :=
  Finset.sum_congr rfl fun z _ => finsum_fiber_localDegree g h D s t hs ht z

-- Reference: [program] boring peel of `Finset.sum_fiberwise_of_maps_to` at
-- the doubly filtered shape (the inlined application timed out `isDefEq`
-- inside the `calc`).
open scoped Classical in
/-- **Fiberwise summation over an image-containing finset**: the sum over
`t` of the fiber sums is the sum over the filtered finset. -/
theorem sum_fiberwise_filter (g : X ⟶ Y) (s : Finset ↥X) (t : Finset ↥Y)
    (f : ↥X → ℤ) :
    ∑ z ∈ t, ∑ x ∈ (s.filter (fun y => g.base y ∈ ↑t)).filter (fun y => g.base y = z),
        f x =
      ∑ x ∈ s.filter (fun y => g.base y ∈ ↑t), f x :=
  Finset.sum_fiberwise_of_maps_to (fun _ hx => (Finset.mem_filter.mp hx).2) f

-- Reference: [program] boring peel of the vanishing off the filter: the
-- composite local degree vanishes at points of `s` whose image lies off
-- `t` (such points lie off the support of `D`).
open scoped Classical in
/-- **The composite local degree vanishes off the filtered finset**: at a
point of `s` whose image under `g` lies outside `t`, the point lies outside
the support of `D`, so the local degree is zero. -/
theorem localDegree_eq_zero_of_not_mem_filter (g : X ⟶ Y) (h : Y ⟶ Z)
    (D : AlgebraicCycle X ℤ) (s : Finset ↥X) (t : Finset ↥Y)
    (hs : D.support ⊆ ↑s) (ht : g.base '' D.support ⊆ ↑t)
    {x : ↥X} (hx' : x ∉ s.filter (fun y => g.base y ∈ ↑t)) :
    localDegree (g ≫ h) D x = 0 := by
  have hxs : x ∉ D.support := fun hmem =>
    hx' (Finset.mem_filter.mpr
      ⟨hs hmem, ht (Set.mem_image_of_mem g.base hmem)⟩)
  exact Eq.trans
    (congrArg₂ HMul.hMul (Function.notMem_support.mp hxs) rfl)
    (zero_mul _)

-- Reference: [program] boring peel of `Finset.sum_subset` at the filtered
-- shape (terms off the filter vanish).
open scoped Classical in
/-- **Extending a sum past a filter**: the filtered sum of the composite
local degrees is the sum over `s`. -/
theorem sum_filter_localDegree (g : X ⟶ Y) (h : Y ⟶ Z) (D : AlgebraicCycle X ℤ)
    (s : Finset ↥X) (t : Finset ↥Y) (hs : D.support ⊆ ↑s)
    (ht : g.base '' D.support ⊆ ↑t) :
    ∑ x ∈ s.filter (fun y => g.base y ∈ ↑t), localDegree (g ≫ h) D x =
      ∑ x ∈ s, localDegree (g ≫ h) D x :=
  Finset.sum_subset (Finset.filter_subset _ _)
    (fun _ _ hx' => localDegree_eq_zero_of_not_mem_filter g h D s t hs ht hx')

-- Reference: W. Fulton, *Intersection Theory*, ch. 1 (the degree of the
-- pushforward of a zero-cycle along a morphism is the degree of the
-- cycle along the composite).
-- REVIEW(citation): pin down the section.
open scoped Classical in
/-- **The trace formula**: the degree of the pushforward of a zero-cycle
along `h` is the degree of the cycle along the composite `g ≫ h`,
summed over finite sets: `t` contains the image of the support of `D`,
and `s` contains the support of `D`. -/
theorem degree_pushforward (g : X ⟶ Y) [QuasiCompact g] (h : Y ⟶ Z)
    (D : AlgebraicCycle X ℤ)
    (s : Finset ↥X) (t : Finset ↥Y) (hs : D.support ⊆ ↑s)
    (ht : g.base '' D.support ⊆ ↑t) :
    degree h (pushforward g D) t
      (Set.Subset.trans (support_pushforward_subset_image g D) ht) =
      degree (g ≫ h) D s hs := by
  refine Eq.trans (degree_eq_sum h (pushforward g D) t _) ?_
  refine Eq.trans ?_ (degree_eq_sum (g ≫ h) D s hs).symm
  exact Eq.trans (sum_localDegree_pushforward g h D t)
    (Eq.trans (sum_finsum_fiber_localDegree g h D s t hs ht)
      (Eq.trans (sum_fiberwise_filter g s t (localDegree (g ≫ h) D))
        (sum_filter_localDegree g h D s t hs ht)))

end AlgebraicCycle

end AlgebraicGeometry
