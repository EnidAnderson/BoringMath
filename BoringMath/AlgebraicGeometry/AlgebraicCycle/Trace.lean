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

-- Reference: W. Fulton, *Intersection Theory*, ch. 1 (the degree of the
-- pushforward of a zero-cycle along a morphism is the degree of the
-- cycle along the composite).
-- REVIEW(citation): pin down the section.
set_option maxHeartbeats 1000000 in
-- The re-indexing of the fiber sums over the composite is a large
-- unification problem; the elaboration needs the raised limit.
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
  change ∑ z ∈ t, localDegree h (pushforward g D) z =
    ∑ x ∈ s, localDegree (g ≫ h) D x
  calc ∑ z ∈ t, localDegree h (pushforward g D) z
      = ∑ z ∈ t, ∑ᶠ (x : ↥X) (_ : x ∈ g.base ⁻¹' {z}),
          (D x * (g.residueDegree x : ℤ)) * (h.residueDegree z : ℤ) :=
        Finset.sum_congr rfl fun z _ =>
          Eq.trans (congrArg₂ HMul.hMul (pushforward_apply g D z) rfl)
            (finsum_mem_mul _ _)
    _ = ∑ z ∈ t, ∑ᶠ (x : ↥X) (_ : x ∈ g.base ⁻¹' {z}),
          localDegree (g ≫ h) D x :=
        Finset.sum_congr rfl fun z _ =>
          finsum_mem_congr rfl fun x hx => localDegree_comp g h D hx
    _ = ∑ z ∈ t, ∑ x ∈ (s.filter (fun y => g.base y ∈ ↑t)).filter
          (fun y => g.base y = z), localDegree (g ≫ h) D x :=
        Finset.sum_congr rfl fun z hz => by
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
    _ = ∑ x ∈ s.filter (fun y => g.base y ∈ ↑t),
          localDegree (g ≫ h) D x :=
        Finset.sum_fiberwise_of_maps_to
          (fun i hi => (Finset.mem_filter.mp hi).2
            : ∀ i ∈ s.filter (fun y => g.base y ∈ ↑t), g.base i ∈ t)
          (localDegree (g ≫ h) D)
    _ = ∑ x ∈ s, localDegree (g ≫ h) D x :=
        Finset.sum_subset (Finset.filter_subset _ _)
          (fun x _ hx' => by
            have hxs : x ∉ D.support := fun hmem =>
              hx' (Finset.mem_filter.mpr
                ⟨hs hmem, ht (Set.mem_image_of_mem g.base hmem)⟩)
            exact Eq.trans
              (congrArg₂ HMul.hMul (Function.notMem_support.mp hxs) rfl)
              (zero_mul _))

end AlgebraicCycle

end AlgebraicGeometry
