/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Topology.Sober

/-!
# Specializations of generic points

The generic points of the irreducible components are minimal for
specialization: a point that specializes to a generic point is that generic
point. The closure of the generic point is an irreducible component, hence
maximal among the irreducible sets; the closure of the specializing point
is an irreducible set containing it, so the two closures agree, and a
T₀ space has at most one generic point of a set.

## References
* Stacks Project, tags 004W–004X (irreducible components and their
  generic points).
  REVIEW(citation): pin down the exact tag.
-/

universe u

-- Reference: Stacks Project, tags 004W–004X (the generic points of the
-- irreducible components are minimal for specialization).
-- REVIEW(citation): pin down the exact tag.
/-- **A specialization of a generic point is that generic point**: the
generic points of the irreducible components are minimal for
specialization. -/
theorem eq_of_specializes_of_mem_genericPoints {α : Type u}
    [TopologicalSpace α] [T0Space α] {η ρ : α}
    (hη : η ∈ genericPoints α) (h : ρ ⤳ η) : ρ = η := by
  have hηmem : closure ({η} : Set α) ∈ irreducibleComponents α :=
    Set.mem_ofPred_eq.mp hη
  have hsub : closure ({η} : Set α) ⊆ closure ({ρ} : Set α) :=
    closure_minimal
      (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp h))
      isClosed_closure
  have hirr : IsIrreducible (closure ({ρ} : Set α)) :=
    isIrreducible_singleton.closure
  obtain ⟨C', hC', hsub'⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible _ hirr
  have hCC' : closure ({η} : Set α) = C' :=
    Maximal.eq_of_subset hηmem hC'.1 (Set.Subset.trans hsub hsub')
  have heq : closure ({ρ} : Set α) = closure ({η} : Set α) :=
    Set.Subset.antisymm
      (Eq.subst (motive := fun S => closure ({ρ} : Set α) ⊆ S)
        hCC'.symm hsub') hsub
  exact IsGenericPoint.eq
    (Eq.subst (motive := fun S => IsGenericPoint ρ S) heq
      isGenericPoint_closure)
    isGenericPoint_closure
