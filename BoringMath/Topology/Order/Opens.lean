/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Topology.Order
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.Inseparable

/-!
# Specialization in open subspaces

Specialization is local: a specialization between two points of an open
subspace is a specialization in the ambient space, and conversely. The
closure in the induced topology of the subtype is the ambient closure of
the image.

## References
* Stacks Project, tag 004X (points of a topological space and
  specialization).
  REVIEW(citation): pin down the exact tag.
-/

universe u

namespace TopologicalSpace

namespace Opens

-- Reference: Stacks Project, tag 004X (specialization is local).
-- REVIEW(citation): pin down the exact tag.
/-- **Specialization in an open subspace is specialization in the
ambient space**, and conversely. -/
theorem specializes_iff {X : Type u} [TopologicalSpace X] (U : Opens X)
    {x x' : ↥U} : x' ⤳ x ↔ (x' : X) ⤳ (x : X) := by
  refine Iff.intro ?_ ?_
  · intro h
    refine specializes_iff_mem_closure.mpr ?_
    refine Eq.subst (motive := fun S => (x : X) ∈ S)
      (congrArg closure Set.image_singleton) ?_
    exact closure_induced.mp (specializes_iff_mem_closure.mp h)
  · intro h
    exact specializes_iff_mem_closure.mpr
      (closure_induced.mpr
        (Eq.subst (motive := fun S => (x : X) ∈ S)
          (congrArg closure
            (Set.image_singleton (f := fun z : ↥U => (z : X)) (a := x'))).symm
          (specializes_iff_mem_closure.mp h)))

end Opens

end TopologicalSpace
