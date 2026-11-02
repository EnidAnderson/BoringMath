/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import BoringMath.GroupTheory.CFSG.BNPair
import BoringMath.LieTheory.RootData

/-!
# Lie groups and finite groups of Lie type — ticket #550 (CFSG #251–#253)

The bridge from differential Lie theory (pin: `Geometry/Manifold/Algebra/
LieGroup`) to the CFSG Lie-type sector: a finite group of Lie type carries a
BN-pair. Feeds `AlgebraicGroups/` (#321–#326, the scheme-side Chevalley
construction) and `RepresentationTheory/LieWeights.lean` (#345).

## References
* [Helgason] S. Helgason, *Differential Geometry, Lie Groups, and Symmetric
  Spaces*, Academic Press 1978, ch. II.
* [Carter], ch. 10; [Wilson] *The Finite Simple Groups*, GTM 251, ch. 3.
* mathlib pin v4.35.0-rc3: `LieGroup`, `LieAlgebra`; BoringMath pin:
  `BNPairs` (`GroupTheory/CFSG/BNPair.lean`).
-/

namespace BoringMath

-- Reference: [Carter], ch. 10 (the finite groups of Lie type are the
-- Chevalley/Steinberg groups attached to a root datum).
/-- A **finite group of Lie type**: a finite group equipped with a root datum
whose Chevalley construction recovers it. -/
class IsFiniteGroupOfLieType (G : Type*) [Group G] [Fintype G] where
  rootDatum : RootDatum

-- Reference: [Wilson], ch. 3, Theorem 3.5.1 (Chevalley groups have BN-pairs:
-- `B = U T`, `N = N_G(T)`, `S` the simple reflections of the Weyl group).
-- TEMPORARY SORRY with peeling plan.
-- PEELING PLAN (#550, #251): (i) from the root datum build the Chevalley
-- group `H` (#549, `RootData.chevalley_group_finite`); (ii) the Bruhat
-- decomposition `H = ⊔_{w ∈ W} B w B` constructs `B`, `N`, `S` satisfying
-- the BN-pair axioms of `BNPairs`.
/-- **Finite groups of Lie type have BN-pairs**. -/
theorem bnPair_of_finite_lie_type (G : Type*) [Group G] [Fintype G]
    [IsFiniteGroupOfLieType G] : Nonempty (BNPairs G) := by
  sorry

end BoringMath
