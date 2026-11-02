/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.GroupTheory.IsPerfect
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer

/-!
# Quasisimple groups — foundation of the CFSG local-analysis library

Ticket CFSG.LIB (#236). A group is **quasisimple** if it is perfect and its
quotient by the center is simple; the CFSG reduces to the study of quasisimple
subgroups (the layers of a finite group). mathlib at the pin has `Group.IsPerfect`
and the focal subgroup theorem but no quasisimple layer.

## References
* [GLS] Number 1, ch. 1 (quasisimple groups, layers); [Aschbacher 2011] vol. 1.
* mathlib pin v4.35.0-rc3: `Group.IsPerfect` (GroupTheory/IsPerfect.lean),
  `Subgroup.map_commutator`, `Subgroup.map_top_of_surjective`,
  `commutator_alternatingGroup_eq_top` (Alternating/Centralizer.lean).
-/

namespace BoringMath

open Subgroup

variable {G H : Type*} [Group G] [Group H]

-- Reference: [GLS] Number 1, ch. 1 (definition); mathlib pin `Group.IsPerfect`.
/-- A group is **quasisimple** if it is perfect and `G / Z(G)` is simple. -/
class IsQuasisimpleGroup (G : Type*) [Group G] : Prop extends Group.IsPerfect G where
  /-- The quotient by the center is simple. -/
  quotient_center_simple : IsSimpleGroup (G ⧸ Subgroup.center G)

-- Reference: mathlib pin v4.35.0-rc3, `Subgroup.map_commutator`,
-- `Subgroup.map_top_of_surjective`; [GLS] Number 1 (perfectness is preserved
-- under surjections).
/-- **Perfectness is preserved under surjective homomorphisms** (proved). -/
theorem Group.IsPerfect.of_surjective [Group.IsPerfect G] (f : G →* H)
    (hf : Function.Surjective f) : Group.IsPerfect H := by
  have e1 := commutator_def H
  have e2 := Subgroup.map_commutator (f := f) (H₁ := ⊤) (H₂ := ⊤)
  have e3 : ⁅Subgroup.map f ⊤, Subgroup.map f ⊤⁆ = ⁅(⊤ : Subgroup H), ⊤⁆ :=
    congrArg (fun K => ⁅K, K⁆) (Subgroup.map_top_of_surjective f hf)
  have e4 : Subgroup.map f (commutator G) = Subgroup.map f ⊤ :=
    congrArg (Subgroup.map f) Group.IsPerfect.commutator_eq_top
  exact ⟨e1.trans (e3.symm.trans (e2.symm.trans (e4.trans (Subgroup.map_top_of_surjective f hf))))⟩

-- Reference: mathlib pin v4.35.0-rc3, `commutator_alternatingGroup_eq_top`
-- (Alternating/Centralizer.lean); [GLS] Number 1 (A_n is perfect for n ≥ 5).
/-- **The alternating group is perfect for `n ≥ 5`** (consumed at the pin). -/
theorem alternatingGroup_isPerfect {α : Type*} [DecidableEq α] [Fintype α]
    (h5 : 5 ≤ Nat.card α) : Group.IsPerfect (alternatingGroup α) :=
  ⟨commutator_alternatingGroup_eq_top h5⟩

-- Reference: mathlib pin v4.35.0-rc3, `Group.IsPerfect.center_quotient_center_eq_bot`;
-- [GLS] Number 1 (a perfect group has trivial center modulo its center).
/-- **A perfect group has trivial center modulo its center** (consumed). -/
theorem Group.IsPerfect.center_quotient_center_eq_bot' [Group.IsPerfect G] :
    Subgroup.center (G ⧸ Subgroup.center G) = ⊥ :=
  Group.IsPerfect.center_quotient_center_eq_bot (G := G)

end BoringMath
