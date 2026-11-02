/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Almost simple groups — the socle layer

Ticket CFSG.LIB.almostsimple (#244). A group `G` is **almost simple** if its
socle is a simple nonabelian group `N` (normal in `G`, with trivial
centralizer in `G`); then `N ≤ G ≤ Aut(N)`. The CFSG reduces to almost simple
groups via the layer theory.

## References
* [GLS] Number 3, Part I, Chapter A (almost simple `𝒦`-groups).
* mathlib pin v4.35.0-rc3: `IsSimpleGroup`, `Subgroup.centralizer`.
-/

namespace BoringMath

open Subgroup

variable {G : Type*} [Group G]

-- Reference: [GLS] Number 3, Part I, Chapter A (definition: socle simple
-- nonabelian with trivial centralizer).
/-- A group is **almost simple** if it has a normal simple nonabelian subgroup
`N` (the socle) whose centralizer in `G` is trivial. -/
class IsAlmostSimpleGroup (G : Type*) [Group G] : Prop where
  /-- There is a normal simple nonabelian `N` with trivial centralizer. -/
  exists_socle : ∃ N : Subgroup G, N.Normal ∧ IsSimpleGroup ↥N ∧
    (∃ a b : ↥N, a * b ≠ b * a) ∧ centralizer (N : Set G) = ⊥

-- Reference: immediate from `IsSimpleGroup.toNontrivial`; [GLS] Number 3
-- (an almost simple group is nontrivial).
/-- **An almost simple group is nontrivial** (proved). -/
theorem IsAlmostSimpleGroup.nontrivial {G : Type*} [Group G] [IsAlmostSimpleGroup G] :
    Nontrivial G := by
  obtain ⟨N, _, hsimple, _, _⟩ := IsAlmostSimpleGroup.exists_socle (G := G)
  obtain ⟨x, y, hxy⟩ := exists_pair_ne (α := ↥N)
  exact ⟨x.1, y.1, fun h => hxy (Subtype.ext h)⟩

end BoringMath
