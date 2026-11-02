/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Centralizers of subgroups — basic tools for local analysis

Ticket CFSG.LIB.local (#241). The centralizer `C_G(S)` of a subgroup; the key
monotonicity fact is that centralization is antitone in the subgroup.

## References
* [GLS] Number 2, ch. 1 (centralizers in local analysis).
* mathlib pin v4.35.0-rc3: `Subgroup.centralizer`, `Subgroup.centralizer_le_iff`.
-/

namespace BoringMath

open Subgroup

variable {G : Type*} [Group G]

-- Reference: mathlib pin v4.35.0-rc3, `Subgroup.centralizer_le_iff` (membership
-- characterization); [GLS] Number 2.
/-- **Centralization is antitone in the subgroup** (proved):
`Q ≤ R` implies `C_G(R) ≤ C_G(Q)`. -/
theorem centralizer_anti {Q R : Subgroup G} (h : Q ≤ R) :
    centralizer (R : Set G) ≤ centralizer (Q : Set G) := by
  intro x hx
  refine (Subgroup.mem_centralizer_iff).mpr fun y hy => ?_
  exact (Subgroup.mem_centralizer_iff).mp hx y (h hy)

end BoringMath
