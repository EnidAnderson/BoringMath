/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Local subgroups: normalizers `N_G(P)`

Ticket CFSG.LIB.local (#241). The **local subgroup** attached to a subgroup
`P` is its normalizer `N_G(P)`; local analysis studies `G` through these.
mathlib at the pin has `Subgroup.normalizer` and `Subgroup.le_normalizer_iff`.

## References
* [GLS] Number 2, ch. 1 (local subgroups `N_G(P)`).
-/

namespace BoringMath

open Subgroup

variable {G : Type*} [Group G]

-- Reference: [GLS] Number 2, ch. 1 (the local subgroup `N_G(P)`).
/-- The **local subgroup** attached to `P`: its normalizer `N_G(P)`. -/
def localSubgroup (P : Subgroup G) : Subgroup G := Subgroup.normalizer (P : Set G)

-- Reference: mathlib pin v4.35.0-rc3, `Subgroup.le_normalizer_iff`; [GLS] Number 2
-- (`P ≤ N_G(P)`).
/-- **`P` is contained in its own normalizer** (proved). -/
theorem le_localSubgroup (P : Subgroup G) : P ≤ localSubgroup P :=
  Subgroup.le_normalizer_iff.mpr fun h hh k hk =>
    P.mul_mem (P.mul_mem hh hk) (P.inv_mem hh)

end BoringMath
