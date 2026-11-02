/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.GroupTheory.PGroup

/-!
# The `p`-core `O_p(G)` — the largest normal `p`-subgroup

Ticket CFSG.LIB.local (#241). `O_p(G)` is the join of all normal `p`-subgroups
of `G`; it is itself a normal `p`-subgroup and contains every normal
`p`-subgroup. Used throughout the local analysis (e.g. constrained groups).
mathlib at the pin has `normalCore` but no `p`-core.

## References
* [GLS] Number 2, ch. 1 (`O_p(G)`); Aschbacher, *Finite Group Theory*, ch. 8.
* mathlib pin v4.35.0-rc3: `IsPGroup`, `Subgroup.iSup_normal` (Pointwise.lean).
-/

namespace BoringMath

open Subgroup

variable (p : ℕ) (G : Type*) [Group G]

-- Reference: [GLS] Number 2, ch. 1 (definition of `O_p(G)`).
/-- The **`p`-core `O_p(G)`**: the join of all normal `p`-subgroups of `G`. -/
def oCore : Subgroup G :=
  ⨆ N : {N : Subgroup G // N.Normal ∧ IsPGroup p N}, N.1

-- Reference: mathlib pin v4.35.0-rc3, `Subgroup.iSup_normal`.
/-- Every normal subgroup in the family is normal (instance wrapper). -/
instance oCore_family_normal :
    ∀ N : {N : Subgroup G // N.Normal ∧ IsPGroup p N}, (N.1).Normal :=
  fun ⟨_, hN, _⟩ => hN

-- Reference: mathlib pin v4.35.0-rc3, `Subgroup.iSup_normal`; [GLS] Number 2.
/-- **`O_p(G)` is normal** (proved). -/
theorem oCore_normal : (oCore p G).Normal :=
  iSup_normal _

-- Reference: immediate from the definition (`le_iSup`); [GLS] Number 2
-- (`O_p(G)` contains every normal `p`-subgroup).
/-- **Every normal `p`-subgroup lies in `O_p(G)`** (proved). -/
theorem le_oCore {N : Subgroup G} (hN : N.Normal) (hP : IsPGroup p N) :
    N ≤ oCore p G :=
  le_iSup (fun M : {N : Subgroup G // N.Normal ∧ IsPGroup p N} => M.1) ⟨N, hN, hP⟩

-- Reference: [GLS] Number 2 (`O_p(G)` is a `p`-group). TEMPORARY SORRY with
-- peeling plan.
/-- **`O_p(G)` is a `p`-group**. TEMPORARY SORRY with peeling plan. -/
theorem oCore_isPGroup : IsPGroup p (oCore p G) := by
  -- TEMPORARY SORRY: the honest proof has not been instantiated yet.
  -- PEELING PLAN: the family of normal `p`-subgroups is directed (the sup of
  -- two normal `p`-subgroups is a normal `p`-subgroup — extension of `p`-groups
  -- by `p`-groups, using `IsPGroup` quotient/surjection lemmas at the pin);
  -- then `Subgroup.mem_iSup_of_directed` puts every element of `O_p(G)` in a
  -- member, and `isPGroup_iff_orderOf` closes it.
  sorry

end BoringMath
