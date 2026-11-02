/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.GroupTheory.PGroup

/-!
# Strongly closed subgroups — the characteristic-2 local analysis tool

Ticket CFSG.LIB.local (#241). A subgroup `P` is **strongly closed in `G` with
respect to `Q`** if conjugates of elements of `P` by elements of `Q` that land
in `P` already lie in the conjugacy class within `P`. This is the key notion of
Goldschmidt's and Bender's characteristic-2 analysis (and of Thompson's
replacement theorem).

## References
* [GLS] Number 2 (strongly closed subgroups); Goldschmidt, *A group-theoretic
  proof of the nonsolvability of the signalizer functor theorem* (1981).
-/

namespace BoringMath

variable {G : Type*} [Group G]

-- Reference: [GLS] Number 2, ch. 1 (definition of strongly closed: conjugates
-- under `Q` that stay in `P` are already `P`-conjugate).
/-- `P` is **strongly closed in `G` with respect to `Q`** if every `Q`-conjugate
of an element of `P` that lies in `P` is already a `P`-conjugate. -/
def StronglyClosed (P Q : Subgroup G) : Prop :=
  ∀ x : G, x ∈ P → ∀ g : G, g ∈ Q → g * x * g⁻¹ ∈ P →
    ∃ y : G, y ∈ P ∧ y * x * y⁻¹ = g * x * g⁻¹

-- Reference: immediate (take `y = g`); [GLS] Number 2.
/-- **Any subgroup is strongly closed in itself with respect to itself**
(proved: take `y = g`). -/
theorem stronglyClosed_self (P : Subgroup G) : StronglyClosed P P :=
  fun x _hx g hg _ => ⟨g, hg, rfl⟩

end BoringMath
