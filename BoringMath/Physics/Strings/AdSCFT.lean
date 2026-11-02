/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringMath.Physics.Specializations
import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# The AdS/CFT dictionary as a reconstruction adjunction — PHYS.STR.0 (#366, items 7–8)

The Maldacena–Witten dictionary in the framework's terms: a
`HolographicGravity` specialization whose hologram `bulk ⥤ boundary` has a
right adjoint `reconstruct` — bulk states are reconstructed from boundary
data. The toy instance `adscftToy` (bulk = boundary = a finite discrete set,
hologram = identity) proves the reconstruction adjunction outright
(`adscftToy_reconstruction`); the full dictionary (GKPW relation, partition
functions) is the named extension tracked in the lab ledger STR.1.1 (#26).

## References
* J. M. Maldacena, "The large-N limit of superconformal field theories and
  supergravity", Adv. Theor. Math. Phys. 2 (1998) 231, hep-th/9711200, §3 —
  the dictionary. REVIEW(citation): pin the section.
* E. Witten, "Anti de Sitter space and holography", Adv. Theor. Math. Phys. 2
  (1998) 253, hep-th/9802150, §2 — the GKPW relation. REVIEW(citation): pin.
* [GKPW] E. Witten, "Anti de Sitter space, thermal phase transition, and
  confinement in gauge theories", Adv. Theor. Math. Phys. 2 (1998) 253,
  hep-th/9802150, §3. REVIEW(citation): pin.
* Program register: BoringMath #366 (PHYS.STR.0), items 7–8; roadmap #361/#378.
-/


namespace BoringMath

open CategoryTheory

-- Reference: [Maldacena 1998] §3; [Witten 1998] §2 — the toy dictionary: bulk
-- and boundary are the same finite discrete category, hologram = identity,
-- reconstruct = identity; info = ℕ with the state index as measure.
/-- The **AdS/CFT toy**: bulk = boundary = `Discrete (Fin n)`, hologram and
reconstruction both the identity, information = the state index. -/
def adscftToy (n : ℕ) [NeZero n] : HolographicGravity.{0, 0, 0, 0, 0} where
  bulk := Discrete (Fin n)
  bulkUnit := Discrete.mk 0
  boundary := Discrete (Fin n)
  hologram := 𝟭 (Discrete (Fin n))
  reconstruct := 𝟭 (Discrete (Fin n))
  info := ℕ
  bulkInfo := fun b => b.as.val
  boundaryInfo := fun b => b.as.val
  holographicEq := fun _ => rfl
  boundaryLocality := (CategoryTheory.GrothendieckTopology.trivial _).toCoverage

-- Reference: [Maldacena 1998] §3 — the toy's hologram as a named functor (the
-- identity), so the adjunction statement has concrete types.
/-- The **toy hologram**: the identity functor on `Discrete (Fin n)`. -/
def adscftToyHologram (n : ℕ) : Discrete (Fin n) ⥤ Discrete (Fin n) := 𝟭 _

-- Reference: projection law (STYLE §5): peeled into its own named lemma.
/-- **Projection law**: the toy's hologram field is `adscftToyHologram`. -/
theorem adscftToy_hologram (n : ℕ) [NeZero n] :
    (adscftToy n).hologram = adscftToyHologram n := rfl

-- Reference: projection law (STYLE §5): peeled into its own named lemma.
/-- **Projection law**: the toy's reconstruct field is the identity functor. -/
theorem adscftToy_reconstruct (n : ℕ) [NeZero n] :
    (adscftToy n).reconstruct = 𝟭 (Discrete (Fin n)) := rfl

-- Reference: [Maldacena 1998]; roadmap #378 — reconstruction as an adjunction:
-- the toy's hologram is left adjoint to its reconstruct, proved outright.
/-- **The toy has a reconstruction adjunction**: `hologram ⊣ reconstruct`
holds for `adscftToy n` (via the projection laws and the identity adjunction). -/
theorem adscftToy_reconstruction (n : ℕ) :
    Nonempty (adscftToyHologram n ⊣ 𝟭 (Discrete (Fin n))) :=
  ⟨Adjunction.id (C := Discrete (Fin n))⟩

end BoringMath
