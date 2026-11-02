/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.GroupTheory.PGroup

/-!
# Conjugation morphisms and fusion — foundation of the fusion-system library

Ticket CFSG.LIB.fusion (#240). A homomorphism `φ : Q →* R` between subgroups of
`G` is **conjugation by an element of `G`** if it agrees with `x ↦ g * x * g⁻¹`.
The fusion system of `G` on a Sylow `p`-subgroup is built from these morphisms.

## References
* [GLS] Number 2 (fusion); Alperin's fusion theorem.
* mathlib pin v4.35.0-rc3: `Subgroup`, `MonoidHom`.
-/

namespace BoringMath

variable {G : Type*} [Group G]

-- Reference: [GLS] Number 2, ch. 1 (morphisms of the fusion system are
-- conjugation by elements of `G`).
/-- A hom `φ : Q →* R` between subgroups of `G` is **conjugation by an element
of `G`** if it agrees with `x ↦ g * x * g⁻¹` on `Q`. -/
def IsConjHom {Q R : Subgroup G} (φ : ↥Q →* ↥R) : Prop :=
  ∃ g : G, ∀ x : ↥Q, (φ x : G) = g * (x : G) * g⁻¹

-- Reference: immediate (conjugation is injective); [GLS] Number 2.
/-- **Conjugation morphisms are injective** (proved). -/
theorem IsConjHom.injective {Q R : Subgroup G} {φ : ↥Q →* ↥R} (h : IsConjHom φ) :
    Function.Injective φ := by
  obtain ⟨g, hg⟩ := h
  intro x y hxy
  apply Subtype.ext
  have h1 : g * (x : G) * g⁻¹ = g * (y : G) * g⁻¹ :=
    (hg x).symm.trans (congrArg Subtype.val hxy |>.trans (hg y))
  have h2 : g * ((x : G) * g⁻¹) = g * ((y : G) * g⁻¹) :=
    (mul_assoc g (x : G) g⁻¹).symm.trans (h1.trans (mul_assoc g (y : G) g⁻¹))
  exact mul_right_cancel (mul_left_cancel h2)

end BoringMath
