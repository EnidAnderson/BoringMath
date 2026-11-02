/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringMath.GroupTheory.CFSG.Fusion

/-!
# The fusion system of a group on a subgroup

Ticket CFSG.LIB.fusion (#240). The **fusion system** `F(G, P)` of a group `G`
on a subgroup `P` has as objects the subgroups of `P` and as morphisms `Q → R`
the homomorphisms induced by conjugation by elements of `G`
(`IsConjHom`, from `Fusion.lean`). Saturation and Alperin's fusion theorem are
the deep content built on this.

## References
* [GLS] Number 2, ch. 1 (fusion systems); Alperin, *Fusion systems in algebra
  and topology*; Aschbacher–Kessar–Oliver, *Fusion Systems in Group Theory*.
-/

namespace BoringMath

variable {G : Type*} [Group G]

-- Reference: [GLS] Number 2, ch. 1 (morphisms of the fusion system are
-- conjugation by elements of `G`).
/-- The morphisms of the fusion system of `G` on `P` from `Q` to `R`
(`Q, R ≤ P`): the `IsConjHom`s. -/
def fusionHom (_P Q R : Subgroup G) : Set (↥Q →* ↥R) :=
  {φ | IsConjHom φ}

-- Reference: immediate (conjugation by `1`); [GLS] Number 2 (identities are in
-- the fusion system).
/-- **The identity is a fusion morphism** (proved: conjugation by `1`). -/
theorem fusionHom_id_mem (P Q : Subgroup G) :
    MonoidHom.id ↥Q ∈ fusionHom P Q Q := by
  refine ⟨1, fun x => ?_⟩
  exact (((congrArg (fun t => t * (1 : G)⁻¹) (one_mul (x : G))).trans
      ((congrArg (fun t => (x : G) * t) inv_one).trans (mul_one (x : G))))).symm

-- Reference: [GLS] Number 2 (composition of fusion morphisms is a fusion
-- morphism); conjugation by `h * g`.
/-- **Fusion morphisms are closed under composition** (proved). -/
theorem fusionHom_comp_mem {P Q R S : Subgroup G} {φ : ↥Q →* ↥R} {ψ : ↥R →* ↥S}
    (hφ : φ ∈ fusionHom P Q R) (hψ : ψ ∈ fusionHom P R S) :
    ψ.comp φ ∈ fusionHom P Q S := by
  obtain ⟨g, hg⟩ := hφ
  obtain ⟨h, hh⟩ := hψ
  refine ⟨h * g, fun x => ?_⟩
  have e1 : ((ψ.comp φ) x : G) = h * (g * (x : G) * g⁻¹) * h⁻¹ :=
    (hh (φ x)).trans (congrArg (fun t => h * t * h⁻¹) (hg x))
  have e2 : h * (g * (x : G) * g⁻¹) * h⁻¹ = (h * g) * (x : G) * (h * g)⁻¹ :=
    ((congrArg (fun t => t * h⁻¹)
        ((mul_assoc h (g * (x : G)) g⁻¹).symm.trans
          (congrArg (fun t => t * g⁻¹) (mul_assoc h g (x : G)).symm))).trans
      ((mul_assoc ((h * g) * (x : G)) g⁻¹ h⁻¹).trans
        (congrArg (fun t => ((h * g) * (x : G)) * t) (mul_inv_rev h g).symm)))
  exact e1.trans e2

end BoringMath
