/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Pullback

/-!
# The constant sheaf commutes with pullback and pushforward of sheaves

This module answers the hypothesis hunt posed by the TODO in
`Mathlib.CategoryTheory.Sites.ConstantSheaf` (Equivalence section, quoted
verbatim there):

> TODO: find suitable assumptions for proving generalizations of
> `equivCommuteConstant` and `equivCommuteConstant'` above, to commute
> `constantSheaf` with pullback/pushforward of sheaves.

The hunt succeeds on the pullback side with purely site-theoretic
hypotheses, and on the pushforward side under an explicit
sheafification-commutation hypothesis; continuity alone does not suffice
on the pushforward side (see `docs/PRs/constant-sheaf-commute.md`,
FINDING 1).

## Main results

* `CategoryTheory.pullbackCommuteConstant`: for a continuous functor
  `G : C ⥤ D` whose sheaf pushforward is a right adjoint and which sends a
  terminal object `T` of `C` to a terminal object of `D`, pullback of sheaves
  commutes with the constant sheaf functor:
  `constantSheaf J A ⋙ G.sheafPullback A J K ≅ constantSheaf K A`.
* `CategoryTheory.pushforwardCommuteConstant`: pushforward of sheaves
  commutes with the constant sheaf functor,
  `constantSheaf K A ⋙ G.sheafPushforwardContinuous A J K ≅ constantSheaf J A`,
  under the candidate hypothesis `hG` that precomposition with `G.op`
  commutes with sheafification across the two topologies.

## References

* SGA 4, Exposé III, *Fonctorialité des catégories de faisceaux* (J.-L.
  Verdier), §1: morphisms of sites and the pullback/pushforward functors
  between sheaf categories.
  REVIEW(citation): the exposé and section were verified against web mirrors
  of SGA 4; the exact proposition number for constant sheaves under
  pullback/pushforward is not pinned.
* Stacks Project, chapter *Sites and Sheaves*, Section 14 "Morphisms of
  sites" (tag 00X0); chapter *Étale Cohomology*, Section 64 "Locally constant
  sheaves" (tag 09Y8) for constant sheaves on sites.
* D. Asgeirsson, `Mathlib.CategoryTheory.Sites.ConstantSheaf`: the constant
  sheaf functor, `constantSheafAdj`, `equivCommuteConstant`, and the TODO
  addressed here.
-/

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Limits Opposite

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable (A : Type u₃) [Category.{v₃} A]
variable (G : C ⥤ D) [Functor.IsContinuous G J K]
variable [HasWeakSheafify J A] [HasWeakSheafify K A]

section Pullback

variable [(G.sheafPushforwardContinuous A J K).IsRightAdjoint]
variable {T : C} (hT : IsTerminal T) (hT' : IsTerminal (G.obj T))

-- Reference: SGA 4, Exposé III, §1 (morphisms of sites), formalized in-file by
-- D. Asgeirsson's `equivCommuteConstant` (`Sites.ConstantSheaf`); Stacks
-- Project, Sites, §14 "Morphisms of sites" (tag 00X0).
-- REVIEW(citation): exact SGA 4 Exposé III proposition number not pinned.
/-- **Pullback commutes with the constant sheaf functor**: for a continuous
functor `G : C ⥤ D` whose sheaf pushforward is a right adjoint and which sends
a terminal object `T` of `C` to a terminal object of `D`,
`constantSheaf J A ⋙ G.sheafPullback A J K ≅ constantSheaf K A`.
Both sides are left adjoint to evaluation at `op T` (resp. `op (G.obj T)`),
so the iso is `Adjunction.leftAdjointUniq`, as in `equivCommuteConstant`. -/
noncomputable def pullbackCommuteConstant : -- noncomputable: choice-backed sheafification
    constantSheaf J A ⋙ G.sheafPullback A J K ≅ constantSheaf K A :=
  ((constantSheafAdj J A hT).comp (G.sheafAdjunctionContinuous A J K)).leftAdjointUniq
    (constantSheafAdj K A hT')

end Pullback

section Pushforward

-- Reference: SGA 4, Exposé III, §1 (direct image of a constant sheaf is
-- constant only under a fiber-connectedness condition); Stacks Project,
-- Sites, §14 "Morphisms of sites" (tag 00X0).
-- REVIEW(citation): exact SGA 4 Exposé III proposition number not pinned.
/-- **Pushforward commutes with the constant sheaf functor** under the
candidate hypothesis `hG` that precomposition with `G.op` commutes with
sheafification across `K` and `J`:
`constantSheaf K A ⋙ G.sheafPushforwardContinuous A J K ≅ constantSheaf J A`.
The hypothesis `hG` is the obstruction isolated by the hunt: continuity of
`G` alone does not imply it (the pushforward of a constant sheaf is the
sheaf of locally constant functions on the fibers of `G`). -/
noncomputable def pushforwardCommuteConstant -- noncomputable: choice-backed sheafification
    (hG : presheafToSheaf K A ⋙ G.sheafPushforwardContinuous A J K ≅
      (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj G.op ⋙ presheafToSheaf J A) :
    constantSheaf K A ⋙ G.sheafPushforwardContinuous A J K ≅ constantSheaf J A :=
  Functor.associator (Functor.const Dᵒᵖ) (presheafToSheaf K A)
      (G.sheafPushforwardContinuous A J K) ≪≫
    Functor.isoWhiskerLeft (Functor.const Dᵒᵖ) hG ≪≫
      (Functor.associator (Functor.const Dᵒᵖ)
        ((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj G.op) (presheafToSheaf J A)).symm ≪≫
        Functor.isoWhiskerRight (Functor.constCompWhiskeringLeftIso (J := Cᵒᵖ) (C := A) G.op)
          (presheafToSheaf J A)

end Pushforward

end CategoryTheory
