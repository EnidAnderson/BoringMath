/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringMath.AlgebraicGeometry.AlgebraicCycle.RationalEquivalence

/-!
# The Chow group `A_*(X)` of a scheme (I.1, part 2)

The **Chow group** `A_*(X)` of a scheme `X` (ticket I.1, #281): the quotient of
the group of cycles `Z_*(X) = AlgebraicCycle X ℤ` by the rational-equivalence
subgroup (the A¹-family structure-of-record of
`AlgebraicCycle/RationalEquivalence.lean`), with the class map `chowClass`
and the membership characterization.

The graded pieces `A_k(X)` by support dimension, and the functoriality
(pushforward/pullback on Chow groups), are I.2 (#283) — not here.

## References
* W. Fulton, *Intersection Theory*, 2nd ed., Springer 1998, ch. 1, §1.3, §1.5?
  (the Chow group `A_*(X)`). REVIEW(citation): pin the section.
* Stacks Project, Chow Homology, §42.10? (rational equivalence and the Chow
  group; tags 02R9 ff.). REVIEW(citation): pin the tags.
* Hartshorne, *Algebraic Geometry*, GTM 52, App. A, §1 (Chow groups).
  REVIEW(citation): pin.
-/

universe u

namespace AlgebraicGeometry

open CategoryTheory

variable (X : Scheme.{u})

-- Reference: Fulton ch. 1, §1.3/§1.5? (the Chow group as the quotient of the
-- cycle group by rational equivalence).
-- REVIEW(citation): pin the section.
/-- The **Chow group** `A_*(X)` of `X`: cycles modulo rational equivalence. -/
abbrev chowGroup (X : Scheme.{u}) : Type u :=
  AlgebraicCycle X ℤ ⧸ rationalEquivalenceAddSubgroup X

-- Reference: the quotient of an `AddCommGroup` by an `AddSubgroup` (normal,
-- since the group is commutative) is an `AddCommGroup` (mathlib's
-- `QuotientAddGroup`).
/-- The Chow group is an abelian group. `noncomputable`: the quotient type
mentions the (choice-backed) fiber product `X × 𝔸¹` through the
rational-equivalence subgroup. -/
noncomputable instance chowGroupAddCommGroup : AddCommGroup (chowGroup X) := inferInstance

-- Reference: Fulton ch. 1, §1.5? (the class map `Z_*(X) → A_*(X)`).
-- REVIEW(citation): pin.
/-- The **class map** from cycles to the Chow group (the quotient map as an
`AddMonoidHom`). `noncomputable`: via the choice-backed subgroup. -/
noncomputable def chowClass (X : Scheme.{u}) : AlgebraicCycle X ℤ →+ chowGroup X :=
  QuotientAddGroup.mk' _

-- Reference: Fulton ch. 1, §1.3 (two cycles have the same class iff they are
-- rationally equivalent); mathlib's `QuotientAddGroup.eq` +
-- `AddMonoidHom.mem_range`, with `-c + d = -(c - d)` and closure under
-- negation (`map_neg`, `AddSubgroup.neg_mem`).
-- REVIEW(citation): pin.
/-- **Two cycles have the same Chow class iff they differ by
`i₀*γ - i₁*γ`** for some cycle `γ` on `X × 𝔸¹` — the A¹-family
characterization of rational equivalence. -/
theorem chowClass_eq_iff (X : Scheme.{u}) (c d : AlgebraicCycle X ℤ) :
    chowClass X c = chowClass X d ↔
      ∃ γ : AlgebraicCycle (prodAffineLine X) ℤ, rationalEquivalenceHom X γ = c - d := by
  have hneg : -c + d = -(c - d) :=
    Eq.trans (add_comm (-c) d) (Eq.trans (sub_eq_add_neg d c).symm (neg_sub c d).symm)
  refine Iff.trans (QuotientAddGroup.eq (a := c) (b := d)) ?_
  refine Iff.trans (AddMonoidHom.mem_range (f := rationalEquivalenceHom X)) ?_
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨γ, hγ⟩ := h
    refine ⟨-γ, ?_⟩
    exact Eq.trans (map_neg (rationalEquivalenceHom X) γ)
      (Eq.trans (congrArg Neg.neg hγ)
        (Eq.trans (congrArg Neg.neg hneg) (neg_neg (c - d))))
  · obtain ⟨γ, hγ⟩ := h
    refine ⟨-γ, ?_⟩
    exact Eq.trans (map_neg (rationalEquivalenceHom X) γ)
      (Eq.trans (congrArg Neg.neg hγ) hneg.symm)

end AlgebraicGeometry
