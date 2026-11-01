/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Algebra.Field.Subfield.Basic

/-!
# Opposite sides of a subfield

This module contributes the "boring" subfield-algebra seeds of the program's
escape-reduction layer: a difference whose two summands lie on opposite
sides of a subfield stays outside the subfield, a two-term `a + c * b`
outside the subfield forces one summand out, and membership of a difference
transfers along an inclusion of subfields.

Instantiation (the program's register seeds): with `K := K0`, `K' := K1`,
`a := rho`, `b := sigma`, `e := E`, `ci := Ci (2 * pi)`, these are the
reduction steps "opposite sides of `K0` give a difference outside `K0`"
(register Section 62, item (1)), "`rho + c * sigma` outside `K0` with
`c ∈ K0` forces one of `rho`, `sigma` outside `K0`" (register Section 70),
and "`E - Ci(2π)` in `K1` whenever `E ∈ K1` and `Ci(2π) ∈ K0 ≤ K1`"
(register Section 63, PEEL G).

## References
* [Jacobson] N. Jacobson, *Basic Algebra I*, 2nd ed., W. H. Freeman, 1985.
-/

universe u

variable {F : Type u} [DivisionRing F]

namespace Subfield

-- Reference: [Jacobson], Chapter 2, §2.2 (a subfield is closed under the
-- field operations).
-- REVIEW(citation): pin down the exact section in review (web-checked TOC of
-- the 1985 Freeman edition: Chapter 2 "Rings", §2.2 "Types of rings", p. 90;
-- field extensions are developed at the start of Chapter 4 "Galois theory").
/-- **Difference across a membership boundary.** If `a ∈ K` and `b ∉ K`,
then `a - b ∉ K`: otherwise `b = a - (a - b)` would lie in `K`. -/
theorem sub_notMem_of_mem_of_notMem (K : Subfield F) {a b : F} (ha : a ∈ K)
    (hb : b ∉ K) : a - b ∉ K :=
  -- Leibniz substitutivity (`Eq.subst`) applied to the ring identity
  -- `sub_sub_cancel a b : a - (a - b) = b` and to the `K`-closure
  -- `Subfield.sub_mem K ha h` of `h : a - b ∈ K` against `ha : a ∈ K`.
  fun h => hb (Eq.subst (sub_sub_cancel a b) (Subfield.sub_mem K ha h))

-- Reference: [Jacobson], Chapter 2, §2.2 (closure under negation and
-- subtraction).
-- REVIEW(citation): pin down the exact section in review.
/-- **Opposite sides.** If exactly one of `a`, `b` lies in the subfield `K`,
then `a - b ∉ K`. -/
theorem sub_notMem_of_opp_sides (K : Subfield F) {a b : F}
    (h : (a ∈ K ∧ b ∉ K) ∨ (a ∉ K ∧ b ∈ K)) : a - b ∉ K := by
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact sub_notMem_of_mem_of_notMem K ha hb
  · -- `neg_sub a b : -(a - b) = b - a`; closure under negation
    -- (`Subfield.neg_mem`) moves `a - b ∈ K` to `b - a ∈ K` via `Eq.subst`,
    -- contradicting the first lemma with the roles swapped.
    exact fun hsub => sub_notMem_of_mem_of_notMem K hb ha
      (Eq.subst (neg_sub a b) (Subfield.neg_mem K hsub))

-- Reference: [Jacobson], Chapter 2, §2.2 (closure under addition and
-- multiplication).
-- REVIEW(citation): pin down the exact section in review.
/-- **Sum of a product of members is a member.** If `a`, `b`, `c ∈ K` then
`a + c * b ∈ K`. -/
theorem mem_add_mul_of_mem (K : Subfield F) {a b c : F} (ha : a ∈ K) (hb : b ∈ K)
    (hc : c ∈ K) : a + c * b ∈ K :=
  Subfield.add_mem K ha (Subfield.mul_mem K hc hb)

-- Reference: [Jacobson], Chapter 2, §2.2 (closure under addition and
-- multiplication).
-- REVIEW(citation): pin down the exact section in review.
/-- **One summand must escape.** If `c ∈ K` and `a + c * b ∉ K`, then
`a ∉ K ∨ b ∉ K`. -/
theorem notMem_left_or_notMem_right_of_add_mul_notMem (K : Subfield F) {a b c : F}
    (hc : c ∈ K) (h : a + c * b ∉ K) : a ∉ K ∨ b ∉ K :=
  -- Classical case split on `a ∈ K` via `Classical.em`; the statement is a
  -- Prop, so classical logic is admissible here (STYLE §2.3).
  Or.elim (Classical.em (a ∈ K))
    (fun ha => Or.inr (fun hb => h (mem_add_mul_of_mem K ha hb hc)))
    (fun ha => Or.inl ha)

-- Reference: [Jacobson], Chapter 2, §2.2 (closure under subtraction transfers
-- along an inclusion of subfields).
-- REVIEW(citation): pin down the exact section in review.
/-- **Difference across an inclusion.** If `K ≤ K'` are subfields of `F`,
`e ∈ K'`, and `ci ∈ K`, then `e - ci ∈ K'`. -/
theorem sub_mem_of_le_of_mem {K K' : Subfield F} (hle : K ≤ K') {e ci : F}
    (he : e ∈ K') (hci : ci ∈ K) : e - ci ∈ K' :=
  Subfield.sub_mem K' he (mem_of_le_of_mem hle hci)

end Subfield

namespace BoringMath.Register

-- Reference: register §62, item (1) (opposite-sides seed of the weight-3
-- reduction layer).
-- REVIEW(citation): internal register, not publicly verifiable.
/-- **Paid of opposite sides** (register §62 (1)): if `rho` and `sigma` lie
on opposite sides of `K0`, then `rho - sigma ∉ K0`. -/
theorem paid_of_opposite_sides (K0 : Subfield F) (rho sigma : F)
    (h : (rho ∈ K0 ∧ sigma ∉ K0) ∨ (rho ∉ K0 ∧ sigma ∈ K0)) : rho - sigma ∉ K0 :=
  Subfield.sub_notMem_of_opp_sides K0 h

-- Reference: register §62, item (1), symmetric form.
-- REVIEW(citation): internal register, not publicly verifiable.
/-- **Paid of opposite sides, symmetric** (register §62 (1)): if `rho` and
`sigma` lie on opposite sides of `K0`, then `sigma - rho ∉ K0`. -/
theorem paid_of_opposite_sides' (K0 : Subfield F) (rho sigma : F)
    (h : (sigma ∈ K0 ∧ rho ∉ K0) ∨ (sigma ∉ K0 ∧ rho ∈ K0)) : sigma - rho ∉ K0 :=
  Subfield.sub_notMem_of_opp_sides K0 h

-- Reference: register §70 / §62 (pair-single seed: `rho + c * sigma ∉ K0`
-- with `c ∈ K0` forces one of `rho`, `sigma` out of `K0`).
-- REVIEW(citation): internal register, not publicly verifiable.
/-- **Paid of pair single** (register §70/§62): if `c ∈ K0` and
`rho + c * sigma ∉ K0`, then `rho ∉ K0 ∨ sigma ∉ K0`. -/
theorem paid_of_pair_single (K0 : Subfield F) (rho sigma c : F) (hc : c ∈ K0)
    (h : rho + c * sigma ∉ K0) : rho ∉ K0 ∨ sigma ∉ K0 :=
  Subfield.notMem_left_or_notMem_right_of_add_mul_notMem K0 hc h

-- Reference: register §63, PEEL G (escape seed).
-- REVIEW(citation): internal register, not publicly verifiable.
/-- **Paid of escape** (register §63, PEEL G): if `K0 ≤ K1`, `e ∈ K1`, and
`ci ∈ K0`, then `e - ci ∈ K1`. -/
theorem paid_of_escape (K0 K1 : Subfield F) (e ci : F) (hle : K0 ≤ K1) (he : e ∈ K1)
    (hci : ci ∈ K0) : e - ci ∈ K1 :=
  Subfield.sub_mem_of_le_of_mem hle he hci

end BoringMath.Register
