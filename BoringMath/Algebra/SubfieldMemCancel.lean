/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Algebra.Field.Subfield.Basic

/-!
# Subfield membership cancellation across an inclusion

This module contributes the first "boring" subfield-algebra lemma of the
program's escape-reduction layer: membership of a two-term sum in a larger
subfield, with one summand in a smaller one, forces the other summand into
the larger subfield.

Instantiation (the program's `paid_of_escape` seed, register Section 63,
PEEL G): with `L := C`, `K := K0`, `K' := K1`, `a := rho`,
`b := Ci (2 * pi)`, the lemma is the reduction step "`Ci (2 * pi)` in `K0`
together with `rho + Ci (2 * pi)` in `K1` forces `rho` into `K1`", whose
contrapositive transfers the escape sink `rho not in K1` to the one-point
instance `Ci (2 * pi) not in K0`.

## References
* [Jacobson] N. Jacobson, *Basic Algebra I*, 2nd ed., W. H. Freeman, 1985.
-/

universe u

namespace Subfield

-- Reference: [Jacobson], Chapter 2, §1 (subfields are closed under the field
-- operations; closure transfers along inclusion).
-- REVIEW(citation): pin down the exact section in review.
/-- **Membership cancellation on the right across an inclusion.** If `K ≤ K'`
are subfields of `L`, `a + b ∈ K'`, and `b ∈ K`, then `a ∈ K'`: a summand of
a `K'`-member cannot escape `K'` when the other summand lies in the smaller
subfield. -/
theorem add_mem_cancel_right_of_le {L : Type u} [DivisionRing L] {K K' : Subfield L}
    (hle : K ≤ K') {a b : L} (h : a + b ∈ K') (hb : b ∈ K) : a ∈ K' :=
  -- Linear proof: each input is used exactly once. Leibniz substitutivity
  -- (`Eq.subst`) applied to the fully instantiated ring identity
  -- `add_sub_cancel_right a b : (a + b) - b = a` and to the `K'`-closure
  -- `Subfield.sub_mem` of `h` against `b ∈ K'`, which is `hb` transferred
  -- along the inclusion `hle` by `mem_of_le_of_mem`. No tactic is used.
  Eq.subst (add_sub_cancel_right a b) (Subfield.sub_mem K' h (mem_of_le_of_mem hle hb))

end Subfield
