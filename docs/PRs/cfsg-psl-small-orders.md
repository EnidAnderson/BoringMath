# Candidate PR: sector-C small orders in the CFSG skeleton (PSL(2,3), PSL(3,2), A_6)

Tickets: **#281 CFSG.C.1a** (the `(2,3)` exception), **#282 CFSG.C.1b** (the
order-168 family), **#284 CFSG.C.1c** (`A_6` cardinality). Module:
`BoringMath/GroupTheory/Simple/Classification.lean` (additions to the existing
sector-C section). Branch (proposed): `pr/grouptheory-cfsg-sector-c-orders`.

## Statement (all proved, sorry-free)

* `card_SL_3_2` — `|SL(3, F_2)| = 168` (literal `card_SL_field` computation).
* `card_alternatingGroup_fin6` — `|A_6| = 360`.
* `card_rootsOfUnity_two_zmod3` — `|μ_2(ZMod 3)| = 2` (the unit group has order
  `totient 3 = 2`, so every unit squares to 1: `μ_2 = (ZMod 3)ˣ`).
* `card_center_SL_2_3` — `|Z(SL(2, F_3))| = 2` (via
  `center_equiv_rootsOfUnity'`).
* `card_PSL_2_3` — `|PSL(2, F_3)| = 12` (from `|PSL| * |Z| = |SL|`):
  closes the cardinality side of the `(2,3)` exception; non-simplicity of
  `PSL(2,3)` itself is #281's remaining step via #280c.
* `card_center_SL_3_2` — `|Z(SL(3, F_2))| = 1` (`F_2ˣ` trivial).
* `card_PSL_3_2` — `|PSL(3, F_2)| = 168` (so `PSL(3,2) ≅ PSL(2,7)` at order
  level; simplicity of the order-168 group is #282's remaining step).

## Literature

* [Wilson] GTM 251, ch. 5 (PSL definition, order formula, the `(2,2)`, `(2,3)`
  exceptions); [ATLAS] p. xvi (orders).
* mathlib pin v4.35.0-rc3: `Matrix.card_SL_field`,
  `Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity'`,
  `Subgroup.card_eq_card_quotient_mul_card_subgroup`, `ZMod.card_units_eq_totient`,
  `Nat.totient_prime`, `nat_card_alternatingGroup`.

## Where it would live in Mathlib

`Mathlib/LinearAlgebra/Matrix/ProjectiveSpecialLinearGroup.lean` /
`GeneralLinearGroup/Card.lean` (cardinality of `PSL(n, F_q)` and its center),
and `Mathlib/GroupTheory/SpecificGroups/Alternating.lean` (`|A_6|`). The
CFSG-sector packaging stays in `BoringMath/GroupTheory/Simple/Classification.lean`.

## Does Mathlib already have it?

Partially: the pin has `card_SL_field`, the center equivalence, the
quotient-cardinality split, and `|A_n| = n!/2`; it does **not** have the
assembled `|PSL(2,3)| = 12`, `|PSL(3,2)| = 168`, `|Z(SL(2,3))| = 2`, or the
`μ_n(ZMod p)` gcd formula (that is ticket #283/#235).

## Verification

* `lake build BoringMath.GroupTheory.Simple.Classification` — clean except
  the 2 pre-existing deliberate sorries (`PSL_isSimpleGroup`,
  `classification_of_finite_simple_groups`).
* `scripts/check-style.sh` — zero violations.
