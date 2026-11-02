# Candidate PR: small-order non-simplicity (orders `p*q` and `p^2`)

Ticket: **#280 CFSG.SMALL** (sub-tickets #280a, #280b landed; #280c order 12 is a
deliberate `sorry` with peeling plan). Module:
`BoringMath/GroupTheory/Simple/SmallOrders.lean`. Branch (proposed):
`pr/grouptheory-small-orders`.

## Statement

* `not_isSimpleGroup_of_card_eq_prime_mul_prime` — a finite group of order
  `p * q` with primes `p < q` is not simple: Sylow III (`n_q ≡ 1 [MOD q]`,
  `n_q ∣ p`) forces `n_q = 1`, so the Sylow `q`-subgroup is normal of order `q`.
* `not_isSimpleGroup_of_card_eq_prime_sq` — a finite group of order `p ^ 2` is
  not simple: commutative (`IsPGroup.isMulCommutative_of_card_eq_prime_sq`),
  Cauchy gives an element of order `p`, and its cyclic subgroup is normal,
  proper, nontrivial.
* `not_isSimpleGroup_of_card_eq_twelve` — order 12 (the `PSL(2,3) ≅ A_4`
  level): **TEMPORARY SORRY with peeling plan** (#280c): `n_3 ∈ {1,4}`; in the
  `n_3 = 4` case the conjugation action on `Sylow 3 G` embeds `G` into `S_4`
  (transitive image, `4 ∣ |im| ∣ 12`), and order-12 subgroups of `S_4` are
  `A_4` (census in `BoringMath/Symmetry/S4Census.lean`), so `kleinFour` pulls
  back to a normal subgroup of order 4.

## Literature

* [Dummit–Foote], Ch. 4, Sec. 6 (Sylow's theorems, counting applications).
  REVIEW(citation): pin the exact section against a held copy in review.
* [Wilson] GTM 251, ch. 1 (smallest nonabelian simple group is `A_5`, order 60).

## Where it would live in Mathlib

New module `Mathlib/GroupTheory/Simple/SmallOrders.lean` (or into
`Mathlib/GroupTheory/Sylow.lean`'s application section); the statements use
only `IsSimpleGroup` + Sylow + Cauchy API already in Mathlib.

## Does Mathlib already have it?

No (checked at pin v4.35.0-rc3): `IsSimpleGroup` API has the prime-order
iff (abelian case, `Cyclic.lean`), quotient/surjective lemmas, and the
alternating `A_n` (`n ≥ 5`) simplicity; there is **no** order-`pq` /
order-`p^2` / small-order non-simplicity lemma. Ours adds exactly those.

## Verification

* `lake build BoringMath.GroupTheory.Simple.SmallOrders` — clean except the
  one deliberate `sorry` (#280c).
* `scripts/check-style.sh` — zero violations.
