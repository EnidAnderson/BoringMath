/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Data.ZMod.Basic
import BoringMath.GroupTheory.Simple.Classification

/-!
# The order of `PSL(n, ZMod p)` — the roots-of-unity gcd formula

Ticket **#283** (= **#235** detailed): over the prime field `F_p`, the group of
`n`-th roots of unity has order `gcd n (p - 1)` (because `F_pˣ` is cyclic of
order `p - 1`), which turns the cardinality split
`card_PSL_finiteField_mul_card_rootsOfUnity` (in
`BoringMath.GroupTheory.Simple.Classification`) into the full order formula

  `|PSL(n, F_p)| * gcd n (p - 1) = (∏_{i < n} (p^n - p^i)) / (p - 1)`.

The gcd formula itself is a TEMPORARY SORRY with a peeling plan (§7); the
order formula below it is proved from it.

## References
* [Wilson] R. A. Wilson, *The Finite Simple Groups*, Springer GTM 251, 2009,
  ch. 5 (the order of `PSL(n, q)`: `(1 / ((q-1) gcd(n, q-1))) ∏ (q^n - q^i)`).
* [ATLAS] J. H. Conway et al., *ATLAS of Finite Groups*, OUP 1985, p. xvi.
* mathlib pin v4.35.0-rc3: `rootsOfUnityEquivNthRoots`, `Polynomial.card_nthRoots`,
  `ZMod.pow_card_sub_one_eq_one`, `FiniteField.splits_X_pow_card_sub_X` /
  `roots_X_pow_card_sub_X`, `IsCyclic (ZMod p)ˣ` (`Mathlib/RingTheory/ZMod/UnitsCyclic.lean`),
  `Matrix.card_SL_field` (via `Classification.lean`).
-/

namespace BoringMath

open Matrix
open scoped MatrixGroups

-- Reference: [Wilson] GTM 251, ch. 5 (the center of `SL(n, q)` is `μ_n(F_q)`,
-- of order `gcd n (q - 1)`); mathlib pin v4.35.0-rc3, `IsCyclic (ZMod p)ˣ`.
/-- **The `n`-th roots of unity in `ZMod p` number `gcd n (p - 1)`** (over the
prime field `F_pˣ` is cyclic of order `p - 1`, and the `n`-torsion of a cyclic
group of order `m` has order `gcd n m`). TEMPORARY SORRY with peeling plan. -/
theorem card_rootsOfUnity_zmod_prime {n p : ℕ} [Fact p.Prime] :
    Nat.card (rootsOfUnity n (ZMod p)) = Nat.gcd n (p - 1) := by
  -- TEMPORARY SORRY: the honest proof has not been instantiated yet.
  -- PEELING PLAN (ticket #283):
  --   (1) `rootsOfUnityEquivNthRoots`: `Nat.card (rootsOfUnity n R)` equals the
  --       number of roots of `X^n - 1` in `R` (`Multiset.card (nthRoots n 1)`);
  --   (2) Bezout + Fermat (`ZMod.pow_card_sub_one_eq_one`): for `a : (ZMod p)ˣ`,
  --       `a ^ n = 1 ↔ a ^ (gcd n (p - 1)) = 1`, so `nthRoots n 1` and
  --       `nthRoots (gcd n (p - 1)) 1` have the same elements in `ZMod p`;
  --   (3) for `d ∣ p - 1`, `X^d - 1 ∣ X^(p-1) - 1` and `X^(p-1) - 1` splits into
  --       distinct linear factors over `ZMod p` (`roots_X_pow_card_sub_X`),
  --       so `Multiset.card (nthRoots d 1) = d` (`splits_iff_card_roots` +
  --       nodup, with `Polynomial.card_nthRoots` for the upper bound);
  --   (4) alternatively in the cyclic group `(ZMod p)ˣ` of order `p - 1`
  --       (`IsCyclic (ZMod p)ˣ`): `n`-torsion `= zpowers (g ^ ((p-1) / gcd))`,
  --       of order `gcd n (p - 1)` via `Nat.card_zpowers` + `orderOf_pow`.
  sorry

-- Reference: `card_PSL_finiteField_mul_card_rootsOfUnity` (Classification.lean)
-- + `card_rootsOfUnity_zmod_prime` + `ZMod.card`; [Wilson] GTM 251, ch. 5.
/-- **The full order formula for `PSL(n, F_p)` over a prime field** (proved from
#283): `|PSL(n, F_p)| * gcd n (p - 1) = (∏_{i<n} (p^n - p^i)) / (p - 1)`. -/
theorem card_PSL_zmod_prime_mul_gcd {n p : ℕ} [NeZero n] [Fact p.Prime] :
    Nat.card (PSL(n, ZMod p)) * Nat.gcd n (p - 1) =
      (∏ i : Fin n, (p ^ n - p ^ (i : ℕ))) / (p - 1) :=
  (congrArg (fun c => Nat.card (PSL(n, ZMod p)) * c)
      (card_rootsOfUnity_zmod_prime (p := p) (n := n))).symm.trans
    ((card_PSL_finiteField_mul_card_rootsOfUnity (n := n) (𝔽 := ZMod p)).trans
      (congrArg (fun c => (∏ i : Fin n, (c ^ n - c ^ (i : ℕ))) / (c - 1)) (ZMod.card p)))

end BoringMath
