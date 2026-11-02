/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand

/-!
# The cyclotomic polynomial at prime powers, and the value `Φ_q(1) = p`

Mathlib's `Polynomial.cyclotomic` is choice-backed at the pin (it is defined
through `Exists.choose` in a `noncomputable section`). This module therefore
builds the cyclotomic polynomial at the prime power `q = p ^ (k + 1)` as
explicit sum data — the geometric sum
`Φ_{p^(k+1)}(X) = ∑_{i < p} (X ^ p ^ k) ^ i = Φ_p(X ^ p ^ k)` — proves it equal
to `Polynomial.cyclotomic (p ^ (k + 1)) ℤ`, records the recursion
`Φ_{p^(k+2)}(X) = Φ_{p^(k+1)}(X ^ p)`, states the quotient identity
`Φ_p(X) = (X ^ p - 1)/(X - 1)` at the polynomial level, and proves the value
ledger `Φ_q(1) = p` for `q = p ^ k` with `k ≥ 1`.

Computability note at the pin `v4.35.0-rc3`: `Polynomial.semiring` is itself
`noncomputable` (`Mathlib/Algebra/MonoidAlgebra/Basic.lean` opens with
`@[expose] public noncomputable section`), so even the explicit geometric sum
is a `noncomputable def` and cannot be `#eval`'d; the point of `phiPrimePow`
is the explicit *statement-level* data and its proved equality with
`Polynomial.cyclotomic`, not kernel evaluation.

## References
* [Washington] L. C. Washington, *Introduction to Cyclotomic Fields*, 2nd ed.,
  Springer GTM 83, 1997, Chapter 2 "Basic Results".
-/

namespace BoringMath

open scoped Polynomial

-- Reference: [Washington], Chapter 2 "Basic Results", §2 (for a prime `p`,
-- `Φ_{p^(k+1)}(X) = Φ_p(X ^ p ^ k) = ∑_{i < p} (X ^ p ^ k) ^ i`).
-- REVIEW(citation): pin down the exact section number in review.
/-- **The cyclotomic polynomial at a prime power, as explicit data.**
`phiPrimePow p k` is `Φ_{p^(k+1)}(X) = ∑_{i < p} (X ^ p ^ k) ^ i`, the geometric
sum `Φ_p(X ^ p ^ k)`. `noncomputable` at the pin because `Polynomial.semiring`
is noncomputable there (see the module docstring). -/
noncomputable def phiPrimePow (p k : ℕ) : ℤ[X] :=
  ∑ i ∈ Finset.range p, (Polynomial.X ^ p ^ k) ^ i

-- Reference: [Washington], Chapter 2 "Basic Results", §2 (prime-power form of
-- the cyclotomic polynomial); mathlib
-- `Polynomial.cyclotomic_prime_pow_eq_geom_sum`.
-- REVIEW(citation): pin down the exact section number in review.
/-- **The explicit prime-power data equals mathlib's cyclotomic polynomial**:
`phiPrimePow p k = Polynomial.cyclotomic (p ^ (k + 1)) ℤ`. -/
theorem phiPrimePow_eq_cyclotomic {p : ℕ} (hp : p.Prime) (k : ℕ) :
    phiPrimePow p k = Polynomial.cyclotomic (p ^ (k + 1)) ℤ :=
  (Polynomial.cyclotomic_prime_pow_eq_geom_sum (R := ℤ) (p := p) (n := k) hp).symm

-- Reference: [Washington], Chapter 2 "Basic Results", §2 (the recursion
-- `Φ_{p^(k+2)}(X) = Φ_{p^(k+1)}(X ^ p)`); mathlib
-- `Polynomial.cyclotomic_expand_eq_cyclotomic`, with
-- `Polynomial.expand_eq_comp_X_pow : expand R p f = f.comp (X ^ p)`.
-- REVIEW(citation): pin down the exact section number in review.
/-- **Recursion for prime-power cyclotomic polynomials**:
`Φ_{p^(k+2)}(X) = Φ_{p^(k+1)}(X ^ p)`, written via `Polynomial.expand`
(which is composition with `X ^ p`). -/
theorem phiPrimePow_expand_succ {p : ℕ} (hp : p.Prime) (k : ℕ) :
    Polynomial.expand ℤ p (phiPrimePow p k) = phiPrimePow p (k + 1) := by
  have hstep1 :
      Polynomial.expand ℤ p (phiPrimePow p k)
        = Polynomial.expand ℤ p (Polynomial.cyclotomic (p ^ (k + 1)) ℤ) :=
    congrArg (fun f : ℤ[X] => Polynomial.expand ℤ p f) (phiPrimePow_eq_cyclotomic hp k)
  have hstep2 :
      Polynomial.expand ℤ p (Polynomial.cyclotomic (p ^ (k + 1)) ℤ)
        = Polynomial.cyclotomic (p ^ (k + 1) * p) ℤ :=
    Polynomial.cyclotomic_expand_eq_cyclotomic hp (dvd_pow_self p (Nat.succ_ne_zero k)) ℤ
  have hstep3 :
      Polynomial.cyclotomic (p ^ (k + 1) * p) ℤ
        = Polynomial.cyclotomic (p ^ (k + 1 + 1)) ℤ :=
    congrArg (fun n : ℕ => Polynomial.cyclotomic n ℤ) (pow_succ p (k + 1)).symm
  have hstep4 :
      Polynomial.cyclotomic (p ^ (k + 1 + 1)) ℤ = phiPrimePow p (k + 1) :=
    (phiPrimePow_eq_cyclotomic hp (k + 1)).symm
  exact hstep1.trans (hstep2.trans (hstep3.trans hstep4))

-- Reference: [Washington], Chapter 2 "Basic Results", §2 (for a prime `p`,
-- `Φ_p(X) = 1 + X + ... + X ^ (p - 1)`); mathlib `Polynomial.cyclotomic_prime`.
-- REVIEW(citation): pin down the exact section number in review.
/-- **The prime cyclotomic polynomial as a geometric sum over ℤ**:
`Φ_p(X) = ∑_{i < p} X ^ i`. -/
theorem cyclotomic_prime_eq_geom_sum (p : ℕ) [Fact p.Prime] :
    Polynomial.cyclotomic p ℤ = ∑ i ∈ Finset.range p, Polynomial.X ^ i :=
  Polynomial.cyclotomic_prime ℤ p

-- Reference: [Washington], Chapter 2 "Basic Results", §2 (for a prime `p`,
-- `Φ_p(X) = (X ^ p - 1)/(X - 1)`, stated as a product identity since `X - 1`
-- is monic); mathlib `Polynomial.cyclotomic_prime_mul_X_sub_one`.
-- REVIEW(citation): pin down the exact section number in review.
/-- **The quotient identity for a prime cyclotomic polynomial at the
polynomial level over ℤ**: `Φ_p(X) * (X - 1) = X ^ p - 1`. -/
theorem cyclotomic_prime_mul_X_sub_one (p : ℕ) [Fact p.Prime] :
    Polynomial.cyclotomic p ℤ * (Polynomial.X - 1) = Polynomial.X ^ p - 1 :=
  Polynomial.cyclotomic_prime_mul_X_sub_one ℤ p

-- Reference: [Washington], Chapter 2 "Basic Results", §2 (for `q = p ^ (k+1)`,
-- `Φ_q(X) = (X ^ q - 1)/(X ^ (q / p) - 1)`, stated as a product identity);
-- mathlib `Polynomial.cyclotomic_prime_pow_mul_X_pow_sub_one`.
-- REVIEW(citation): pin down the exact section number in review.
/-- **The quotient identity for a prime power at the polynomial level over ℤ**:
`Φ_{p^(k+1)}(X) * (X ^ p ^ k - 1) = X ^ p ^ (k + 1) - 1`. -/
theorem cyclotomic_prime_pow_mul_X_pow_sub_one (p k : ℕ) [Fact p.Prime] :
    Polynomial.cyclotomic (p ^ (k + 1)) ℤ * (Polynomial.X ^ p ^ k - 1)
      = Polynomial.X ^ p ^ (k + 1) - 1 :=
  Polynomial.cyclotomic_prime_pow_mul_X_pow_sub_one ℤ p k

-- Reference: [Washington], Chapter 2 "Basic Results", §2 (`Φ_n(1) = p` when
-- `n = p ^ k` is a prime power); mathlib
-- `Polynomial.eval_one_cyclotomic_prime_pow`.
-- REVIEW(citation): pin down the exact section number in review.
/-- **The value ledger**: for a prime `p` and `k ≥ 1`,
`(Polynomial.cyclotomic (p ^ k) ℤ).eval 1 = p`, i.e. `Φ_{p^k}(1) = p`. -/
theorem cyclotomic_prime_pow_eval_one {p : ℕ} [Fact p.Prime] {k : ℕ} (hk : 1 ≤ k) :
    (Polynomial.cyclotomic (p ^ k) ℤ).eval 1 = p :=
  Eq.subst (motive := fun e => (Polynomial.cyclotomic (p ^ e) ℤ).eval 1 = p)
    (Nat.sub_add_cancel hk)
    (Polynomial.eval_one_cyclotomic_prime_pow (R := ℤ) (p := p) (k - 1))

-- Reference: [Washington], Chapter 2 "Basic Results", §2
-- (`Φ_{p^(k+1)}(1) = p`); mathlib `Polynomial.eval_one_cyclotomic_prime_pow`,
-- transported along `phiPrimePow_eq_cyclotomic`.
-- REVIEW(citation): pin down the exact section number in review.
/-- **The value ledger for the explicit prime-power data**:
`(phiPrimePow p k).eval 1 = p`, i.e. `Φ_{p^(k+1)}(1) = p`. -/
theorem phiPrimePow_eval_one {p : ℕ} [Fact p.Prime] (k : ℕ) :
    (phiPrimePow p k).eval 1 = p :=
  Eq.subst (motive := fun f : ℤ[X] => f.eval 1 = p)
    (phiPrimePow_eq_cyclotomic Fact.out k).symm
    (Polynomial.eval_one_cyclotomic_prime_pow (R := ℤ) (p := p) k)

end BoringMath
