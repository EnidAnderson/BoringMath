/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Ordinary generating functions — ticket #295

The OGF of a sequence `a : ℕ → ℚ` is the formal power series `∑ aₙ Xⁿ`; the
Cauchy product (convolution of coefficients) is mathlib's `PowerSeries.coeff_mul`.

## References
* [Stanley] R. P. Stanley, *Enumerative Combinatorics*, vol. 1, Cambridge 1997,
  ch. 1 (ordinary generating functions).
* mathlib pin v4.35.0-rc3: `PowerSeries.mk`, `PowerSeries.coeff_mk`,
  `PowerSeries.coeff_mul`, `PowerSeries.ext`.
-/

namespace BoringMath

-- Reference: [Stanley], vol. 1, ch. 1; mathlib `PowerSeries.mk`.
/-- The **ordinary generating function** of a sequence over `ℚ`. -/
def ogf (a : ℕ → ℚ) : PowerSeries ℚ := PowerSeries.mk a

-- Reference: mathlib pin v4.35.0-rc3, `PowerSeries.coeff_mk`.
/-- The `n`-th coefficient of an OGF is the `n`-th term of the sequence (proved). -/
theorem coeff_ogf (a : ℕ → ℚ) (n : ℕ) : PowerSeries.coeff n (ogf a) = a n :=
  PowerSeries.coeff_mk n a

-- Reference: [Stanley], vol. 1, ch. 1 (Cauchy product); mathlib pin v4.35.0-rc3,
-- `PowerSeries.ext`, `PowerSeries.coeff_mul`, `Finset.Nat.antidiagonal`.
/-- **Cauchy product**: the OGF of the convolution of two sequences is the
product of their OGFs (proved via `PowerSeries.coeff_mul`). -/
theorem ogf_mul (a b : ℕ → ℚ) :
    ogf a * ogf b = ogf (fun n => ∑ k ∈ Finset.range (n + 1), a k * b (n - k)) := by
  apply PowerSeries.ext
  intro n
  calc PowerSeries.coeff n (ogf a * ogf b)
      = ∑ p ∈ Finset.antidiagonal n,
          PowerSeries.coeff p.1 (ogf a) * PowerSeries.coeff p.2 (ogf b) :=
        PowerSeries.coeff_mul n (ogf a) (ogf b)
    _ = ∑ p ∈ Finset.antidiagonal n, a p.1 * b p.2 :=
        Finset.sum_congr (Eq.refl _) fun p _ =>
          congrArg₂ (fun x y => x * y) (coeff_ogf a p.1) (coeff_ogf b p.2)
    _ = ∑ k ∈ Finset.range (n + 1), a k * b (n - k) :=
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => a i * b j) n
    _ = PowerSeries.coeff n
          (ogf fun n => ∑ k ∈ Finset.range (n + 1), a k * b (n - k)) :=
        (coeff_ogf (fun n => ∑ k ∈ Finset.range (n + 1), a k * b (n - k)) n).symm

end BoringMath
