/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Basic

/-!
# Shannon entropy — ticket #542 (proposed range #339–#342)

Finite Shannon entropy and its laws (nonnegativity, the chain rule under
independence). Mathlib at the pin has `BinaryEntropy` and coding/Hamming/
Kullback–Leibler (`InformationTheory.*`) but no Shannon entropy of a finite
distribution (audited: #339–#342 are gaps; feeds BPP/PAC #308 and the
games/entropy rows).

## References
* [Shannon 1948] C. E. Shannon, *A Mathematical Theory of Communication*,
  Bell System Tech. J. 27 (1948) 379–423, §6.
* [Cover–Thomas] T. M. Cover, J. A. Thomas, *Elements of Information Theory*,
  2nd ed., Wiley 2006, ch. 2.
* mathlib pin v4.35.0-rc3: `Analysis/SpecialFunctions/BinaryEntropy`,
  `InformationTheory/Hamming`, `InformationTheory/KullbackLeibler`;
  MISSING: Shannon entropy of a finite PMF.
-/

namespace BoringMath

-- Reference: [Shannon 1948], §6 (H = -Σ pᵢ log pᵢ).
-- NONCOMPUTABLE: `Real.log` is noncomputable at the pin (content-forced,
-- STYLE §2.3).
/-- **Shannon entropy** of a finite distribution `p` on `s` (nats). -/
noncomputable def shannonEntropy {α : Type*} (s : Finset α) (p : α → ℝ) : ℝ :=
  -Finset.sum s fun i => p i * Real.log (p i)

-- Reference: [Cover–Thomas], ch. 2, Theorem 2.1.1 (0 ≤ H ≤ log |s|).
-- TEMPORARY SORRY with peeling plan.
-- PEELING PLAN (#542): for `p i ∈ [0, 1]`, `-p i * log (p i) ≥ 0` termwise
-- (`Real.log` nonpositivity on `(0,1]`, pin `Real.log_nonpos`), then
-- `Finset.sum` nonnegativity.
/-- **Entropy is nonnegative** on a subdistribution with values in `[0,1]`. -/
theorem shannonEntropy_nonneg {α : Type*} {s : Finset α} {p : α → ℝ}
    (hp0 : ∀ i ∈ s, 0 ≤ p i) (hp1 : ∀ i ∈ s, p i ≤ 1) :
    0 ≤ shannonEntropy s p := by
  sorry

-- Reference: [Cover–Thomas], ch. 2, Theorem 2.5.1 (H(X,Y) = H(X) + H(Y) for
-- independent X, Y). TEMPORARY SORRY with peeling plan.
-- PEELING PLAN (#542): on the product `s ×ˢ t` with `p(i,j) = p₁ i * p₂ j`,
-- the sum splits as `H(s,p₁) + H(t,p₂)` after `Real.log_mul` (pin:
-- `Real.log_mul`).
/-- **Chain rule under independence**: `H(X,Y) = H(X) + H(Y)`. -/
theorem shannonEntropy_prod {α β : Type*} {s : Finset α} {t : Finset β}
    {p₁ : α → ℝ} {p₂ : β → ℝ} :
    shannonEntropy (s ×ˢ t) (fun ij => p₁ ij.1 * p₂ ij.2) =
      shannonEntropy s p₁ + shannonEntropy t p₂ := by
  sorry

end BoringMath
