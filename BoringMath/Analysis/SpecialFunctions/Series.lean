/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Basic.Complex.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# The special-function shelf — ticket #501 (TREE D.8)

The transcendence line needs the entire functions `Ein`, `Si` and the
singular ones `Ci`, `E₁` as *definitional series* (TREE D.8: "definitions and
definitional series identities"). Mathlib at the pin has `Real.exp`, `Complex.exp`,
`Real.log` and the Gamma function but no `Ein`/`Ci`/`E₁`/`Si` API (audited).
This module defines the entire ones as explicit power series (computable
data) and states their analytic realization.

## References
* [Abramowitz–Stegun] M. Abramowitz, I. A. Stegun (eds.), *Handbook of
  Mathematical Functions*, Dover 1972, ch. 5 §5.1 (Ein, E₁), ch. 6 §6.2 (Si, Ci).
* [DLMF] NIST Digital Library of Mathematical Functions, §6.2, §6.12.
* mathlib pin v4.35.0-rc3: `PowerSeries`, `HasSum`; MISSING: `Ein`, `Ci`,
  `E₁`, `Si` (TREE D.8).
-/

namespace BoringMath

-- Reference: [DLMF] §6.12.2 — `Ein(z) = Σ_{n≥1} zⁿ / (n · n!)`.
-- NONCOMPUTABLE: complex division (`Complex.instInv`) is noncomputable at the
-- pin, so the coefficient function is too (content-forced, STYLE §2.3).
/-- The **entire exponential integral** `Ein` as a power series:
`einSeries = Σ_{n≥1} Xⁿ / (n · n!)`. -/
noncomputable def einSeries : PowerSeries ℂ :=
  PowerSeries.mk fun n => if n = 0 then 0 else ((n : ℂ) * (n.factorial : ℂ))⁻¹

-- Reference: [DLMF] §6.2.3 — `Si(z) = Σ_{n≥0} (-1)ⁿ z^{2n+1} / ((2n+1)·(2n+1)!)`.
-- NONCOMPUTABLE: same as `einSeries` (complex division is noncomputable).
/-- The **sine integral** `Si` as a power series. -/
noncomputable def siSeries : PowerSeries ℂ :=
  PowerSeries.mk fun n =>
    if n % 2 = 0 then 0
    else ((-1 : ℂ) ^ (n / 2)) * ((n : ℂ) * (n.factorial : ℂ))⁻¹

-- Reference: [DLMF] §6.12.1 (`Ein` is entire, `Ein z = E₁(z) + ln z + γ`).
-- TEMPORARY SORRY with peeling plan.
-- PEELING PLAN (#501, TREE D.8): (i) the coefficient bound `|zⁿ/(n·n!)| ≤
-- |z|ⁿ/n!` gives summability on every disc (comparison with `exp`);
-- (ii) term-by-term differentiability of the power series (pin:
-- `PowerSeries`/`HasSum` differentiability API) gives `Differentiable ℂ f`.
/-- **The series `einSeries` is entire**: there is an entire function whose
value at `z` is the sum of the series. -/
theorem exists_entire_ein :
    ∃ f : ℂ → ℂ, Differentiable ℂ f ∧
      ∀ z : ℂ, HasSum
        (fun n : ℕ => if n = 0 then 0 else z ^ n / ((n : ℂ) * (n.factorial : ℂ))) (f z) := by
  sorry

end BoringMath
