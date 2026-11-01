/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.NumberTheory.Bernoulli

/-!
# Bernoulli parity row: the consume-or-cite wrapper (M.1.3a, ticket #204)

The 2026-11-01 audit (`docs/AUDITS/2026-11-01-bernoulli-audit.md`) found the
parity law already in mathlib at the pin and no growth bound anywhere. Per the
consume-or-cite law (STYLE.C) this module adds ONLY a thin statement-side
wrapper row consuming the mathlib lemma; the growth row is a recorded gap,
deferred to a separate moderate ticket — no padding.

## References
* [Mathlib-pin] mathlib `v4.35.0-rc3`, `Mathlib/NumberTheory/Bernoulli.lean`
  (`bernoulli_eq_zero_of_odd`).
* [Davenport] H. Davenport, *Multiplicative Number Theory*, 3rd ed., Springer,
  2000, Ch. 23 (Bernoulli numbers and the zeta function).
-/

namespace BoringMath

-- Reference: mathlib pin v4.35.0-rc3, Mathlib/NumberTheory/Bernoulli.lean
-- `bernoulli_eq_zero_of_odd` (consumed, not duplicated); standard statement:
-- Bernoulli numbers at odd indices > 1 vanish (Davenport, 3rd ed., Ch. 23, the generating-function parity).
-- REVIEW(citation): pin the textbook section in review.
/-- **Bernoulli parity row** (M.1.3a): odd-indexed Bernoulli numbers above `1`
vanish — a one-line consumption of mathlib's `bernoulli_eq_zero_of_odd`. -/
theorem bernoulli_parity_row {n : ℕ} (hodd : Odd n) (hlt : 1 < n) :
    bernoulli n = 0 :=
  bernoulli_eq_zero_of_odd hodd hlt

end BoringMath
