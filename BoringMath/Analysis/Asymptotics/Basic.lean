/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Analysis.Asymptotics.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Sqrt

/-!
# Asymptotics — ticket #502 (proposed range #350–#352)

Asymptotic equivalence of sequences, and the analytic-combinatorics layer:
saddle-point/Mellin asymptotics for coefficients of generating functions
(feeds `Combinatorics` #297–#298), with Stirling's formula as the first law.
Mathlib at the pin has the `Asymptotics` filter API (`IsBigO`/`IsLittleO`)
but no sequence-asymptotic wrapper and no Stirling.

## References
* [de Bruijn] N. G. de Bruijn, *Asymptotic Methods in Analysis*, North-Holland
  1958, ch. 3 (saddle point), ch. 5.
* [Flajolet–Sedgewick] P. Flajolet, R. Sedgewick, *Analytic Combinatorics*,
  Cambridge 2009, ch. VIII (saddle-point asymptotics).
* [Stirling 1730]; mathlib pin v4.35.0-rc3: `Asymptotics.IsBigO`/`IsLittleO`;
  MISSING: Stirling's formula, saddle-point transfer.
-/

namespace BoringMath

-- Reference: [Flajolet–Sedgewick], ch. VIII.1 (asymptotic equivalence `u ~ v`).
/-- **Asymptotic equivalence** of real sequences: `u n - v n = o(v n)`. -/
def IsAsymptotic (u v : ℕ → ℝ) : Prop :=
  Asymptotics.IsLittleO Filter.atTop (fun n : ℕ => u n - v n) v

-- Reference: [Stirling 1730]; [de Bruijn], ch. 3.6 (Stirling via the Gamma
-- integral). TEMPORARY SORRY with peeling plan.
-- PEELING PLAN (#502, range #350–#352): (i) log-convexity of `n!` gives the
-- two-sided bound `√(2πn)(n/e)ⁿ ≤ n! ≤ √(2πn)(n/e)ⁿ e^{1/(12n)}`
-- (Wallis product for the constant); (ii) hence `IsAsymptotic` as stated.
/-- **Stirling's formula**: `n! ~ √(2πn) (n/e)ⁿ`. -/
theorem stirling_isAsymptotic :
    IsAsymptotic (fun n : ℕ => (n.factorial : ℝ))
      (fun n : ℕ => Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n) := by
  sorry

end BoringMath
