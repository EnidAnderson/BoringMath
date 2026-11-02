/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Computability.Partrec
import BoringMath.Complexity.Defs

/-!
# Complexity ↔ computability bridge — ticket #539

Every time-bounded (`DTIME`) language is decidable by a total computable
function: the bridge from `Complexity/Defs.lean` (#301–#308) to mathlib's
recursion theory (`Computability`). Feeds the Cook–Levin spine #302–#304
and the Kolmogorov-complexity row #339–#342.

## References
* [Arora–Barak], ch. 1–2; [Sipser] M. Sipser, *Introduction to the Theory of
  Computation*, ch. 7 (decidability).
* mathlib pin v4.35.0-rc3: `Computability.Partrec` (`Computable`),
  `Turing.TM0` (`ToPartrec`: Turing machines are partial recursive).
-/

namespace BoringMath

open Turing

-- Reference: [Sipser], ch. 7.1 (a time-bounded machine always halts, so its
-- language is decidable). TEMPORARY SORRY with peeling plan.
-- PEELING PLAN (#539): (i) from `h : L ∈ DTIME t` get the machine `M` with
-- `AcceptsWithin M (TM0.init x) (t x.length) ↔ x ∈ L`; (ii) the characteristic
-- function `x ↦ decide (x ∈ L)` is `M`-computable via the pin's
-- `TM0 → Partrec` translation (`Computability/TuringMachine/ToPartrec`);
-- (iii) wrap as `Computable`.
/-- **Time-bounded implies decidable**: every `DTIME t` language has a
total computable characteristic function. -/
theorem DTIME_decidable {t : ℕ → ℕ} {L : Language} (h : L ∈ DTIME t) :
    ∃ f : List Bool → Bool, Computable f ∧ ∀ x : List Bool, f x = true ↔ x ∈ L := by
  sorry

end BoringMath
