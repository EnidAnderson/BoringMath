/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Probability.ProbabilityMassFunction.Basic

/-!
# From ℚ-mass prediction tables to `PMF` — ticket #286

Bridge between the epistemology thread's carrier (`Learning.lean` / #28's
prediction tables `hyp → List (ℚ × outcome)`) and mathlib's `PMF`: a finite
ℚ-table with nonnegative entries summing to `1` is a probability mass function
on the outcome type.

## References
* [Billingsley] P. Billingsley, *Probability and Measure*, Wiley 1995, ch. 1.
* mathlib pin v4.35.0-rc3: `PMF` (`ProbabilityMassFunction/Basic.lean`),
  `hasSum_fintype`.
-/

namespace BoringMath

open ENNReal

-- Reference: mathlib pin v4.35.0-rc3, `PMF` is `{f : α → ℝ≥0∞ // HasSum f 1}`;
-- `hasSum_fintype`; `Finset.sum_filter` / fiber sums.
/-- A **finite ℚ-mass table** (nonnegative entries summing to `1`) on a finite
outcome type is a `PMF`: the mass at `o` is the sum of the entries labelled `o`. -/
def PMF.ofRatTable {outcome : Type} [Fintype outcome] [DecidableEq outcome]
    (t : List (ℚ × outcome)) (hnn : ∀ p ∈ t, 0 ≤ p.1) (hsum : (t.map Prod.fst).sum = 1) :
    PMF outcome where
  val o := ((t.filter (fun p => p.2 = o)).map Prod.fst).sum
  property := by
    sorry -- TEMPORARY SORRY: HasSum over the Fintype via `hasSum_fintype` and the
    -- fiber decomposition of the sum over `t` (each entry counted once).

-- Reference: the definition, applied pointwise.
/-- The pointwise mass of `PMF.ofRatTable` at `o`. -/
theorem PMF.ofRatTable_apply {outcome : Type} [Fintype outcome] [DecidableEq outcome]
    (t : List (ℚ × outcome)) (hnn : ∀ p ∈ t, 0 ≤ p.1) (hsum : (t.map Prod.fst).sum = 1)
    (o : outcome) :
    PMF.ofRatTable t hnn hsum o
      = ((t.filter (fun p => p.2 = o)).map Prod.fst).sum := rfl

end BoringMath
