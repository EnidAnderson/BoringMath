/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.MeasureTheory.Measure.Basic
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.Data.Finset.Basic
import BoringMath.ProbabilityTheory.RatMass

/-!
# Measure-theoretic probability — ticket #558

The measure induced by a finite PMF as a sum of Dirac masses, bridging
`ProbabilityTheory/RatMass.lean` (#286, ℚ-mass tables ↔ PMF) to
`MeasureTheory` at the pin. Feeds the Hoeffding/Chernoff/PAC layer
#287–#289 and the LQG kinematical Hilbert space `L²(Ā, dμ_AL)` (#352).

## References
* [Kolmogorov 1933] A. N. Kolmogorov, *Grundbegriffe der
  Wahrscheinlichkeitsrechnung*, Springer 1933.
* [Billingsley] P. Billingsley, *Probability and Measure*, Wiley 1995, ch. 1.
* mathlib pin v4.35.0-rc3: `MeasureTheory.Measure`, `Measure.dirac`;
  BoringMath pin: `PMF.ofRatTable` (#286).
-/

namespace BoringMath

open MeasureTheory

-- Reference: [Billingsley], ch. 1, §3 (a discrete distribution is a
-- countable convex combination of Dirac masses).
-- NONCOMPUTABLE: measures at the pin are noncomputable (content-forced,
-- STYLE §2.3).
/-- The **measure induced by a finite PMF**: `∑ a, p a • δ_a`. -/
noncomputable def pmfToMeasure {α : Type*} [Fintype α] [MeasurableSpace α] [DecidableEq α]
    (p : α → ENNReal) : Measure α :=
  Finset.sum Finset.univ fun a => p a • Measure.dirac a

-- Reference: [Kolmogorov 1933], ch. I (total mass 1).
-- TEMPORARY SORRY with peeling plan.
-- PEELING PLAN (#558, feeds #287–#289): `Measure.sum_apply`/`dirac_apply`
-- reduce `pmfToMeasure p h Set.univ` to `∑ a, p a`, which is `1` by `h`;
-- measurability of `Set.univ` is `MeasurableSet.univ`.
/-- A finite PMF induces a **probability measure** (total mass 1). -/
theorem pmfToMeasure_univ {α : Type*} [Fintype α] [MeasurableSpace α] [DecidableEq α]
    (p : α → ENNReal) (h : Finset.sum Finset.univ p = 1) :
    pmfToMeasure p Set.univ = 1 := by
  sorry

end BoringMath
