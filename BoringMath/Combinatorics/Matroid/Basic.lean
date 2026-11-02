/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Combinatorics.Matroid.Basic
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Card

/-!
# Matroid theory — ticket #556

The Tutte polynomial as a computable rank sum on top of pin's `Matroid`
(with the `ℕ∞`-valued rank `eRk`). Sits next to `Combinatorics/Graph`
(cycle matroids) and feeds the species-of-matroids row #299.

## References
* [Oxley] J. G. Oxley, *Matroid Theory*, 2nd ed., Oxford 2011, ch. 3–4.
* [Tutte 1967]; mathlib pin v4.35.0-rc3: `Combinatorics/Matroid/*` (`eRk`);
  MISSING: Tutte polynomial, representability criteria.
-/

namespace BoringMath

-- Reference: [Oxley], ch. 4.1 (the Tutte polynomial
-- `T_M(x,y) = Σ_{A ⊆ E} (x-1)^{r(E)-r(A)} (y-1)^{|A|-r(A)}`), evaluated at
-- integer points as a plain `ℤ` (computable data).
-- NONCOMPUTABLE: `Matroid.eRk` is noncomputable at the pin (content-forced,
-- STYLE §2.3).
/-- The **Tutte polynomial evaluated at `(x, y)`** via the rank-sum formula. -/
noncomputable def tutteEval {E : Type*} [Fintype E] [DecidableEq E] (M : Matroid E)
    (x y : ℤ) : ℤ :=
  Finset.sum (Finset.univ : Finset E).powerset fun A =>
    (x - 1) ^ ((M.eRk (Set.univ : Set E)).toNat - (M.eRk (↑A : Set E)).toNat) *
    (y - 1) ^ (A.card - (M.eRk (↑A : Set E)).toNat)

-- Reference: [Oxley], ch. 4.1 (special value `T_M(1,1)` = number of bases).
-- TEMPORARY SORRY with peeling plan.
-- PEELING PLAN (#556): (i) `T(1,1)` kills every summand except `A` with
-- `r(E) - r(A) = 0` and `|A| - r(A) = 0`, i.e. `A` a base; (ii) count bases
-- as `(Finset.univ.powerset.filter fun B => M.IsBase (B : Set E)).card`.
/-- **Tutte specialization `T(1,1)` counts the bases**. -/
theorem tutteEval_one_one {E : Type*} [Fintype E] [DecidableEq E] (M : Matroid E) :
    tutteEval M 1 1 = (Set.ncard {B : Set E | M.IsBase B} : ℤ) := by
  sorry

end BoringMath
