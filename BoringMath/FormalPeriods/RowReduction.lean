/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringMath.FormalPeriods.RowReduction.RowOps
import BoringMath.FormalPeriods.RowReduction.PivotSearch
import BoringMath.FormalPeriods.RowReduction.Loop
import BoringMath.FormalPeriods.RowReduction.Predicates
import BoringMath.FormalPeriods.RowReduction.Invariant
import BoringMath.FormalPeriods.RowReduction.StepPivot
import BoringMath.FormalPeriods.RowReduction.Correctness
import BoringMath.FormalPeriods.RowReduction.Smoke

/-!
# Row reduction: Gaussian elimination over a discrete field

Ticket P.2.1 (leaf of P.2, issues #94/#108). An explicit, total
Gaussian-elimination procedure on matrices in `FreeMod` coordinates
(`FreeMatrix K m n = Fin m → Fin n → K`), producing the reduced
row-echelon normal form (RREF). Termination is by an explicit decreasing
measure (`colMeasure`): each recursive call consumes exactly one column,
so `n + 1` units of fuel suffice (`rrefAux` is structurally recursive on
the fuel). Correctness lemmas state that the output satisfies the
normal-form predicates (`IsRref`: zero rows at the bottom, pivot entries
`1`, strictly increasing pivot columns, pivot columns cleared elsewhere).

Everything on the core path is computable and choice-free (verified by
`#lint_axioms` at the end of this file), so the procedure is
`decide`-evaluable in the computational sense — the *term* computes —
demonstrated by `#eval` on a concrete 3×3 matrix over `ℚ`
(the `decide` *tactic* is banned by style; the computation itself is not).

Program context: this elimination layer supplies the decidability behind
the finite-dimensional quotient computations in Hörmann's formal-period
filtration (Def. 3.1, Remark 3.3).

Note on inversion: at the pin v4.35.0-rc3 the `⁻¹` instance path from
`Field K` (`CommGroupWithZero.toDivisionCommMonoid`) reaches
`Classical.choice` (verified by `#print axioms`), so the elimination takes
the inversion as explicit data: `invK : K → K` with its defining property
`hinv : ∀ a ≠ 0, invK a * a = 1` (computability discipline, STYLE §2.3).
For `K = ℚ` the smoke test uses `fun a => a⁻¹`.

## References
* R. Mines, F. Richman, W. Ruitenburg, *A Course in Constructive Algebra*,
  Springer Universitext, 2008, Pt. II Ch. 6 "Matrices and vector spaces"
  (and Pt. V Ch. 1 "Diagonalizing matrices") — constructive Gaussian
  elimination over discrete fields; TOC verified via SpringerLink.
* F. Hörmann, *A note on formal periods*, arXiv:2106.03803, Def. 3.1 and
  Remark 3.3 (verified against the arXiv HTML): `P^k(M)` is the quotient of
  `H_B(M) ⊗_ℚ H_dR(M)^∨` by the relations `∑ σᵢ ⊗ ωᵢ` coming from exact
  sequences `0 → N' → M^m → N → 0` with `m ≤ k`, and `P^k(M) = P^∞(M)` for
  `k = dim H_B(M)` — the stabilization this elimination layer computes.
-/
