# Candidate PR: row reduction (Gaussian elimination) over a discrete
# field (branch `pr/formal-periods-row-reduction`)

Ticket: P.2.1 (#108), leaf of P.2 (#94). Built on P.1.1 (`FreeMod`, landed).

## Statement

One new module `BoringMath/FormalPeriods/RowReduction.lean` (58 declarations):

* `FreeMatrix K m n` — abbrev for `Fin m → Fin n → K`, a matrix in `FreeMod`
  coordinates (array form of a map `FreeMod K n → FreeMod K m`).
* Elementary row operations as computable defs with pointwise peels:
  `matRowSwap` (+`_apply/_left/_right/_other/_diag`), `matRowScale`
  (+`_self/_other`), `matRowElim` (+`_self/_other`, `matRowElim_pivot_zero`),
  `rrefStep_pivot_one`.
* `findPivotRow` — explicit finite pivot search (structural recursion on
  fuel), with soundness/completeness specs `findPivotRow_some_spec`,
  `findPivotRow_none_spec`, `findPivotRow_eq_none_of`.
* `rrefAux` / `rref` — the total elimination loop, structurally recursive on
  fuel `n+1`; termination measure `colMeasure n j = n - j` with
  `colMeasure_step` (`Nat.sub_succ_lt_self`): each recursive call consumes
  exactly one column, so `n+1` units of fuel suffice. No well-founded
  shortcut, no choice.
* Normal-form predicates: `matRowZero`, `matLeadingCol`, `IsRref` (zero rows
  at the bottom, pivot entries `1`, strictly increasing pivot columns, pivot
  columns cleared in all other rows), and the loop invariant `RrefState`.
* Correctness peels: `rrefState_zero`, `rrefState_isRref_of_done`,
  `rrefState_step_none`, `rrefState_step_pivot` (both proved; the pivot step
  via the search/leading-column peels `findPivotRow_eq_some_of_first`,
  `findPivotRow_congr_before`, `matLeadingCol_eq_some/_eq_none/_some_of_lt/
  _eq_of_agree_before/_eq_of_zero_before` and the pointwise peels
  `rrefStep_swap_scale_self`, `rrefStepMat_pivot_row_before/_pivot_row_at/
  off_pivot_before`), `rrefAux_state` (the invariant induction),
  `rref_isRref : IsRref (rref invK A)`.
* Smoke test: `smokeMat` (3×3 over `ℚ`) with `#eval` displays — input
  `[[2,4,6],[1,3,5],[0,1,4]]`, output (RREF) `[[1,0,0],[0,1,0],[0,0,1]]`.

Note on inversion: at the pin v4.35.0-rc3 the `⁻¹` instance path from
`Field K` (`CommGroupWithZero.toDivisionCommMonoid`) reaches
`Classical.choice` (verified by `#print axioms`), so the algorithm takes the
inversion as explicit data `invK : K → K` with `hinv : ∀ a ≠ 0, invK a * a = 1`
(STYLE §2.3, explicit data over instance-chosen data). For `K = ℚ` the smoke
test passes `fun a => a⁻¹`.

## Literature

* R. Mines, F. Richman, W. Ruitenburg, *A Course in Constructive Algebra*,
  Springer Universitext, 2008, Pt. II Ch. 6 "Matrices and vector spaces" (and
  Pt. V Ch. 1 "Diagonalizing matrices") — constructive Gaussian elimination
  over discrete fields (the Richman/Bridges prior-art line named in #94).
  TOC verified via SpringerLink and a library catalogue record. No
  `REVIEW(citation)` tag.
* F. Hörmann, *A note on formal periods*, arXiv:2106.03803, Def. 3.1 and
  Remark 3.3 — verified against the arXiv HTML: `P^k(M)` is the quotient of
  `H_B(M) ⊗_ℚ H_dR(M)^∨` by the relations `∑ σᵢ ⊗ ωᵢ` from exact sequences
  `0 → N' → M^m → N → 0` with `m ≤ k`, and `P^k(M) = P^∞(M)` for
  `k = dim H_B(M)`. Program context for this elimination layer (the
  decidability supply behind the finite-dimensional quotient computations).
* S. Axler, *Linear Algebra Done Right*, 4th ed., Ch. 1 (used in FreeMod;
  field/vector axioms behind the row operations).

## Where it would live in Mathlib

`Mathlib/LinearAlgebra/Matrix/Echelon/` — alongside `Matrix.IsRowEchelon`
(`Mathlib/LinearAlgebra/Matrix/Echelon/Basic.lean`).

## Does Mathlib already have it?

At the pin, Mathlib has the *predicate* `Matrix.IsRowEchelon` and pivot
machinery (`Echelon/Pivot.lean`), but no RREF-producing Gaussian-elimination
algorithm over a general discrete field (no `rref`/Gaussian in
`Mathlib/LinearAlgebra/Matrix/`), and its echelon API is stated over general
`LT`/`R`-matrices, not over a discrete field with decidable pivot search. Ours
is the constructive algorithm on `Fin m → Fin n → K` with an explicit fuel,
an explicit decreasing measure, lint-CLEAN decidability, and a `#eval`-able
smoke test. `Fintype.decidablePiFintype` is choice-tainted at the pin (see the
P.1.1 pin-run), so all decidability here is built directly (`if … then …`
on `Nat.decLt`, `DecidableEq K`, `Bool` tests) — no `Decidable` instance over
`Fin` is used.

## Verification (machine-checked at the pin, v4.35.0-rc3)

* `lake build BoringMath.FormalPeriods.RowReduction` — succeeds,
  warning-clean (no `sorry` anywhere in the module).
* `bash scripts/check-style.sh BoringMath/FormalPeriods/RowReduction.lean` —
  **0 violations**, 0 sorries.
* `#lint_axioms` on all 58 declarations (printed at the end of the module):
  **58 CLEAN** (`[propext, Quot.sound]`, `[propext]`, or no axioms);
  **0 `sorryTainted`, 0 `choiceTainted`, 0 `banned`** — no `sorryAx`, no
  `Classical.choice` anywhere, including `rrefState_step_pivot`,
  `rrefAux_state`, `rref_isRref`.
* `#eval matToLists smokeMat` → `[[2, 4, 6], [1, 3, 5], [0, 1, 4]]`;
  `#eval matToLists (rref (K := ℚ) (fun a => a⁻¹) smokeMat)` →
  `[[1, 0, 0], [0, 1, 0], [0, 0, 1]]`. (`decide`-evaluable in the
  computational sense: the term computes. The `decide` *tactic* is banned by
  style; a kernel `rfl` cannot fire on `ℚ` arithmetic only because Lean core
  marks `Rat.mul`/`Rat.inv` `@[irreducible]`, which is unrelated to this
  module — `#eval` demonstrates the computation.)

## Closed: `rrefState_step_pivot` (peeling record)

The single sorry is closed; the module is sorry-free. The inline peeling
plan was implemented as named lemmas, all proved honestly:

* `findPivotRow_eq_some_of_first` — if the predicate holds at `i` and fails
  at every earlier row of the searched range, the search returns `i`.
* `findPivotRow_congr_before` — if `p`, `q` agree on the searched rows below
  `b` and the search for `p` hits `i < b` within its fuel, the search for `q`
  hits the same `i` (the search only reads the prefix it examines).
* `matLeadingCol_eq_some` / `matLeadingCol_eq_none` / `matLeadingCol_some_of_lt`
  — definitional peels of `matLeadingCol` at `some`/`none`, and extraction
  of the found column from a leading column below `j ≤ n`.
* `matLeadingCol_eq_of_agree_before` — `A`, `B` agreeing on row `a` at all
  columns `< j`, with `matLeadingCol A a < j ≤ n`, have the same leading
  column there (via `findPivotRow_congr_before`).
* `matLeadingCol_eq_of_zero_before` — a row vanishing before `j < n` and
  nonzero at `j` has leading column exactly `j` (via
  `findPivotRow_eq_some_of_first`).
* `rrefStep_swap_scale_self`, `rrefStepMat_pivot_row_before`,
  `rrefStepMat_pivot_row_at`, `rrefStepMat_off_pivot_before` — pointwise
  peels of the composed step `A3 = matRowElim (matRowScale (matRowSwap A r'
  i) r' (invK (A i c))) r' c`: the pivot row vanishes before `c` and is `1`
  at `c` (`rrefStep_pivot_one`), column `c` is cleared off row `r'`
  (`matRowElim_pivot_zero`), and every other row agrees with `A` on all
  columns `< j`.

`rrefState_step_pivot` then verifies the six `RrefState` components at
`(r+1, j+1)` directly: rows `≥ r+1` vanish on columns `< j+1` (agreement +
`RrefState.1`, and the cleared pivot column), old pivot rows keep their
leading column and their `1` (`matLeadingCol_eq_of_agree_before` +
agreement), the new pivot row `r'` has leading column `j`
(`matLeadingCol_eq_of_zero_before`), and pivot columns strictly increase and
are cleared in all other rows.

## Review notes

Human reviewer's decision pending. Open questions for the reviewer:
(1) Is taking `invK`/`hinv` as explicit data acceptable, given the pin's
choice-tainted `⁻¹` instance path, or should the module wait for a mathlib
fix of `CommGroupWithZero.toDivisionCommMonoid`? (2) Is `IsRref`'s four-clause
formulation the right normal-form predicate, or should it mirror
`Matrix.IsRowEchelon` extended by a "reduced" clause?
