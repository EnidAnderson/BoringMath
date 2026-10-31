# Candidate PR: row reduction (Gaussian elimination) over a discrete
# field (branch `pr/formal-periods-row-reduction`)

Ticket: P.2.1 (#108), leaf of P.2 (#94). Built on P.1.1 (`FreeMod`, landed).

## Statement

One new module `BoringMath/FormalPeriods/RowReduction.lean` (47 declarations):

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
  `rrefState_step_none` (proved), `rrefState_step_pivot` (sorry, see below),
  `rrefAux_state` (the invariant induction, proved modulo the step lemma),
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

* `lake build BoringMath.FormalPeriods.RowReduction` — succeeds; the only
  warning is the single deliberate `declaration uses 'sorry'`
  (`rrefState_step_pivot`).
* `bash scripts/check-style.sh BoringMath/FormalPeriods/RowReduction.lean` —
  **0 violations**, 1 sorry (informational).
* `#lint_axioms` on all 47 declarations (printed at the end of the module):
  **44 CLEAN** (`[propext, Quot.sound]` or no axioms); 3 `sorryTainted`
  (`rrefState_step_pivot`, and `rrefAux_state` / `rref_isRref` which use it);
  **0 `choiceTainted`, 0 `banned`** — no `Classical.choice`, no `sorryAx` on
  the algorithm core.
* `#eval matToLists smokeMat` → `[[2, 4, 6], [1, 3, 5], [0, 1, 4]]`;
  `#eval matToLists (rref (K := ℚ) (fun a => a⁻¹) smokeMat)` →
  `[[1, 0, 0], [0, 1, 0], [0, 0, 1]]`. (`decide`-evaluable in the
  computational sense: the term computes. The `decide` *tactic* is banned by
  style; a kernel `rfl` cannot fire on `ℚ` arithmetic only because Lean core
  marks `Rat.mul`/`Rat.inv` `@[irreducible]`, which is unrelated to this
  module — `#eval` demonstrates the computation.)

## Remaining sorry and peeling plan

`rrefState_step_pivot` (one sorry): one pivot step preserves `RrefState`.
Plan recorded inline: with `A3 = matRowElim (matRowScale (matRowSwap A r' i)
r' (invK (A i c))) r' c`, use `rrefStep_pivot_one` (`A2 r' c = 1`),
`matRowElim_pivot_zero` (column `c` cleared off row `r'`), and for columns
`c' < j` the fact that `A2 r' c' = 0` (row `i` vanished before `j` by
`RrefState.1`), so `A3` agrees with `A` on all columns `< j` off row `r'`;
this needs a "leading column is determined by a prefix" lemma
(`matLeadingCol` congruence via `findPivotRow` specs) to transport components
2–6 of `RrefState` from `A` to `A3`, plus the new pivot row `r'` having
leading column `j`. Next peels: `findPivotRow_congr_before` (searches agree
when predicates agree on the searched range) and
`matLeadingCol_eq_of_agree_before`.

## Review notes

Human reviewer's decision pending. Open questions for the reviewer:
(1) Is taking `invK`/`hinv` as explicit data acceptable, given the pin's
choice-tainted `⁻¹` instance path, or should the module wait for a mathlib
fix of `CommGroupWithZero.toDivisionCommMonoid`? (2) Is `IsRref`'s four-clause
formulation the right normal-form predicate, or should it mirror
`Matrix.IsRowEchelon` extended by a "reduced" clause?
