/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringMath.FormalPeriods.DecidableSubspace.Sums
import BoringMath.FormalPeriods.DecidableSubspace.RowSpan
import BoringMath.FormalPeriods.DecidableSubspace.Pivots
import BoringMath.FormalPeriods.DecidableSubspace.Rank
import BoringMath.FormalPeriods.DecidableSubspace.RowOps
import BoringMath.FormalPeriods.DecidableSubspace.RrefProps
import BoringMath.FormalPeriods.DecidableSubspace.Residual
import BoringMath.FormalPeriods.DecidableSubspace.Uniqueness
import BoringMath.FormalPeriods.DecidableSubspace.Decide
/-!
# Decidable subspace membership, equality, and containment (P.2.3)
Ticket P.2.3 (leaf of P.2, issue #110), built on the landed P.2.1 RREF
(`BoringMath.FormalPeriods.RowReduction`). A subspace of `FreeMod K n` is
given by an explicit spanning set, i.e. a matrix `A : FreeMatrix K m n`
whose rows span it (`inRowSpan A v`: an explicit linear combination of the
rows, pointwise in the coordinates). All decisions are computable functions
returning `Bool`, with explicit `Decidable` instances and correctness
lemmas:
* membership `v ∈ span(rows A)` is decided by the rank comparison
  `rankOf (matSnoc A v) = rankOf A` (`memRowSpanBool`), where `rankOf` is the
  number of nonzero rows of the RREF computed by P.2.1 — `v ∈ span S` iff
  `rank(S ∪ {v}) = rank S`;
* containment `span B ⊆ span A` is decided row by row (`spanContainsBool`);
* equality of spans is decided by mutual containment (`spanEqBool`);
* for a subspace given directly by its RREF normal form, membership is
  decided by the residual against the pivot rows (`rrefResidualBool`).
Correctness rests on two constructive facts proved here: row operations and
the whole elimination loop preserve the row span (`inRowSpan_rref`), and the
RREF of a matrix is unique among RREF matrices with the same row span
(`rref_eq_of_span_eq`, and the one-sided refinement
`rref_eq_of_subset_nzCount`), from which the rank criterion follows. No
`Classical.choice`, no `sorry`: every declaration lints CLEAN (see the
`#lint_axioms` block at the end of the file).
Program context: this is the decidability supply behind the finite-dimensional
quotient computations in Hörmann's formal-period filtration.
## References
* R. Mines, F. Richman, W. Ruitenburg, *A Course in Constructive Algebra*,
  Springer Universitext, 1988, eBook DOI 10.1007/978-1-4419-8640-5, Pt. II
  Ch. 6 "Matrices and vector spaces" (row spaces, rank, Gaussian elimination
  over discrete fields; DOI and TOC verified via web) — the rank criterion
  `v ∈ span S ↔ rank(S ∪ {v}) = rank S` and the uniqueness of the reduced
  row-echelon form.
* F. Hörmann, *A note on formal periods*, arXiv:2106.03803, Def. 3.1 and
  Remark 3.3 (verified against the arXiv source): `P^k(M) = P^∞(M)` for
  `k = dim H_B(M)` — the stabilization this decidability layer computes.
* S. Axler, *Linear Algebra Done Right*, 4th ed., Ch. 1 (span as the set of
  linear combinations).
-/
