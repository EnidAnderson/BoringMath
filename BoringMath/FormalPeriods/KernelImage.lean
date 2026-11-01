/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringMath.FormalPeriods.KernelImage.Basic
import BoringMath.FormalPeriods.KernelImage.Pivots
import BoringMath.FormalPeriods.KernelImage.ListSum
import BoringMath.FormalPeriods.KernelImage.MatVec
import BoringMath.FormalPeriods.KernelImage.RowSwap
import BoringMath.FormalPeriods.KernelImage.RowScale
import BoringMath.FormalPeriods.KernelImage.RowElim
import BoringMath.FormalPeriods.KernelImage.ElimLoop

/-!
# Kernel and image of a `FreeModHom` as explicit computable data

Ticket P.2.2 (leaf of P.2, issue #109), built on the landed RREF
(`RowReduction.lean`, P.2.1). For a morphism `f : FreeModHom K m n` with
matrix `A = freeModHomMat f` (column `j` is `f` of the `j`-th standard basis
vector), let `R = rref invK A` be its reduced row-echelon normal form. Then,
as *data*:

* the **kernel basis** `kernelBasis R` — one vector `kernelVec R c` for each
  non-pivot column `c` of `R` (entry `1` at `c`, entry `-R a c` at the pivot
  column of row `a`);
* the **image basis** `imageBasis A R` — the pivot columns of the original
  matrix `A` (row reduction preserves column relations, so the pivot columns
  of `A` span the image);
* the **rank** `rankOf R` = number of pivot columns and the **nullity**
  `nullityOf R` = number of non-pivot columns, with the computation-level
  rank–nullity identity `rankOf R + nullityOf R = m`.

Correctness: `f x = 0` iff `x` is an explicit linear combination of
`kernelBasis R` (kernel membership iff annihilation), and `y` is in the image
of `f` iff `y` is an explicit linear combination of `imageBasis A R`.

All sums are `List.sum` over `List.finRange` — the mathlib `Finset`
big-operator API (`Finset.sum_insert`, `Finset.induction_on`,
`Finset.sum_ite_eq`, …) is `Classical.choice`-tainted at the pin v4.35.0-rc3
(probed with `#print axioms`), so the sum toolbox here is built directly on
`List` induction, which lints CLEAN.

## References
* R. Mines, F. Richman, W. Ruitenburg, *A Course in Constructive Algebra*,
  Springer Universitext, 1988, DOI 10.1007/978-1-4419-8640-5, Pt. II Ch. 6
  "Matrices and vector spaces" — kernel/image from the row-reduced form of
  a matrix over a discrete field (book and DOI verified via SpringerLink).
* F. Hörmann, *A note on formal periods*, arXiv:2106.03803, Def. 3.1 and
  Remark 3.3 (verified against the arXiv HTML): the finite-dimensional
  quotient computations `P^k(M) = P^∞(M)` for `k = dim H_B(M)` that this
  elimination layer supplies the decidability for.
-/

