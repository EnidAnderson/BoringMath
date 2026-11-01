/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringMath.FormalPeriods.ChainStab.Rank
import BoringMath.FormalPeriods.ChainStab.Chain

/-!
# Chain stabilization of row spans (P.2.4)

Ticket P.2.4 (leaf of P.2, issue #111), built on the landed P.2.3 decidable
subspace layer (`BoringMath.FormalPeriods.DecidableSubspace`). The Remark 3.3
engine, isolated and stated abstractly over an indexed family so P.9 can
apply it directly: an ascending chain of row spans of matrices over
`FreeMod K n` reaches a fixed point — a step that changes nothing — at depth
`≤ n`, with the bound computed, not assumed. Concretely, for
`A : ℕ → FreeMatrix K m n` with `span (A i) ⊆ span (A (i+1))` at every step,
there is `k ≤ n` with `span (A k) = span (A (k+1))`: among the first `n + 2`
spans of the `n`-dimensional `FreeMod K n`, two consecutive ranks agree
(finite pigeonhole on the computed ranks, each `≤ n` by `rankOf_le`), and
equal rank plus inclusion forces equal spans
(`spanEq_of_contains_and_rankOf_eq`). This is the finite-dimensional engine
behind the stabilization of the successive quotients of the same space.

The peels: `rankOf_le` (the computed rank is bounded by the number of
columns, via the pivot columns of the RREF — the `matLeadingCol` machinery),
`rankOf_mono_of_spanContains` (containment of spans gives rank monotonicity,
via the pivot-column membership `exists_matLeadingCol_eq_vecLeadingCol`),
`rankOf_lt_of_proper_contains` (proper containment strictly increases the
rank), `spanEq_of_contains_and_rankOf_eq` (containment plus equal computed
rank gives equality of spans), and the main theorem `span_chain_stabilizes`.
A toy chain over `ℚ` of dimension 2 with three relation steps evaluates by
`#eval` to its fixed point at depth 2 = dim. No `Classical.choice`, no
`sorry`: every declaration lints CLEAN (see the `#lint_axioms` block at the
end of the file).

## References
* F. Hörmann, *A note on formal periods*, arXiv:2106.03803, Def. 3.1 remark
  and Remark 3.3 (verified against the arXiv HTML): `P^k(M) = P^{k+1}(M) = ⋯
  = P^∞(M)` for `k = dim H_B(M)` — `P^k(M)` is the quotient of the
  finite-dimensional `H_B(M) ⊗_ℚ H_dR(M)^∨` by the relations of length
  `≤ k`, so the successive quotients of the same finite-dimensional space
  stabilize; this module is the abstract linear-algebra engine.
* R. Mines, F. Richman, W. Ruitenburg, *A Course in Constructive Algebra*,
  Springer Universitext, 1988, eBook DOI 10.1007/978-1-4419-8640-5, Pt. II
  Ch. 6 "Matrices and vector spaces" (DOI and TOC verified via web): rank =
  number of nonzero rows of the RREF, bounded by the number of columns
  (distinct pivot columns); a chain of subspaces of an `n`-dimensional
  space has a constant step among its first `n + 2` terms (finite
  pigeonhole on the dimensions) — the dimension bound.
-/
