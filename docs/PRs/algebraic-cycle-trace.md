# Candidate PR: the trace formula for zero-cycles (C.0)

Ticket: BoringMath issue #16 (C.0 remaining scope: the trace formula).
Branch: `feat/algebraic-cycle-trace`.
Module: `BoringMath/AlgebraicGeometry/AlgebraicCycle/Trace.lean` (owner
directory: Mathlib's `AlgebraicGeometry/AlgebraicCycle/`, mirroring
`Basic.lean` at the pin; see `docs/OWNERSHIP.md`).

## Statement

* `AlgebraicCycle.localDegree_comp` — **the local degree along a
  composite**: on the fiber over `z`, the multiplicity weighted by the
  residue degree over `g` and by the residue degree of `z` over `h` is
  the local degree along the composite — the tower law at the point
  (via `Scheme.Hom.residueDegree_comp`, `Nat.cast_mul`, and the
  commutativity and associativity of multiplication).
* `AlgebraicCycle.degree_pushforward` — **the trace formula**: the
  degree of the pushforward of a zero-cycle along `h` is the degree of
  the cycle along the composite `g ≫ h`,
  `degree h (g_* D) = degree (g ≫ h) D`,
  where `t` contains the image of the support of `D` and `s` contains
  the support of `D`. The containing-set witness on the left is derived
  from the support law for the pushforward.

The proof re-indexes the fiber sums of the pushforward onto the
containing set `s`: each fiber finsum is reduced to a finite sum over
the fiber's intersection with `s` (`finsum_cond_eq_sum_of_cond_iff`,
the summand vanishing off the support), the fibers over `t` are
assembled by `Finset.sum_fiberwise_of_maps_to`, and the extension from
the filtered set to `s` vanishes off the image of the support. All
substitution steps are named-lemma transports (`finsum_mem_mul`,
`finsum_mem_congr`).

## Verification

`lake build`: success, zero warnings. `scripts/check-style.sh`: 0
violations, 0 sorries.

## Literature

* W. Fulton, *Intersection Theory*, ch. 1 (the pushforward of
  zero-cycles and the degree: the degree of a pushforward is the degree
  along the composite). REVIEW(citation): exact section to be pinned by
  the human referee.
* S. Lang, *Algebra*, revised 3rd ed., Springer, 2002 (the tower law
  for the degrees of field extensions). REVIEW(citation): exact section
  to be pinned.
