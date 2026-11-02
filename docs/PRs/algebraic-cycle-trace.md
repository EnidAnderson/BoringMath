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

## Update: boring restructure of `degree_pushforward` (urgent-class issue resolved)

The original proof carried `set_option maxHeartbeats 1000000` on
`degree_pushforward`: the fiber-sum re-indexing (`finsum_cond_eq_sum_of_cond_iff`
inside a `calc` step, `Finset.sum_fiberwise_of_maps_to` against the doubly
filtered shape) was elaborated inline, and the cumulative `isDefEq`/`whnf`
work blew the default 200000-heartbeat budget (confirmed: at the default
limit the proof times out at the `sum_fiberwise_of_maps_to` step).

Per the standing ruling (heartbeat/non-boring issues are urgent), the
proof is peeled into named, fully typed lemmas — `degree_eq_sum`,
`localDegree_pushforward`, `sum_localDegree_pushforward`,
`finsum_fiber_localDegree`, `sum_finsum_fiber_localDegree`,
`sum_fiberwise_filter`, `localDegree_eq_zero_of_not_mem_filter`,
`sum_filter_localDegree` — and the main theorem is a flat chain of
`Eq.trans` applications of those lemmas. The statement of
`degree_pushforward` is unchanged. It now elaborates at the default
heartbeat limit: `lake build BoringMath.AlgebraicGeometry.AlgebraicCycle.Trace`
succeeds warning-free in ~30s; `scripts/check-style.sh` 0 violations.
