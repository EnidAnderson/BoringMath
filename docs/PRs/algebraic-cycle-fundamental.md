# Candidate PR: the fundamental cycle of a Noetherian scheme (C.1/C.0 gate)

Ticket: BoringMath issues #10 (TREE C.1 prep) and #16 (TREE C.0: the
flat pullback's gate). Branch: `feat/algebraic-cycle-fundamental`.
Module: `BoringMath/AlgebraicGeometry/AlgebraicCycle/FundamentalCycle.lean`
(owner directory: Mathlib's `AlgebraicGeometry/AlgebraicCycle/`,
mirroring `Basic.lean` at the pin; see `docs/OWNERSHIP.md`).

## Statement

* `Scheme.genericPointsFinset` — the generic points of a Noetherian
  scheme, as a finite set (a Noetherian scheme has finitely many
  irreducible components, stacks 0BA8, and the components of a sober
  space biject with their generic points).
* `Scheme.fundamentalCycle` — the **fundamental cycle** of a Noetherian
  scheme: the formal sum of its irreducible components, each with
  multiplicity one — the sum of the point cycles at the generic points.
  Noncomputable: the generic points are chosen and the point cycles are
  enumerated by choice.
* `Scheme.fundamentalCycle_apply` — the coefficient is one at each
  generic point and zero elsewhere (the evaluation chain:
  `locallyFinsuppWithin.coe_sum`, `Finset.sum_apply`,
  `single_apply`, `Finset.sum_ite_eq`).
* `Scheme.support_fundamentalCycle` — the support is exactly the set of
  generic points.
* `Scheme.isFinite_fundamentalCycle` — the fundamental cycle has finite
  support.

## Unblocking

This retires the shared gate recorded on #10 and #16: the cycle [Γ_f]
of a graph correspondence is the pushforward of the fundamental cycle
along the graph immersion, and the flat pullback of a point cycle
`f*[P]` is the fundamental cycle of the scheme-theoretic fiber
`f.fiber P`. Multiplicity-one is the reduced case; the
geometric-multiplicity version (local lengths of the fiber) remains a
named extension for the flat pullback's general form.

## Literature

* W. Fulton, *Intersection Theory*, ch. 1 (the cycle of a variety: the
  sum of its irreducible components, each with multiplicity one for a
  reduced scheme). REVIEW(citation): exact section to be pinned by the
  human referee.
* Stacks Project, tag 0BA8 (a Noetherian scheme has finitely many
  irreducible components).
