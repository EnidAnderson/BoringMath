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
* `Scheme.image_genericPoints_of_isIso` — the generic points transport
  along isomorphisms: the image of the set of generic points is the set
  of generic points. The proof: the closure of the image of a point is
  the image of the closure (`Homeomorph.image_closure` — the base of an
  isomorphism is a homeomorphism via `Scheme.Hom.homeomorph`), the
  image of the closure is the preimage of the closure under the inverse
  homeomorphism, and the preimage of an irreducible component under the
  inverse is an irreducible component
  (`preimage_mem_irreducibleComponents_of_isPreirreducible_fiber`,
  whose fiber condition holds because the fibers of a homeomorphism are
  singletons).

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

## Addendum: the isomorphism transport

* `Scheme.fundamentalCycle_of_isIso` — **the fundamental cycle
  transports along isomorphisms**: the pushforward of the fundamental
  cycle along an isomorphism is the fundamental cycle of the target.
  The assembly: the pushforward distributes over the sum of the point
  cycles (`map_sum` via `pushforwardHom`); each point cycle pushes
  forward to the point cycle at the image with coefficient one (the
  point-cycle law `pushforward_single`, and the residue degree of an
  isomorphism, `residueDegree_of_isIso`); and the generic-point finsets
  correspond (the image of the source's finset is the target's, by
  `image_genericPoints_of_isIso`).
