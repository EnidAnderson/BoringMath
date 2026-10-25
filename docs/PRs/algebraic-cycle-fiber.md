# Candidate PR: the fiber cycle — the flat pullback of a point (C.0)

Ticket: BoringMath issue #16 (TREE C.0, clause 3: the flat pullback —
the pullback of a point cycle). Branch: `feat/algebraic-cycle-fiber`.
Module: `BoringMath/AlgebraicGeometry/AlgebraicCycle/FiberCycle.lean`
(owner directory: Mathlib's `AlgebraicGeometry/AlgebraicCycle/`,
mirroring `Basic.lean` at the pin; the substrate is
`Mathlib/AlgebraicGeometry/Fiber.lean`'s scheme-theoretic fiber).

## Statement

* `AlgebraicCycle.fiberCycle f P` — **the fiber cycle** of a morphism
  at a point: the fundamental cycle of the scheme-theoretic fiber
  `f.fiber P = pullback f (Y.fromSpecResidueField P)`, pushed forward
  along the fiber embedding `fiberι`. For a flat morphism this is the
  flat pullback of the point cycle, with multiplicity one — the reduced
  case. Noncomputable: the fiber's generic points are chosen and the
  fiber sums are enumerated by choice.
* `support_fiberCycle` — the support is contained in the image of the
  generic points of the fiber (the pushforward support law).
* `isFinite_fiberCycle` — the fiber cycle of a Noetherian fiber has
  finite support.
* `support_fiberCycle_subset_preimage` — **the fiber cycle is supported
  on the set-theoretic fiber**: every point of the support maps to the
  given point (the fiber factorization law `fiber_fac`, the
  constancy of `fiberToSpecResidueField`, and the constancy of
  `fromSpecResidueField`).

## Findings recorded

* Multiplicity one is the reduced case: the general flat pullback
  carries the local lengths of the fiber (Serre's intersection
  multiplicities) — the named extension, shared with the intersection
  machinery of C.2 (#24).
* The fiber's Noetherianity is an explicit hypothesis; it also supplies
  the fiber embedding's quasicompactness by instance (morphisms from a
  Noetherian scheme are quasicompact).
* The base-change functoriality for zero-cycles (the ticket's second
  minimal clause) is the next peel: the fiber of a composite and the
  fiber of a base change — GOLD reads of `Mathlib/AlgebraicGeometry/
  Fiber.lean`'s `isPullback_fiberToSpecResidueField_of_isPullback` and
  the pullback-associativity API.

## Literature

* W. Fulton, *Intersection Theory*, ch. 1 (the flat pullback of a
  cycle: for a flat morphism, the pullback of a point is the
  fundamental cycle of the fiber). REVIEW(citation): exact section to
  be pinned by the human referee.
* Stacks Project, tag 02R4 (the flat pullback of cycles).
  REVIEW(citation): exact tag to be pinned.
