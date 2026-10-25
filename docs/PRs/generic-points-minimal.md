# Candidate PR: specializations of generic points

Ticket: BoringMath issue #16 (C.0 clause 3: the generic-point transfer
along the base-change map of the fibers — the topological core of peel 2
of the multiplicity-level arc). Branch: `feat/generic-points-minimal`.
Module: `BoringMath/Topology/Sober/GenericPoints.lean`
(owner directory: Mathlib's `Topology/Sober.lean` at the pin, where
`IsGenericPoint` and `genericPoints` live; see `docs/OWNERSHIP.md`).

## Statement

* `eq_of_specializes_of_mem_genericPoints` — **a specialization of a
  generic point is that generic point**: in a T₀ space, if `η` is a
  generic point of an irreducible component and `ρ ⤳ η`, then `ρ = η`.
  The generic points are minimal for specialization.

  The closure of the generic point is an irreducible component, maximal
  among the irreducible sets (`Maximal.eq_of_subset`); the closure of
  the specializing point is an irreducible set containing it
  (`isIrreducible_singleton.closure`,
  `exists_mem_irreducibleComponents_subset_of_isIrreducible`), so the
  two closures agree, and a T₀ space has at most one generic point of a
  set (`IsGenericPoint.eq`).

## Notes

* The consumer is the generic-point transfer for the base-change map of
  the fibers: a flat surjective morphism lifts specializations, and the
  lifted specialization into a generic point is the generic point, so
  the image of a generic point under the base-change map is a generic
  point of an irreducible component of the target fiber. The missing
  scheme-level input (flat morphisms lift specializations, the affine
  gluing of `RingHom.Flat.generalizingMap_comap`) is the next named
  peel.

## Verification

* `lake build` clean (2740 jobs, zero warnings).
* `scripts/check-style.sh` zero violations, zero sorries.
