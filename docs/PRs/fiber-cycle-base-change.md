# Candidate PR: the fiber cycle under base change

Ticket: BoringMath issue #16 (C.0 clause 3: the flat base-change
functoriality for zero-cycles — the first cycle-level law, the support
compatibility). Branch: `feat/fiber-cycle-base-change`.
Module: `BoringMath/AlgebraicGeometry/AlgebraicCycle/FiberBaseChange.lean`
(owner directory: the fiber-cycle layer of `BoringMath/AlgebraicGeometry/
AlgebraicCycle/`; consumers ride the base-change square of
`BoringMath/AlgebraicGeometry/Fiber/BaseChange.lean`; see
`docs/OWNERSHIP.md`).

## Statement

Given a cartesian square `IsPullback fst snd f g` (with `fst : P ⟶ X`,
`snd : P ⟶ Y`, `f : X ⟶ Z`, `g : Y ⟶ Z`) and a point `y : Y`:

* `AlgebraicCycle.support_fiberCycle_baseChange` — **the fiber cycle of a
  base change is supported on the preimage of the fiber**: the support of
  the fiber cycle of the vertical morphism at `y` maps under the
  cartesian map into the set-theoretic fiber of the given morphism at
  the image point:
  `(fiberCycle snd y).support ⊆ fst.base ⁻¹' (Set.range (f.fiberι (g y)).base)`.
  Every support point is the image of a generic point of the fiber; the
  base-change map of the fibers carries the fiber embedding over the
  cartesian map (`fiberBaseChange_fiberι`), so the image lies in the
  range of the embedding of the image fiber.

## Notes

* The multiplicity-level functoriality (the coefficients of the fiber
  cycle of a base change against the fundamental cycle of the base-changed
  fiber) needs the generic-point transfer along the base-change map of
  the fibers: the base change is by a field extension
  (`SpecMap_residueFieldMap_fromSpecResidueField`), so the base-change map
  is flat and surjective, and the images of the generic points of the
  base-changed fiber are generic points of the fiber. The named next peels:
  the flatness and surjectivity of the base-change map, then the
  generic-point transfer, then the coefficient formula.

## Verification

* `lake build` clean (2730 jobs, zero warnings).
* `scripts/check-style.sh` zero violations, zero sorries.
