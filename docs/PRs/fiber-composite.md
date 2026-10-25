# Candidate PR: the fiber of a composite

Ticket: BoringMath issue #16 (C.0 clause 3: the fiber of a composite —
the second scheme-level peel of the zero-cycle base-change
functoriality). Branch: `feat/fiber-composite`.
Module: `BoringMath/AlgebraicGeometry/Fiber/Composite.lean`
(owner directory: Mathlib's `AlgebraicGeometry/Fiber.lean` at the pin;
the composite API of the scheme-theoretic fiber; see
`docs/OWNERSHIP.md`).

## Statement

Given morphisms `f : X ⟶ Y`, `g : Y ⟶ Z` and a point `P : Z`:

* `AlgebraicGeometry.fiberComposite` — **the comparison map of the fiber
  of a composite**: `(f ≫ g).fiber P ⟶ g.fiber P`, the map induced by
  `f` (the lift into `g`'s fiber square of the legs of the composite's
  fiber square, `IsPullback.lift`).
* `AlgebraicGeometry.fiberComposite_fiberι` — the comparison map
  restricts `f` to the fibers
  (`μ ≫ g.fiberι P = (f ≫ g).fiberι P ≫ f`; `IsPullback.lift_snd`).
* `AlgebraicGeometry.fiberComposite_fiberToSpecResidueField` — the
  comparison map lies over the point (`IsPullback.lift_fst`).
* `AlgebraicGeometry.isPullback_fiberComposite` — **the fiber of a
  composite is the preimage of the fiber**: the square of the comparison
  map over `f` is a pullback square (paste-cancellation
  `IsPullback.of_right'`: the composite's fiber square pasted with `g`'s
  fiber square, both `IsPullback.of_hasPullback`).
* `AlgebraicGeometry.fiberCompositeIso` — the same as an isomorphism:
  `(f ≫ g).fiber P ≅ pullback f (g.fiberι P)`
  (`IsPullback.isoPullback`, up to `pullbackSymmetry`).

## Notes

* The fiber squares enter the paste in the flipped orientation
  (`IsPullback.flip`): the cancellation consumes the
  fiber-to-spectrum-residue-field legs as the horizontal ones.
* The cycle-level composite statement rides this iso: the fiber cycle of
  the composite at a point is the fiber cycle of the preimage, with the
  residue-degree bookkeeping of the fiber embeddings
  (`residueDegree_fiberι`, landed).

## Verification

* `lake build` clean (2729 jobs, zero warnings).
* `scripts/check-style.sh` zero violations, zero sorries.
