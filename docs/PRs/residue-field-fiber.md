# Candidate PR: the residue fields of the scheme-theoretic fiber

Ticket: BoringMath issue #16 (C.0 clause 3: the residue-degree-one peel for
the base-change functoriality of zero-cycles — the fiber application).
Branch: `feat/residue-field-fiber`.
Module: `BoringMath/AlgebraicGeometry/ResidueField/Fiber.lean`
(owner directory: Mathlib's `AlgebraicGeometry/Fiber.lean` at the pin;
the residue field API of the scheme-theoretic fiber; see
`docs/OWNERSHIP.md`).

## Statement

* `Scheme.Hom.residueDegree_fiberι` — **the residue degree of the fiber
  embedding is one**: at the point of the scheme-theoretic fiber over a
  point of the ambient scheme, `(f.fiberι (f x)).residueDegree
  (f.asFiber x) = 1`. The fiber square factors the canonical map from
  the spectrum of the residue field through the fiber embedding
  (`asFiberHom_fiberι`); the tower law (`residueDegree_comp`, landed in
  the tower module) identifies the degrees along the factorization, and
  both factors are preimmersions (`residueDegree_of_isPreimmersion`,
  landed in the preimmersion module): the canonical map from the spectrum
  of the residue field, and the canonical map of a point into its fiber.

## Notes

* The rewrite of the composite along `asFiberHom_fiberι` is performed by
  `Eq.subst` with the motive's binder type given explicitly
  (`fun g : Spec (X.residueField x) ⟶ X => ...`); leaving the binder
  type to inference does not terminate in the elaborator's normalization.
* The closed point of `Spec (X.residueField x)` is the unique point of
  the one-point spectrum (`IsLocalRing.closedPoint`; the residue field
  of a point is a field).

## Verification

* `lake build` clean (2727 jobs, zero warnings).
* `scripts/check-style.sh` zero violations, zero sorries.
