# Candidate PR: the base change of the scheme-theoretic fiber

Ticket: BoringMath issue #16 (C.0 clause 3: the base-change iso for fibers
— the first named peel of the zero-cycle base-change functoriality).
Branch: `feat/fiber-base-change`.
Module: `BoringMath/AlgebraicGeometry/Fiber/BaseChange.lean`
(owner directory: Mathlib's `AlgebraicGeometry/Fiber.lean` at the pin;
the base-change API of the scheme-theoretic fiber; see
`docs/OWNERSHIP.md`).

## Statement

Given a cartesian square `IsPullback fst snd f g` (with `fst : P ⟶ X`,
`snd : P ⟶ Y`, `f : X ⟶ Z`, `g : Y ⟶ Z`) and a point `y : Y`:

* `AlgebraicGeometry.fiberBaseChange` — **the base-change map of the
  fibers**: `snd.fiber y ⟶ f.fiber (g y)`, the map induced by the
  cartesian map (`pullback.map` over the residue-field square; the
  compatibility of the residue-field square is
  `Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField`).
* `AlgebraicGeometry.fiberBaseChange_fiberι` — the base-change map
  restricts the cartesian map: it embeds the fiber into the base-changed
  scheme over the embedding of the image fiber
  (`μ ≫ f.fiberι (g y) = snd.fiberι y ≫ fst`; `pullback.lift_fst`).
* `AlgebraicGeometry.fiberBaseChange_fiberToSpecResidueField` — the
  base-change map lies over the map of the spectra of the residue fields
  (`pullback.lift_snd`).
* `AlgebraicGeometry.isPullback_fiberBaseChange` — **the base change of
  the fiber is cartesian**: the square of the base-change map over the
  residue-field square is a pullback
  (`isPullback_fiberToSpecResidueField_of_isPullback` at the pin).
* `AlgebraicGeometry.fiberBaseChangeIso` — **the base-change iso of the
  fibers**: `snd.fiber y ≅ f.fiber (g y) ×[Spec κ(g y)] Spec κ(y)`
  (`IsPullback.isoPullback`).
* `AlgebraicGeometry.flat_fiberBaseChange` — **the base-change map of the
  fibers is flat**: the base change is by a field extension — the map of
  the spectra of the residue fields — and flatness is stable under base
  change (the flatness of the residue-field square rides the flatness of
  a morphism into a one-point integral scheme; the transport to the
  named map is `IsPullback.isoPullback_hom_fst` and `Flat.comp`).
* `AlgebraicGeometry.surjective_fiberBaseChange` — **the base-change map
  of the fibers is surjective**: the base change is by a surjective map
  of one-point spectra, and surjectivity is stable under base change
  (`Scheme.exists_preimage_of_isPullback`; the agreement of the two
  points of the spectra of the residue fields is the uniqueness of the
  point of the spectrum of a field).
* `AlgebraicGeometry.mem_genericPoints_fiberBaseChange` — **the
  base-change map of the fibers carries generic points to generic
  points**: the image of a generic point of an irreducible component of
  the fiber of the vertical morphism is a generic point of an
  irreducible component of the fiber of the given morphism. The image
  point lies in an irreducible component, whose generic point
  specializes to it (`genericPoints.ofComponent`,
  `IsGenericPoint.specializes`); the flat base-change map lifts the
  specialization (`exists_specializes_of_flat`), and the lifted
  specialization into a generic point is the generic point
  (`eq_of_specializes_of_mem_genericPoints`).

## Notes

* The base-changed fiber `f.fiber (g y) ×[Spec κ(g y)] Spec κ(y)` is the
  fiber of `f.fiberToSpecResidueField (g y)` over the point of
  `Spec (Z.residueField (g y))` corresponding to `y`; the cycle-level
  base-change functoriality rides this iso, with the residue-degree
  bookkeeping of the fiber embeddings (`residueDegree_fiberι`, landed).

## Verification

* `lake build` clean (2728 jobs, zero warnings).
* `scripts/check-style.sh` zero violations, zero sorries.
