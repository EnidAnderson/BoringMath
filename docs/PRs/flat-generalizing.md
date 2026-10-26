# Candidate PR: specialization lifting for flat maps of affine schemes

Ticket: BoringMath issue #16 (C.0 clause 3: the generic-point transfer —
the affine case of the scheme-level specialization lifting for flat
morphisms). Branch: `feat/flat-generalizing`.
Module: `BoringMath/AlgebraicGeometry/Morphisms/Flat/Generalizing.lean`
(owner directory: Mathlib's `AlgebraicGeometry/Morphisms/Flat.lean` at
the pin; see `docs/OWNERSHIP.md`).

## Statement

* `AlgebraicGeometry.exists_specializes_of_flat_specMap` — **flat maps
  of affine schemes lift specializations**: for a flat map
  `Spec.map φ : Spec S ⟶ Spec R` of affine schemes, a point `Q` of the
  source, and a specialization `P₀ ⤳ Spec.map φ Q` in the target, there
  is a point `Q₀` of the source with `Q₀ ⤳ Q` over `P₀`. This is the
  affine case of the going-down property of flat ring maps: the map of
  the spectra of a flat ring map is generalizing
  (`RingHom.Flat.generalizingMap_comap`, via the flatness of the
  spectrum map `Flat.SpecMap_iff`).

## Notes

* The consumer is the scheme-level specialization lifting for flat
  morphisms (the generic-point transfer along the base-change map of
  the fibers): the lifting is produced in affine opens and transported
  to the ambient scheme. The remaining inputs for the scheme-level
  assembly: the affine-open conjugation of restricted maps (a map of
  affine schemes as a map of spectra, up to iso), and the transport of
  the specialization hypothesis into the affine open
  (`Opens.specializes_iff`, landed).

## Verification

* `lake build` clean (2742 jobs, zero warnings).
* `scripts/check-style.sh` zero violations, zero sorries.
