# Candidate PR: the residue fields of a preimmersion

Ticket: BoringMath issue #16 (C.0 clause 3: the residue degree of the fiber
embedding — the general degree lemma; the fiber application follows as
`ResidueField/Fiber.lean`). Branch: `feat/residue-field-preimmersion`.
Module: `BoringMath/AlgebraicGeometry/ResidueField/Preimmersion.lean`
(owner directory: Mathlib's `AlgebraicGeometry/ResidueField.lean` at the
pin; the residue field API of `Mathlib/AlgebraicGeometry/Morphisms/
Preimmersion.lean`, whose class `IsPreimmersion` extends
`SurjectiveOnStalks`; see `docs/OWNERSHIP.md`).

## Statement

* `Scheme.Hom.residueFieldMap_residue_apply` — the residue field map sends
  the residue of a germ to the residue of the pulled-back germ: the
  element-level form of `Scheme.residue_residueFieldMap`
  (`Y.residue (f x) ≫ f.residueFieldMap x = f.stalkMap x ≫ X.residue x`).
* `Scheme.Hom.residueFieldMap_surjective` — a morphism surjective on
  stalks induces surjections on residue fields: the residue of any class
  is attained, because every germ in the target stalk is the pullback of
  a germ (`Scheme.Hom.stalkMap_surjective`, the class field of
  `SurjectiveOnStalks`) and every class has a germ representative
  (`Scheme.residue_surjective`).
* `Scheme.Hom.residueDegree_of_surjectiveOnStalks` — **the residue degree
  of a morphism surjective on stalks is one**: the residue field map is a
  bijection (surjective by the previous lemma, injective since the source
  residue field is a field — `RingHom.injective` via
  `DivisionRing.isSimpleRing`), so the target residue field is generated
  over the source by the single nonzero element 1
  (`finrank_eq_one`, over the algebra `residueFieldAlgebra` of the landed
  tower module).
* `Scheme.Hom.residueDegree_of_isPreimmersion` — an immersion does not
  change residue fields: the residue degree of a preimmersion at every
  point is one (the class projection `IsPreimmersion → SurjectiveOnStalks`).

## Notes

* The mathlib residue degree carries the algebra of the residue field map
  ad hoc (`letI` inside `Hom.residueDegree`); the landed instance
  `Scheme.Hom.residueFieldAlgebra` is definitionally that algebra, so the
  `finrank_eq_one` application resolves the module structure through it
  without spelling the instance.
* The element-level peel `residueFieldMap_residue_apply` follows the
  landed `residueFieldMap_comp_apply` pattern: the composition of ring
  homs evaluates as `RingHom.comp_apply`, and the morphism equation is
  transported by `DFunLike.congr_fun` under `congrArg CommRingCat.Hom.hom`.
* `IsTorsionFree` for a residue-field extension resolves by instance
  search over the `residueFieldAlgebra` instance (fields acting on fields).

## Verification

* `lake build` clean (2726 jobs, zero warnings).
* `scripts/check-style.sh` zero violations, zero sorries.
