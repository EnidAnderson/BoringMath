# Candidate PR: vector bundles on schemes (V.1, #280)

Branch: on `pr/algebraicgeometry-motives`. Module:
`BoringMath/AlgebraicGeometry/VectorBundle/Basic.lean` (new; mirror path
`Mathlib/AlgebraicGeometry/VectorBundle/`, absent at the pin).

## Statement

* `IsLocallyFreeOfFiniteRank X M` — a sheaf of `O_X`-modules admitting
  local-generator data with finite generating sets (mathlib has the
  `SheafOfModules.IsLocallyFree` class, Stacks 01C6, and the abelian category
  `X.Modules`; no bundled vector-bundle type at the pin).
* `VectorBundle X` — bundled (toModule, isLocallyFree, finiteRank).
* `Category (VectorBundle X)` (morphisms = module-sheaf maps), the forgetful
  functor `VectorBundle X ⥤ X.Modules`, the free bundle `free I` for finite
  `I`, and `directSum` (biproduct).
* Statement layer (sorried with peeling plans): `dual`, `tensorProduct`,
  `det` — the sheaf-level internal Hom / tensor product / exterior powers are
  ABSENT at the pin (grep-verified); the peel is sheafification of the
  presheaf-level constructions (sheafification exists for `X.Modules`).
* Also sorried: `free_finiteRankData` (cover by ⊤ + `free.generatingSections`),
  `isLocallyFree_biprod` / `finiteRank_biprod` (union of coverings +
  `freeSumIso`).

## Literature

* Hartshorne, *Algebraic Geometry*, GTM 52, ch. II, §5 (vector bundles as
  locally free sheaves; dual/det exercises). REVIEW(citation): pin sections.
* Stacks Project, tag 01C6 (locally free), 01C7? REVIEW(citation): pin tags.
* EGA I (new ed.) §1.7? REVIEW(citation).

## Does Mathlib already have it?

No — `VectorBundle` exists only for manifolds (`Geometry/Manifold`); schemes
have `X.Modules` (abelian, Grothendieck) and `IsLocallyFree`, nothing bundled.

## Review notes

* Build: warning-clean except the 6 deliberate sorry-warnings (each with
  TEMPORARY SORRY + peeling plan); check-style 0 violations.
* Feeds: V.2 (#282) relative Proj / P(E), I.3 (#286) Chern classes, V.4 (#284)
  projective bundle theorem — the road to I.5 (#290) and C.2/G.2.
