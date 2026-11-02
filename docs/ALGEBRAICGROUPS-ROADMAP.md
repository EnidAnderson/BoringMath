# Algebraic groups roadmap — BoringMath/AlgebraicGroups/ (tickets #321–#326)

Pin audit (mathlib v4.35.0-rc3): mathlib has schemes
(`AlgebraicGeometry/AffineScheme` etc.) and Lie algebras, but NO linear
algebraic groups as group objects, no Chevalley construction, no root data
acting on groups. This folder is the Lie-type sector's foundation (#251–#253).

## Ticket tree

- **#321** `AlgebraicGroups/Basic.lean` — SEED: a linear algebraic group as a
  group object in affine schemes (or concretely: a closed subgroup of GL(n)
  given by polynomial equations — the concrete carrier we build on), with
  GL(n), SL(n) instances.
- **#322** root data and the BN-pair interface: connect to `GroupTheory/CFSG/
  BNPair.lean`; Bruhat decomposition statement for split groups.
- **#323** Chevalley construction: from a root datum + field, the group
  G(F_q) with its BN-pair; [Carter] tables (held) as data.
- **#324** Steinberg relations / presentation of G(F_q); finiteness of G(F_q).
- **#325** reductive groups: definition, examples (GL, SL, Sp, SO), the
  isogeny/simply-connected statement layer; interface to Deligne–Lusztig #319.
- **#326** twisted groups (Steinberg/Suzuki/Ree) statement layer joining sector
  C (#231); field automorphisms acting on the BN-pair.

## References
* [Borel] A. Borel, *Linear Algebraic Groups*, Springer 1991.
* [Carter] R. W. Carter, *Simple Groups of Lie Type*, Wiley 1972 (tables held in
  ../refs/).
* [Steinberg] *Lectures on Chevalley Groups*, 1967 (obtain list); [Geck
  arXiv:2404.11472] (held in ../refs/).
* mathlib pin v4.35.0-rc3: `AlgebraicGeometry.*`, `Algebra.Lie.*`,
  `LinearAlgebra.Matrix.GeneralLinearGroup`.
