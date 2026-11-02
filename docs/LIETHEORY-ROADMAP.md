# Lie theory roadmap — BoringMath/LieTheory/ (tickets #549–#553, CFSG Lie-type #251–#253)

Pin audit (mathlib v4.35.0-rc3): `Algebra/Lie/*` (Lie algebras, modules,
weights, root systems) and `Geometry/Manifold/Algebra/LieGroup` (Lie groups).
MISSING: root data acting on groups, the Chevalley construction, Steinberg
relations, and the bridge to BN-pairs. The scheme-side lives in
`AlgebraicGroups/` (#321–#326).

## Ticket tree

- **#549** `LieTheory/RootData.lean` — SEED LANDED: `RootDatum` (data +
  reflection law), `chevalley_group_finite` (sorry with plan). Home of
  #323.
- **#550** `LieTheory/LieGroup.lean` — SEED LANDED: `IsFiniteGroupOfLieType`,
  `bnPair_of_finite_lie_type` (sorry; Bruhat decomposition route to
  `BNPairs`, #251).
- **#551** #323/#252: Chevalley construction completed — `G(Φ, F_q)` finite
  with root subgroups `U_α(F_q)` (consumes #549).
- **#552** #324: Steinberg relations / presentation of `G(F_q)`; finiteness.
- **#553** #325/#326: reductive and twisted groups (Steinberg–Suzuki–Ree),
  statement layer; docks Deligne–Lusztig #319 (`RepresentationTheory`).

## References
* [Borel], ch. IV; [Carter], ch. 8–11 (tables held); [Steinberg], Lectures
  3, 8; [Helgason], ch. II; [Wilson], ch. 3.
* mathlib pin v4.35.0-rc3: `Algebra.Lie.*`, `Geometry.Manifold.Algebra.LieGroup`;
  BoringMath pin: `GroupTheory.CFSG.BNPair`, `AlgebraicGroups.Linear` (#309).
