# K-theory roadmap — BoringMath/KTheory/ (tickets #520–#524, TREE K.0–K.4)

Pin audit (mathlib v4.35.0-rc3): no K-theory beyond `Algebra.GrothendieckGroup`
(commutative monoids). BoringMath landed `CategoryTheory.K0` of an abelian
category (`CategoryTheory/Abelian/GrothendieckGroup.lean`, TREE K.0).
MISSING: functoriality ring completion, exact categories, Milnor K-theory,
GW/Witt rings, the K-theory spectrum.

## Ticket tree

- **#520** `KTheory/K0.lean` — SEED LANDED: `K0.map_comp` (functoriality,
  sorry with plan).
- **#521** `KTheory/Milnor.lean` — SEED LANDED: `MilnorK` class (graded
  abelian groups, symbols, `{ab} = {a}+{b}`), `MilnorK.steinberg` (sorry).
  TREE K.2.
- **#522** TREE K.1: exact categories and `K₀(exact)` (devissage), docking
  #520.
- **#523** TREE K.3/K.4: Grothendieck–Witt ring `GW(k)` and Witt ring `W(k)`
  of a field (pin has `QuadraticForm`), Pfister's theorem (orderings ↔
  primes of `W(k)`) — statement layer.
- **#524** the K-theory spectrum `K(A)` with `π₀ = K₀` (interfaces to
  `AlgebraicTopology/Spectra`, #510) — statement layer.

## References
* [Weibel], *The K-book*, ch. II–IV; [Milnor], Annals Studies 72, §5;
  [Lam], *Introduction to Quadratic Forms over Fields*, ch. VIII.
* mathlib pin v4.35.0-rc3: `Algebra.GrothendieckGroup`, `LinearAlgebra.QuadraticForm`;
  BoringMath pin: `CategoryTheory.K0`.
