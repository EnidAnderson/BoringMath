# Representation theory roadmap — BoringMath/RepresentationTheory/ (tickets #315–#320)

Pin audit (mathlib v4.35.0-rc3): `Mathlib/RepresentationTheory/` has
`Basic`, `Character`, `FDRep`, `FinGroupCharZero`, `Action`, `Homological`,
`Continuous`. MISSING: blocks and Brauer theory, projective representations /
Schur covers, Deligne–Lusztig character input (needs AlgebraicGroups #321+).

## Ticket tree

- **#315** finite-group characters: orthogonality relations consumed from pin
  (`Character`), restated in our naming; `card` of irreducibles = #classes
  (statement + proof plan).
- **#316** induced representations and Frobenius reciprocity (pin has
  `Coinduced`; reciprocity proof).
- **#317** blocks: definition (indecomposable two-sided ideals of the group
  algebra), defect groups; Brauer's theorem statement (#249 in CFSG register).
- **#318** projective representations and the Schur multiplier H²(G, Fˣ)
  (links Cohomology #327).
- **#319** Deligne–Lusztig setup interface: for G a finite reductive group,
  the DL variety construction statement (needs AlgebraicGroups); characters
  R_T^θ as data (#253).
- **#320** applications: simplicity proofs of Lie-type groups via characters
  (Iwasawa is the #230 route; this is the character route), and the motivic
  consumer #262 (irreducible ℓ-adic reps ↔ simple motives).

## References
* [Isaacs] I. M. Isaacs, *Character Theory of Finite Groups*, AMS 1994.
* [Serre] J.-P. Serre, *Linear Representations of Finite Groups*, Springer 1977.
* [Feit] W. Feit, *The Representation Theory of Finite Groups*, AMS 1982
  (blocks/Brauer).
* [Deligne–Lusztig 1976] (held in ../refs/).
* mathlib pin v4.35.0-rc3: `RepresentationTheory.Character`, `FDRep`,
  `FinGroupCharZero`.
