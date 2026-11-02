# Candidate PR: projective space over a base (V.3, part 1, #285)

Branch: `pr/algebraicgeometry-motives`. Module:
`BoringMath/AlgebraicGeometry/ProjectiveSpace.lean` (new; mirror path
`Mathlib/AlgebraicGeometry/ProjectiveSpace.lean`, absent at the pin).

## Statement

* `projectiveSpaceGradedRing n` — the standard-graded `ℤ[x₀,…,x_{n-1}]`
  (abbrev to `MvPolynomial.homogeneousSubmodule`, with the local
  `MvPolynomial.gradedAlgebra` instance).
* `projectiveSpace n := «Proj» (projectiveSpaceGradedRing n)` — `P^{n-1}_ℤ`
  (mathlib's `Proj` scheme).
* `projectiveSpaceToSpecZ n` — the structure map to `Spec ℤ` (terminal map;
  mathlib's `Proj.toSpecZero` is `public section`-hidden at the pin, and the
  terminal map agrees with it by uniqueness).
* `projectiveSpaceOver n S := pullback … …` — `P^{n-1}_S = P^{n-1}_ℤ ×_ℤ S`,
  with projection `projectiveSpaceOverProj`; `projectiveLine S` — `P¹_S`.
* Sorried with peeling plans: `isProper_projectiveSpaceToSpecZ` (mathlib's
  `IsProper (Proj.toSpecZero)` + FiniteType of the degree-0 part +
  terminal uniqueness) and `smooth_projectiveSpaceOverProj` (standard opens
  are affine spaces; base change).

Named next peels (V.3 part 2): the Serre twisting sheaf `O(1)` on `Proj` and
the hyperplane class `h ∈ A¹(P^n)` — absent at the pin.

## Literature

* Hartshorne, GTM 52, ch. II, §7 (Proj; P^n as Proj of the polynomial ring).
  REVIEW(citation): pin the exercise.
* Stacks Project, tags 01M8 (Proj), 01O8 (projective space).
  REVIEW(citation): pin tags. Read at pin: mathlib's `ProjectiveSpectrum/`
  (Proj scheme, structure sheaf, properness) + `RingTheory/MvPolynomial/Homogeneous.lean`.
* 3264 (final draft, refs/eisenbud-harris-3264-final-draft.pdf), ch. 3.2:
  P^n as G(1,n+1) — read from the PDF TOC this session (ch. 3 "Introduction to
  Grassmannians", ch. 4 "Grassmannians in general": 4.1 Schubert cells/cycles,
  4.1.1 Schubert classes and Chern classes).
* MVW (refs/mvw-lecture-notes-motivic-cohomology.pdf), Lecture 1 read from
  the PDF: Cor_k, elementary correspondences, Construction 1.3 ([Z] for Z
  finite surjective over X), graph Example 1.2 — pins the C.1 citations.

## Does Mathlib already have it?

Partially: absolute `Proj` of a graded ring (scheme, structure sheaf,
properness) exists; no `P^n_S` over a base, no `O(1)`/Serre twist, no
projective line as a named object (grep-verified).

## Review notes

* Build: warning-clean except the 2 deliberate sorry-warnings (peeling plans
  inline); check-style 0 violations.
* Note: mathlib's `Proj.toSpecZero`/`basicOpen` are not nameable at the pin
  (inside `@[expose] public section`) — recorded; the terminal map is used
  instead, with the agreement noted in the docstring.
* Feeds: V.5 (#287) Grassmannian via Plücker (P^n = G(1,n+1) is the k=1
  case), V.4 (#284) projective bundle theorem, the Lefschetz motive
  (G.2 #289 needs P¹), E-line.
