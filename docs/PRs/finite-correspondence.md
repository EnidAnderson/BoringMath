# Candidate PR: finite correspondences as data (C.1, #10)

Branch: `pr/correspondence-finite` (proposed). Module:
`BoringMath/AlgebraicGeometry/Correspondence/Finite.lean` (new; extends the
landed `Correspondence/Graph.lean`, PR #72).

## Statement

The C.1 structure-of-record (cycle on the fiber product, per the ratified
C.1/C.2 ownership ruling of 2026-10-26):

* `AlgebraicCycle.IsFiniteOverSource π c` — a cycle on `W` is finite over `X`
  along `π : W ⟶ X` when every fiber of `π` meets the support finitely.
* `finiteCorrespondenceAddSubgroup pX pY` — the additive subgroup of
  `AlgebraicCycle (X ×_S Y) ℤ` of finite cycles finite over the source along
  `pullback.fst`; closure laws `isFiniteOverSource_zero`,
  `IsFiniteOverSource.add`, `IsFiniteOverSource.neg`.
* `FiniteCorrespondence pX pY` — the subtype; named projections from day one
  per the ruling: `toCycle`, `multiplicity`, `support`, `isFinite`,
  `finiteOverSource`, `ext_iff`, and the primitive definitional lemmas
  `zero_toCycle`, `add_toCycle`, `neg_toCycle`, `multiplicity_add`. The
  `AddCommGroup` instance is the induced one on the subgroup.
* `graphFiniteCorrespondence f hf hqc` — the graph correspondence as a finite
  correspondence; the finite-over-source proof uses that the graph is a
  section of the first projection (`graph_fst`), so the fiber over `x` meets
  the support in at most `{graph x}`.
* `Scheme.id_apply` — primitive definitional lemma (identity acts as identity
  on points).

All proofs are exact and sorry-free.

## Scope notes / obstructions

* The classical definition (free abelian group on integral closed `Z ⊆ X ×_S Y`
  with `Z → X` finite and surjective over a component) is identified with the
  structure-of-record by decomposition into irreducible components — named
  Tier-2 peel (`FiniteCorrespondence` effective generators); the point-set
  finite-fibers condition is the operative one used in composition.
* Surjectivity over a component is a condition on effective generators, not on
  the group; recorded for the Tier-2 generator layer.

## Literature

* C. Mazza, V. Voevodsky, C. Weibel, *Lecture Notes on Motivic Cohomology*,
  Clay Mathematics Monographs 2, Amer. Math. Soc. / Clay Math. Inst., 2006,
  Lecture 1 "The category of finite correspondences" (p. 3; TOC web-verified),
  the definition of `Cor_S(X, Y)`. REVIEW(citation): exact definition number.
* A. Suslin, V. Voevodsky, *Singular homology of abstract algebraic
  varieties*, J. reine angew. Math. 481 (1996), 205–232. REVIEW(citation):
  section to be pinned.
* W. Fulton, *Intersection Theory*, ch. 1, §1 (cycles as finite formal sums).
  REVIEW(citation): section to be pinned.

## Where it would live in Mathlib

`Mathlib/AlgebraicGeometry/Correspondence/Finite.lean` (new directory at the
pin; the correspondence layer has no upstream mirror yet — same placement note
as `Correspondence/Graph.lean`).

## Does Mathlib already have it?

No. At the pin `Mathlib/AlgebraicGeometry/AlgebraicCycle/Basic.lean` is a single
file (cycles + weighted pushforward `map`); no correspondences anywhere
(grep-verified for the C.1 prep).

## Review notes

* Build: `lake build BoringMath.AlgebraicGeometry.Correspondence.Finite` clean,
  zero sorries, `check-style.sh` 0 violations.
* Computability: `FiniteCorrespondence` is a Prop-refined subtype of the cycle
  group — computable as a type; `graphFiniteCorrespondence` is `noncomputable`
  (the fundamental cycle chooses the generic points), flagged inline.
