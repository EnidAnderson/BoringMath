# Candidate PR: Nisnevich distinguished squares on schemes (`pr/algebraicgeometry-sites-nisnevich`)

Work order W1 (B2), issue EnidAnderson/BoringMath#9. Statement-only (Tier 1)
shard on top of the landed B1 module `BoringMath/CategoryTheory/Sites/CdStructure.lean`
(PR #7) and the B.0 base-change module (PR #51).

## Statement

One new module `BoringMath/AlgebraicGeometry/Sites/Nisnevich.lean`
(mirroring `Mathlib/AlgebraicGeometry/Sites/`, which at the pin holds
`BigZariski.lean`, `Etale.lean`, etc. but nothing Nisnevich):

* `AlgebraicGeometry.IsNisnevichSquare (sq : Square Scheme.{u}) : Prop` —
  structure with fields `isPullback : sq.IsPullback`,
  `isOpenImmersion_f₂₄ : IsOpenImmersion sq.f₂₄`, `etale_f₃₄ : Etale sq.f₃₄`,
  and `isoOnComplement : ∀ x : sq.X₄, x ∉ Set.range sq.f₂₄ → IsIso (sq.f₃₄.fiberToSpecResidueField x)`
  (cartesian; right leg an open immersion; bottom leg étale and an
  isomorphism over the open complement, stated scheme-theoretically via the
  fiber `→ Spec κ(x)`).
* `AlgebraicGeometry.nisnevichCdStructure : CdStructure Scheme.{u}` —
  `squares := {sq | IsNisnevichSquare sq}`.
* `AlgebraicGeometry.nisnevichTopology : GrothendieckTopology Scheme.{u} :=
  GrothendieckTopology.ofCdStructure nisnevichCdStructure`.
* `nisnevichTopology_eq_ofCdStructure` — topology agreement, routed through
  `ofCdStructure` as landed (primitive definitional lemma; the independent
  point-set pretopology definition and its agreement is the Tier-2 target).
* `nisnevichSquare_iff` — the point-set criterion as a *corollary* of the
  definition, never the foundation (proved, no sorry).
* `mem_nisnevichCdStructure_squares_iff`, `sieve_ofTwoArrows_mem_nisnevichTopology`
  — cheap Tier-2 peels (generation clause at the schemes level, proved from
  B1's `sieve_ofTwoArrows_mem_of_mem_squares`).
* `zariskiTopology_le_nisnevichTopology`, `nisnevichTopology_le_etaleTopology`
  — the sandwich, kept as well-typed `sorry`s with peeling plans
  (statement layer).

Design choice: the big site on `Scheme.{u}` itself, matching mathlib's
`Scheme.zariskiTopology` and `Scheme.etaleTopology` (the api-skeletons
picture's `SchemeOver S` has no GOLD counterpart at the pin;
`AlgebraicGeometry.Scheme.Over` is a typeclass on a single scheme, not a
category — the small site over `S` is the later Tier-2 target via
`smallGrothendieckTopology`).

## Naming memo (GOLD reads at pin v4.35.0-rc3, mathlib checkout in EnidsMathMadness)

* `CategoryTheory.Square` (`Mathlib/CategoryTheory/Square.lean`): fields
  `X₁ X₂ X₃ X₄` (implicit), `f₁₂ f₁₃ f₂₄ f₃₄`, `fac`.
* `Square.IsPullback` (`Mathlib/CategoryTheory/Limits/Shapes/Pullback/Square.lean`):
  `protected def Square.IsPullback : Prop := IsPullback sq.f₁₂ sq.f₁₃ sq.f₂₄ sq.f₃₄`.
* `AlgebraicGeometry.Etale` (`Mathlib/AlgebraicGeometry/Morphisms/Etale.lean:41`):
  `class Etale {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop`; instance
  (priority 900) `[IsOpenImmersion f] : Etale f` at line 76.
* `AlgebraicGeometry.IsOpenImmersion` (`Mathlib/AlgebraicGeometry/OpenImmersion.lean:36`):
  `abbrev IsOpenImmersion : MorphismProperty Scheme.{u}`.
* `Scheme.Hom.fiber`, `Scheme.Hom.fiberToSpecResidueField`
  (`Mathlib/AlgebraicGeometry/Fiber.lean`): `f.fiber y = pullback f (Y.fromSpecResidueField y)`;
  `f.fiberToSpecResidueField y : f.fiber y ⟶ Spec (Y.residueField y)`.
* Points: `instance : CoeFun (X ⟶ Y) (fun _ ↦ X → Y)` (`Scheme.lean:108`);
  `x : X` for `X : Scheme` via the `TopCat` coercion; `Scheme.residueField`,
  `Scheme.Hom.residueFieldMap` (`Mathlib/AlgebraicGeometry/ResidueField.lean`).
* Big sites: `AlgebraicGeometry.Scheme.zariskiTopology` (`Sites/BigZariski.lean:50`),
  `AlgebraicGeometry.Scheme.etaleTopology` (`Sites/Etale.lean`, Merten).
* `Sieve.ofTwoArrows` — used by Riou's `MayerVietorisSquare.lean:122` and by
  the landed B1 module.
* Green-field check: `grep -ri nisnevich Mathlib/` at the pin has exactly one
  hit — Riou's docstring. Confirmed again this session.

## Literature (web-verified this session)

* V. Voevodsky, *Homotopy theory of simplicial sheaves in completely
  decomposable topologies*, J. Pure Appl. Algebra 214 (2010), 1399–1406,
  arXiv:0805.4576 — §2 defines the upper (Nisnevich) cd-structure
  (pullback square, `p` étale, `e` open embedding, `p⁻¹(X∖e(A)) → X∖e(A)`
  an isomorphism); Proposition 2.16: the associated topology on Noetherian
  schemes is the Nisnevich topology. Pinned via the arXiv HTML full text.
* V. Voevodsky, *Homology of schemes*, **Selecta Math. (N.S.) 2 (1996),
  111–153** — correction: the work order's "Compositio Mathematica 111
  (1998)" is wrong; the Stacks Project bibliography gives Selecta Math.
  N.S. 2 (1996) 111–153, doi:10.1007/BF01587941.
* C. Mazza, V. Voevodsky, C. Weibel, *Lecture Notes on Motivic Cohomology*,
  Clay Mathematics Monographs 2 (2006), https://www.claymath.org/library/monographs/cmim02.pdf —
  Part 3 "Nisnevich sheaves with transfers" (Lectures 11–13, p. 81 ff.;
  Lecture 12 "Nisnevich sheaves / the cdh topology", p. 89). REVIEW(citation):
  the exact lecture defining the Nisnevich topology is unpinned.
* Y. Nisnevich, *The completely decomposed topology on schemes and
  associated descent spectral sequences in algebraic K-theory*, in:
  Algebraic K-theory: connections with geometry and topology (Lake Louise,
  AB, 1987), NATO ASI Ser. C 279, Kluwer, 1989, 241–342 (Stacks Project
  bibliography entry `Nishnevich`).
* J. Riou, `Mathlib/CategoryTheory.Sites/MayerVietorisSquare.lean` — GOLD,
  read in full at the pin; docstring names the Nisnevich distinguished
  squares (`f₂₄` open immersion, `f₃₄` étale iso over the complement) as the
  motivating example.

## Where it would live in Mathlib

`Mathlib/AlgebraicGeometry/Sites/Nisnevich.lean`, next to Merten's
`Mathlib/AlgebraicGeometry/Sites/Etale.lean`.

## Does Mathlib already have it?

No. One Nisnevich mention in all of `Mathlib/` at the pin (Riou's docstring).
cd-structures themselves are BoringMath's own B1 module (PR #7).

## Review notes

* Two deliberate `sorry`s with peeling plans (the Zariski/étale sandwich);
  everything else is proved. Tier-2 targets: the sandwich proofs, the
  Mayer–Vietoris property of distinguished squares for `nisnevichTopology`
  (via `CdStructure.IsMayerVietoris` + Riou's `MayerVietorisSquare.mk'`),
  and the small Nisnevich site over a base scheme.
* Build note: the local checkout's `main` was stale; origin/main's landed
  modules were materialized as *untracked* copies in the working tree
  purely to build — identical content to origin/main, not for committing.
