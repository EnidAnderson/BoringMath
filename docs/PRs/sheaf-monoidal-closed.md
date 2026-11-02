# Candidate PR: MonoidalClosed on sheaf categories (TREE H.8, #42)

## Statement

One new module `BoringMath/CategoryTheory/Sites/SheafMonoidalClosed.lean`,
addressing the TODO in the module docstring of
`Mathlib/CategoryTheory/Sites/Monoidal.lean` (Riou), quoted verbatim in issue
#42, in two peels (floor first):

* **Peel (a) — the floor**: `Sheaf.monoidalClosed`, a `scoped instance`
  `MonoidalClosed (Sheaf J A)` under the module's hypotheses
  (`MonoidalClosed A`, `SymmetricCategory A`, `∀ F₁ F₂ : Cᵒᵖ ⥤ A,
  HasFunctorEnrichedHom A F₁ F₂` and `HasEnrichedHom A F₁ F₂`,
  `HasWeakSheafify J A`), obtained abstractly as
  `Monoidal.Reflective.monoidalClosed (sheafificationAdjunction J A)` — exactly
  the route the TODO certifies ("a `MonoidalClosed` instance on sheaves can
  already be obtained abstractly using the material in
  `CategoryTheory.Monoidal.Braided.Reflection`").
* **Peel (b) — the TODO's real content**: the explicit internal hom
  `sheafInternalHom F := sheafToPresheaf J A ⋙ ihom ((sheafToPresheaf J A).obj F)
  ⋙ presheafToSheaf J A`, with
  `sheafInternalHom_underlying_iso : (sheafToPresheaf J A).obj
  (sheafInternalHom F |>.obj G) ≅ (ihom ((sheafToPresheaf J A).obj F)).obj
  ((sheafToPresheaf J A).obj G)` — the underlying presheaf of the sheaf
  internal hom is the internal hom in the category of presheaves.

Supporting declarations: `ihom_obj_eq_functorEnrichedHom`
(`(ihom F).obj G = functorEnrichedHom A F G`, definitional at the pin),
`sheafInternalHom_eq_ihom`, `sheafInternalHom_eq_internalHom` (both `rfl`
primitive definitional lemmas tying `sheafInternalHom` to `ihom F` and to
`MonoidalClosed.internalHom.obj (op F)` under `Sheaf.monoidalClosed`), and
`tensorLeft_adj_sheafInternalHom : tensorLeft F ⊣ sheafInternalHom F` (the
adjunction of the reflection's `Closed` structure).

Hypotheses are explicit binders throughout, matching the hypothesis list of
`Mathlib.CategoryTheory.Sites.Monoidal` itself. `Sheaf.monoidalCategory` is made
a *local* instance (as in Mathlib's own file) because the monoidal structure on
sheaves is deliberately not a global instance; correspondingly
`Sheaf.monoidalClosed` is delivered as a `scoped instance`, not a global one,
so it cannot diamond with H.7's `sheafTypesMonoidalClosed` on
`Sheaf J (Type _)`.

**Cross-citation to H.7 (#41)**: the module imports
`BoringMath.CategoryTheory.Sites.SheafHomBifunctor` and cross-cites it in the
module docstring — for sheaves of types, the cartesian closed structure and the
identification of its internal hom with `sheafHom`
(`sheafHom_iso_internalHom`) are H.7's content and are not duplicated here.

## Literature

* [Riou] J. Riou, `Mathlib.CategoryTheory.Sites.Monoidal` — the TODO anchor,
  read in full at the pin (GOLD).
* [Day] B. Day, *A reflection theorem for closed categories*, J. Pure Appl.
  Algebra 2(1) (1972), 1-11 — verified by web search (ScienceDirect,
  doi:10.1016/0022-4049(72)90021-7); this is the theorem behind
  `CategoryTheory.Monoidal.Braided.Reflection`.
* [Day70] B. Day, *On closed categories of functors*, in: Reports of the
  Midwest Category Seminar IV, Lecture Notes in Math. 137, Springer, 1970,
  1-38 — verified by web search (MathSciNet MR0272852); Day convolution
  internal hom = functor enriched hom.
* [SGA4] M. Artin, A. Grothendieck, J. L. Verdier (eds.), *Théorie des topos et
  cohomologie étale des schémas (SGA 4)*, Séminaire de Géométrie Algébrique du
  Bois-Marie 1963-1964, Lecture Notes in Math. 269, 270, 305, Springer,
  1972-73, Exposés I-II — bibliographic anchor verified by web search (nLab
  "SGA4", Springer). Exact proposition pins are `REVIEW(citation)` (owned by
  W5/#13 per issue #42).
* [MM] S. Mac Lane, I. Moerdijk, *Sheaves in Geometry and Logic*, Springer,
  1992, Chapter I. `REVIEW(citation)`.
* [Mac Lane] S. Mac Lane, *Categories for the Working Mathematician*, 2nd ed.,
  Springer, 1998, Chapter IV (adjoints). `REVIEW(citation)`.

## Where it would live in Mathlib

`Mathlib/CategoryTheory/Sites/Monoidal.lean` itself (it is that file's TODO),
or a new `Mathlib/CategoryTheory/Sites/MonoidalClosed.lean` importing it.

## Does Mathlib already have it?

* The abstract `MonoidalClosed (Sheaf J A)`: **no instance** — Mathlib
  deliberately keeps `Sheaf.monoidalCategory` a `def`, and the TODO says the
  closed instance "can already be obtained abstractly" from
  `Monoidal.Braided.Reflection` without ever providing it. This module delivers
  it as `Sheaf.monoidalClosed`.
* The underlying-presheaf identification of the internal hom: **no** — that is
  precisely the TODO's second bullet, not present at pin v4.35.0-rc3 (verified
  by reading `Sites/Monoidal.lean` in full: only `isSheaf_functorEnrichedHom`
  and the `W`/`Sheaf` monoidal structures exist there).
* Presheaf-level ingredients all exist at the pin (GOLD): scoped instance
  `MonoidalClosed.FunctorCategory.monoidalClosed` (`Monoidal/Closed/
  FunctorCategory/Basic.lean:145`), `functorCategorySymmetric`
  (`Monoidal/FunctorCategory.lean:195`), `Presheaf.isSheaf_functorEnrichedHom`
  (`Sites/Monoidal.lean:104`), `Monoidal.Reflective.monoidalClosed`
  (`Monoidal/Braided/Reflection.lean:240`).

## Review notes

* Purely additive: one new module + this note, per the modular fast-forward
  protocol. No existing file touched; no commit; no branch switch.
* **Build (machine-on)**: `lake build
  BoringMath.CategoryTheory.Sites.SheafMonoidalClosed` — `Build completed
  successfully (1415 jobs)`; **zero warnings from this module** (the only
  warnings in the log are H.7's 14 deliberate `sorry`s in
  `SheafHomBifunctor.lean`, replayed as a dependency).
  `bash scripts/check-style.sh
  BoringMath/CategoryTheory/Sites/SheafMonoidalClosed.lean` — `0 violation(s),
  0 sorry(s)`. All lines ≤ 100 columns; header copied from
  `BoringMath/Foundations/Eta.lean`; every declaration carries a
  `-- Reference:` within 12 lines above it plus a docstring.
* **No sorries**: every declaration is proved honestly. The only tactics used
  are `have` (with explicit type ascriptions) and `exact`; the three `rfl`
  proofs are primitive definitional lemmas (STYLE §5), and the one cast is by
  explicit application of the named definitional lemma (the adjunction is taken
  directly from the reflection's `Closed` structure, whose right adjoint is
  `sheafInternalHom F` definitionally).
* **GOLD-verified names at pin v4.35.0-rc3**
  (`EnidsMathMadness/.lake/packages/mathlib`): `Monoidal.Reflective.monoidalClosed`
  (Braided/Reflection.lean:240), `sheafificationAdjunction` (Sites/
  Sheafification.lean:80), `presheafToSheaf` (:73), `HasWeakSheafify` (:37),
  `Reflective (sheafToPresheaf J A)` instance (:86),
  `sheafToPresheaf` (Sites/Sheaf.lean:328), `fullyFaithfulSheafToPresheaf`
  (:340), `sheafificationIso` (Sheafification.lean:228),
  `Sheaf.monoidalCategory` (Sites/Monoidal.lean:168),
  `GrothendieckTopology.W.monoidal` instance (Sites/Monoidal.lean:152),
  `Presheaf.isSheaf_functorEnrichedHom` (Sites/Monoidal.lean:104),
  `MonoidalClosed.FunctorCategory.monoidalClosed` scoped instance
  (Monoidal/Closed/FunctorCategory/Basic.lean:145),
  `functorCategorySymmetric` (Monoidal/FunctorCategory.lean:195),
  `ihom` (Monoidal/Closed/Basic.lean:76), `MonoidalClosed.internalHom`
  (:289), `SymmetricCategory` extends `BraidedCategory`
  (Monoidal/Braided/Basic.lean:367), `HasEnrichedHom`/`HasFunctorEnrichedHom`/
  `functorEnrichedHom` (Enriched/FunctorCategory.lean:54/295/309).
  Key definitional facts checked by `rfl` at the pin: `(ihom F).obj G =
  functorEnrichedHom A F G` on presheaves, and `sheafInternalHom F = ihom F =
  MonoidalClosed.internalHom.obj (op F)` on sheaves under `Sheaf.monoidalClosed`.
* Proof of `sheafInternalHom_underlying_iso` in one chain:
  `ihom_obj_eq_functorEnrichedHom` (presheaf internal hom = functor enriched
  hom) → `Presheaf.isSheaf_functorEnrichedHom` (it is a sheaf, using
  `G.property`) → `Eq.subst` transport → `sheafificationIso` (a sheaf is its
  own sheafification, so `sheafToPresheaf (presheafToSheaf X) ≅ X` for sheaves
  `X`).
* Open questions for the human: (1) `Sheaf.monoidalClosed` is a *scoped*
  instance (not global) to avoid the diamond with H.7's
  `sheafTypesMonoidalClosed` at `A := Type _` — is scoped the right opt-in
  level, or should it be a plain `def` like `Sheaf.monoidalCategory`?
  (2) No `A := Type _` specialization is stated in code: at the pin, presheaves
  of types carry two `MonoidalClosed` instances (`FunctorToTypes.monoidalClosed`
  and the scoped `FunctorCategory.monoidalClosed`), so a Type-specialized
  declaration would hit an instance diamond; the sheaf-of-types internal hom
  remains H.7's `sheafHom`, cross-cited above. (3) SGA 4 / [MM] / [Mac Lane]
  proposition pins are `REVIEW(citation)`, routed to W5/#13 per issue #42.
