# Candidate PR: `sheafHom` bifunctor + product adjunction (TREE H.7, #41)

## Statement

One new module `BoringMath/CategoryTheory/Sites/SheafHomBifunctor.lean`,
addressing the TODO in `Mathlib/CategoryTheory/Sites/SheafHom.lean` (Riou),
quoted verbatim in issue #41, in three peels:

* **Peel (a)** — the hom-bifunctor on `Sheaf J A`:
  `presheafHomPostcomp` / `presheafHomPrecomp` (the underlying natural
  transformations), `presheafHomFunctor` (covariant in the second variable,
  laws proved honestly via `presheafHomPostcomp_id` / `_comp`),
  `presheafHomBifunctor`, and the sheaf-level `sheafHomPostcomp` /
  `sheafHomPrecomp` / `sheafHomFunctor` / `sheafHomBifunctor`.
* **Peel (b)** — the adjunction `(- ⨯ F) ⊣ sheafHom F` for sheaves of types:
  `prodWith F` (the functor `X ↦ X ⨯ F`, laws from `prod.map_id_id` /
  `prod.map_comp_id`), the bijection `sheafHomProdHomEquiv :
  (X ⨯ F ⟶ Y) ≃ (X ⟶ sheafHom F Y)` assembled from `sheafHomCurry` /
  `sheafHomUncurry` and their two inverse laws, and `sheafHomAdjunction`
  via `Adjunction.mkOfHomEquiv`.
* **Peel (c)** — Cartesian closedness of `Sheaf J (Type (max u v))`:
  `instance sheafTypesMonoidalClosed : MonoidalClosed (Sheaf J
  (Type (max u v)))` (at this pin "Cartesian closed" = `CartesianMonoidalCategory`
  + `MonoidalClosed`), `prodWith_isLeftAdjoint`, and the statement
  `sheafHom_iso_internalHom : sheafHom F G ≅ (internalHom.obj (op F)).obj G`.

Universe discipline: with `A := Type (max u v)` and `CategoryTheory.types :
Category.{w} (Type w)`, `sheafHom F G : Sheaf J (Type (max u v))` lands in the
same sheaf category (`max u (max u v)` reduces to `max u v`), so the
adjunction lives in a single category.

## Literature

* [Riou] J. Riou, `Mathlib/CategoryTheory.Sites.SheafHom` — the TODO anchor,
  read in full at the pin (GOLD).
* [SGA4] Grothendieck et al., *EGA IV*, Publ. Math. IHÉS 32 (1967), Exposé I.
  `REVIEW(citation)` (pins owned by W5/#13 per the issue).
* [Stacks] The Stacks Project, Chapter 7 "Sites and Sheaves" (tag 00UZ),
  §7.7 "Sheaves" (tag 00VL) — chapter/section existence verified by web search;
  the exact cartesian-closedness lemma tag is `REVIEW(citation)`.
* [MM] Mac Lane–Moerdijk, *Sheaves in Geometry and Logic*, Ch. I. `REVIEW(citation)`.
* [Mac Lane] Mac Lane, *CWM* 2nd ed., Ch. IV (Adjoints). `REVIEW(citation)`.

## Where it would live in Mathlib

`Mathlib/CategoryTheory/Sites/SheafHomBifunctor.lean`, directly extending
Riou's `Mathlib/CategoryTheory/Sites/SheafHom.lean` (which it imports).

## Does Mathlib already have it?

* The bifunctor and the `sheafHom` adjunction: **no** — they are exactly the
  TODO of `SheafHom.lean` at pin v4.35.0-rc3 (verified by reading the file in
  full at the pin).
* Cartesian closedness of `Sheaf J (Type _)`: **yes, indirectly** —
  `instance : MonoidalClosed (Sheaf J A)` (`Sites/CartesianClosed.lean:28`)
  together with `CartesianMonoidalCategory (Sheaf J A)`
  (`Sites/CartesianMonoidal.lean`), `HasSheafify J (Type (max u v))`
  (`Sites/LeftExact.lean:313`) and `MonoidalClosed (C ⥤ Type (max w v u))`
  (`Monoidal/Closed/FunctorToTypes.lean:74`) already give peel (c) as an
  `inferInstance`. What Mathlib does **not** have is the identification of the
  internal hom with `sheafHom` — that is peel (b), stated here as
  `sheafHom_iso_internalHom`.

## Review notes

* Purely additive: one new module + this note, per the modular fast-forward
  protocol. No existing file touched; no commit; no branch switch.
* **Build (2026-10-30, machine-on)**: `lake build
  BoringMath.CategoryTheory.Sites.SheafHomBifunctor` — `Build completed
  successfully`; the only warnings are the 14 deliberate `sorry`s.
  `bash scripts/check-style.sh
  BoringMath/CategoryTheory/Sites/SheafHomBifunctor.lean` — `0 violation(s)`.
  All names GOLD-verified at pin v4.35.0-rc3 (`EnidsMathMadness/.lake/packages/mathlib`):
  `presheafHom`, `sheafHom`, `sheafHom'`, `Sheaf.homEquiv`, `J.overPullback`,
  `J.overMapPullback`, `Functor.whiskerLeft_id'`/`Functor.whiskerLeft_comp`
  (Whiskering.lean:180/193, namespace `CategoryTheory.Functor`),
  `NatTrans.ext`, `ConcreteCategory.ext`/`DFunLike.ext` and the scoped
  notation `↾` (needed because at this pin `Type` homs are `TypeCat.Hom`,
  Types/Basic.lean:89/140), `sheafPushforwardContinuousComp`
  (Continuous.lean:383), `Limits.prod.map_id_id`/`Limits.prod.map_comp_id`
  (BinaryProducts.lean:211/244), `CoreHomEquiv` + `Adjunction.mkOfHomEquiv`,
  `Adjunction.rightAdjointUniq` (Unique.lean:102), `IsLeftAdjoint`,
  `MonoidalClosed.internalHom`/`internalHomAdjunction₂` (Closed/Basic.lean:289/301),
  `tensorLeftIsoProd` (Cartesian/Basic.lean:800), `CategoryTheory.types
  : Category.{u} (Type u)`, `NatTrans : Type max u₁ v₂`. Universe corrections
  from the first build: presheaf-level hom types live in
  `Type (max (max u v) v')`, sheaf-level in `Type (max (max u v') v)`
  (`Over X : Type (max u v)`).
* **Honest proofs** (term-level, no banned tactics): `presheafHomPostcomp_id`,
  `presheafHomPostcomp_comp`, `presheafHomPrecomp_id`,
  `presheafHomPrecomp_comp`, `presheafHomFunctor` (laws from the previous
  four), `presheafHomBifunctor` `map_id`/`map_comp`, `prodWith` (both laws),
  `sheafHomProdHomEquiv` (assembly), `sheafTypesMonoidalClosed`
  (`inferInstance`), `prodWith_isLeftAdjoint`.
* **Sorries (14), each with a PEELING PLAN naming the next lemmas**:
  the four `naturality` fields of `presheafHomPostcomp` / `presheafHomPrecomp` /
  the two bifunctor `map` naturalities; the sheaf-level `naturality` fields of
  `sheafHomPostcomp` / `sheafHomPrecomp` and the `sheafHomFunctor` /
  `sheafHomBifunctor` laws (route: `Sheaf.homEquiv.injective` +
  `sheafPushforwardContinuousComp`); `sheafHomCurry`, `sheafHomUncurry`,
  `sheafHomUncurry_curry`, `sheafHomCurry_uncurry` (the componentwise
  construction is written out in the plans); the two
  `CoreHomEquiv` naturality fields of `sheafHomAdjunction`;
  `sheafHom_iso_internalHom` (route: `rightAdjointUniq` + `prod.braiding` +
  `tensorLeftIsoProd`).
* Style backstop run manually: all lines ≤ 100 columns; no banned tactic
  appears (only `funext` as a named term and `NatTrans.ext` as a named lemma,
  both allowed); every one of the 22 declarations carries a `-- Reference:`
  comment and a docstring; explicit binders throughout; header copied from
  `BoringMath/Foundations/Eta.lean`.
* Open questions for the human: (1) is `prodWith` (chosen products via
  `prod.map`) the right carrier for the left adjoint, or should the adjunction
  be stated with `MonoidalCategory.tensorRight F` (iso via `prod.braiding`)?
  (2) Peel (c) is already an `inferInstance` in Mathlib — is stating it here
  plus `sheafHom_iso_internalHom` the right scope, or should the instance be
  dropped and only the internal-hom identification kept?

## Progress note (peeling of the 14 deliberate sorries, ticket #41)

All 14 sorries of commit `fe53dfd` are now peeled; the module builds
warning-clean with **0 sorries** and `scripts/check-style.sh` reports
**0 violations** (all lines ≤ 100 columns).

New named lemmas added in the module (each with `-- Reference:` + docstring):

* Peel (a): `whiskerLeft_overMap_op_whiskerLeft_overForget_op` and
  `overMapPullback_map_overPullback_map` (primitive `rfl` coherences for
  `Over.map`/`Over.forget` and `overMapPullback`/`overPullback`, the latter
  via `sheafPushforwardContinuousComp` being an `Iso.refl`);
  `sheafHomPostcomp_id` / `_comp`, `sheafHomPrecomp_id` / `_comp`,
  `sheafHom_interchange` (the interchange law). The two presheaf naturality
  fields, the presheaf-bifunctor `map` naturality, the two sheaf naturality
  fields, `sheafHomFunctor.map_id` / `map_comp`, and the three
  `sheafHomBifunctor` fields are all proved from these via
  `ConcreteCategory.ext_apply`, `NatTrans.ext`, `DFunLike.ext`,
  `ObjectProperty.hom_ext`, `Functor.map_id` / `map_comp`,
  `Functor.whiskerLeft_comp`, and `Category.assoc`.
* Peel (b): `sheafProdIsoTensor` (`X ⨯ F ≅ X ⊗ F`, pointwise for sheaves of
  types) with its four `fst`/`snd` fac lemmas and `sheafProdMap_app`
  (pointwise formula for the transported `prod.map f (𝟙 F)`);
  `sheafHomCurryTensor` / `sheafHomCurrySection` / `sheafHomCurryVal` /
  `sheafHomUncurryVal` (the pointwise currying/uncurrying at presheaf level,
  routed through `sheafHom'Iso` so that `presheafHom_map_app` and
  `presheafHom_map_app_op_mk_id` apply); `sheafHomCurry` / `sheafHomUncurry`;
  the round trips `sheafHomUncurryVal_curry`, `sheafHomUncurry_curry`,
  `sheafHomCurryVal_uncurry`, `sheafHomCurry_uncurry`; the naturalities
  `sheafHomUncurryVal_naturality_left`, `sheafHomUncurry_naturality_left`,
  `sheafHomCurryVal_naturality_right`, `sheafHomCurry_naturality_right`;
  `sheafHomProdHomEquiv` (now `noncomputable`, since the chosen products enter)
  and `sheafHomAdjunction` (both `CoreHomEquiv` naturality fields proved).
* Peel (c): `prodWithIsoTensorLeft` (`prodWith F ≅ tensorLeft F` via
  `Limits.prod.braiding` + `tensorLeftIsoProd`), and
  `sheafHom_iso_internalHom` via `Adjunction.ofNatIsoLeft` +
  `Adjunction.rightAdjointUniq` against `(MonoidalClosed.closed F).adj`.

Notes: `sheafHomProdHomEquiv`, `sheafHomCurry`, `sheafHomUncurry` are now
`noncomputable` (content-forced: the chosen binary products enter through
`sheafProdIsoTensor`); each carries an inline comment saying so. One
justified `rw` (`natIso_hom_inv_app_apply`) uses a fully instantiated rule
with a uniqueness comment, per STYLE §2.1.
