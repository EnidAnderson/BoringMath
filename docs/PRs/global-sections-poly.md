# Candidate PR: universe-polymorphic global sections (TREE H.10, #44)

## Statement

One new module `BoringMath/CategoryTheory/Sites/GlobalSectionsPoly.lean`,
addressing the TODO in the module docstring of
`Mathlib/CategoryTheory/Sites/GlobalSections.lean` (Eltschig), quoted verbatim
in issue #44:

> TODO: Generalise `Sheaf.ΓNatIsoSectionsFunctor` and
> `Sheaf.ΓNatIsoCoyoneda` from `Type max u v` to `Type max u v w`. This should
> hopefully be doable by relaxing the universe constraints of
> `instHasSheafifyOfHasFiniteLimits`.

Per the coordination flag (binding), the route is **purely additive** — the
TODO's own route would edit an existing instance, which is not allowed. The
module contains exactly three declarations:

* `instance hasWeakSheafify_types_of_hasFiniteLimits_of_small_covers`
  — a **new** instance `HasWeakSheafify J (Type (max u v w))` at general
  universes, under an explicit finite-limits hypothesis
  `[Limits.HasFiniteLimits (Type (max u v w))]` and an explicit smallness
  hypothesis `[∀ X : C, Small.{max u v w, max u v} (J.Cover X)ᵒᵖ]`, mirroring
  the hypothesis shape of Mathlib's `HasSheafify` instance for concrete
  categories. Proof: `HasSheafify.mk'` applied to `plusPlusAdjunction`, then
  the `isRightAdjoint` field.
* `Sheaf.ΓNatIsoSectionsFunctorPoly` — the global sections functor
  `Sheaf.Γ J (Type (max u v w))` is naturally isomorphic to
  `sheafToPresheaf J _ ⋙ Functor.sectionsFunctor _`, generalizing
  `Sheaf.ΓNatIsoSectionsFunctor` from `Type (max u v)` to `Type (max u v w)`.
* `Sheaf.ΓNatIsoCoyonedaPoly (X : Type (max u v w)) [Unique X]` — the global
  sections functor is naturally isomorphic to
  `coyoneda.obj (op ((constantSheaf J (Type (max u v w))).obj X))`,
  generalizing `Sheaf.ΓNatIsoCoyoneda` from `Type (max u v)` to
  `Type (max u v w)`.

Both isomorphisms are proved by `NatIso.ofComponents` from the
universe-polymorphic component equivalences `Sheaf.ΓObjEquivSections` /
`Sheaf.ΓObjEquivHom` (already stated at `Type w` in Mathlib with an explicit
`[HasWeakSheafify J (Type w)]` hypothesis), with naturality closed by the
named extensionality lemma `ConcreteCategory.ext_apply` and the naturality
lemmas `Sheaf.ΓObjEquivSections_naturality` / `Sheaf.ΓObjEquivHom_naturality`.
No `sorry`, no banned tactic; the two `ext x` steps of the upstream proofs are
replaced by the named lemma `ConcreteCategory.ext_apply`.

## Literature

* [Eltschig] B. Eltschig, `Mathlib/CategoryTheory.Sites.GlobalSections` (2025)
  — the TODO anchor, read in full at the pin (GOLD).
* [Stacks] The Stacks Project, Chapter 7 "Sites and Sheaves" (tag 00UZ,
  chapter verified by web search) — sheafification and sheaf Hom.
  `REVIEW(citation)` (section pins owned by W5/#13 per the issue).
* [MM] S. Mac Lane, I. Moerdijk, *Sheaves in Geometry and Logic*, Springer,
  1992, Chapter III (the associated sheaf functor). `REVIEW(citation)`.
* [Mac Lane] S. Mac Lane, *Categories for the Working Mathematician*, 2nd ed.,
  Springer, 1998, Chapter IV (adjoints). `REVIEW(citation)`.

## Where it would live in Mathlib

`Mathlib/CategoryTheory/Sites/GlobalSections.lean` itself, directly
extending Eltschig's file (which this module imports); the new instance would
sit next to `Mathlib/CategoryTheory/Sites/LeftExact.lean`'s
`HasSheafify J (Type (max u v))` instance.

## Does Mathlib already have it?

* The two natural isomorphisms at `Type (max u v)`: **yes** —
  `Sheaf.ΓNatIsoSectionsFunctor` and `Sheaf.ΓNatIsoCoyoneda`
  (`Sites/GlobalSections.lean`, pin v4.35.0-rc3). At `Type (max u v w)` with
  general `w`: **no** — that is exactly the TODO.
* `HasWeakSheafify J (Type (max u v w))` at general `w`: **yes, unconditionally
  at the pin** — the priority-900 instance `sheafToPresheaf_isRightAdjoint`
  (`Sites/ConcreteSheafification.lean`) has only concrete-category hypotheses,
  all of which are instances for `Type (max u v w)` (probed: `example :
  HasWeakSheafify J (Type (max u v w)) := by infer_instance` succeeds with no
  hypotheses). The strong `HasSheafify J (Type (max u v w))` needs
  `Small.{max u v w, max u v} (J.Cover X)ᵒᵖ`, which is not an instance at
  general `w` (probed: it fails without the hypothesis, succeeds with it).

## GOLD verification at pin v4.35.0-rc3

Mathlib checkout `EnidsMathMadness/.lake/packages/mathlib`, commit `c55e6e78`
("chore: bump toolchain to v4.35.0-rc3"), `lean-toolchain`
`leanprover/lean4:v4.35.0-rc3`:

* `instHasSheafifyOfHasFiniteLimits` (the TODO's name) appears only in the
  TODO comment (`Sites/GlobalSections.lean:43`); the actual instance is the
  anonymous `instance [PreservesLimits (forget D)] [HasFiniteLimits D]
  [∀ X : C, Small.{t, max u v} (J.Cover X)ᵒᵖ] : HasSheafify J D` at
  `Sites/LeftExact.lean:307-311`, with `universe s t w' w v u`,
  `variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}` and
  `variable {D : Type w} [Category.{t} D]` plus the concrete-category section
  variables (lines 244-251). `HasSheafify J (Type (max u v))` is the instance
  at `LeftExact.lean:313`.
* `J.Cover X : Type (max u v)` — `Sites/Grothendieck.lean:421`.
* `HasWeakSheafify` is `abbrev HasWeakSheafify : Prop :=
  (sheafToPresheaf J A).IsRightAdjoint`; `IsRightAdjoint` is a `Prop` class
  (`Adjunction/Basic.lean:138`) — so overlapping instances are proof-irrelevant
  and cannot diamond.
* Names used, all verified in the checkout: `Sheaf.Γ`, `HasGlobalSectionsFunctor`,
  `Sheaf.ΓObjEquivSections`, `Sheaf.ΓObjEquivSections_naturality`,
  `Sheaf.ΓObjEquivHom`, `Sheaf.ΓObjEquivHom_naturality`, `sheafToPresheaf`,
  `Functor.sectionsFunctor`, `constantSheaf`, `coyoneda`, `NatIso.ofComponents`,
  `ConcreteCategory.ext_apply` (`ConcreteCategory/Basic.lean:144`),
  `HasSheafify`, `HasSheafify.mk'`, `plusPlusAdjunction`,
  `Limits.HasFiniteLimits`, `Small` (a `class`, `Logic/Small/Defs.lean:37`),
  `preservesFiniteLimits_presheafToSheaf` (the instance discharging
  `PreservesFiniteLimits (plusPlusSheaf J D)` from the explicit hypotheses).

## Collision check (the STOP condition of issue #44)

**Not triggered.** With the new instance declared, probes confirm:
`HasWeakSheafify J (Type (max u v))` and `HasSheafify J (Type (max u v))` still
synthesize at the overlapping universe `max u v w = max u v` (there
`Small.{max u v, max u v} (J.Cover X)ᵒᵖ` is `small_self` and finite limits are
instances, so the new instance applies alongside the `HasSheafify`-derived
one); and `HasWeakSheafify J (Type (max u v w))` still synthesizes with no
hypotheses at general `w` (the priority-900 concrete instance). Since
`HasWeakSheafify` is a `Prop`, any overlap is defeq by proof irrelevance; the
module builds warning-clean with all four probes. No instance diamond, no
defeq failure — the additive route stands.

## Review notes

* Purely additive: one new module + this note, per the modular fast-forward
  protocol. No existing file touched; no commit; no branch switch.
* **Build (machine-on)**: `lake build
  BoringMath.CategoryTheory.Sites.GlobalSectionsPoly` — `Build completed
  successfully`, warning-clean (no sorries, no linter warnings).
  `bash scripts/check-style.sh
  BoringMath/CategoryTheory/Sites/GlobalSectionsPoly.lean` —
  `0 violation(s), 0 sorry(s)`. All lines ≤ 100 columns; header copied from
  `BoringMath/Foundations/Eta.lean`; imports name specific modules only;
  every declaration carries a `-- Reference:` comment (within 12 lines) and a
  docstring; explicit binders throughout.
* **Sorries: none.** All three proofs are exact term proofs.
* Findings for the human: (1) at the pin the weak sheafification of types at
  `Type (max u v w)` is already unconditional (priority-900 instance), so the
  two generalized isomorphisms are stated with no extra hypotheses — the
  strongest form; the new instance is still provided per the coordination flag
  for the explicit finite-limits route and for downstream use. (2) The TODO's
  suggested route (relaxing `instHasSheafifyOfHasFiniteLimits`) is only needed
  for the *left-exact* `HasSheafify` at general `w`, not for the two `Γ`
  isomorphisms, which need only `HasWeakSheafify`.
* Open questions for the human: (1) should the two `*Poly` isomorphisms instead
  take `[HasWeakSheafify J (Type (max u v w))]` as an explicit binder, matching
  the style of `Sheaf.ΓObjEquivSections` / `Sheaf.ΓObjEquivHom`, rather than
  relying on instance synthesis? (2) Is the `Poly` suffix the right naming, or
  should the generalized versions be named e.g. `...Max` to mark the
  `max u v w` universe?
