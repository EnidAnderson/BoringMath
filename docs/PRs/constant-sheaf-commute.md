# Candidate PR: the constant sheaf commutes with pullback/pushforward of sheaves (`pr/sites-constant-sheaf-commute`)

Issue #43 (TREE H.9). Resolves, in a new module, the TODO in Mathlib
`CategoryTheory/Sites/ConstantSheaf.lean` (Equivalence section), quoted
verbatim in the issue:

> TODO: find suitable assumptions for proving generalizations of
> `equivCommuteConstant` and `equivCommuteConstant'` above, to commute
> `constantSheaf` with pullback/pushforward of sheaves.

Purely additive: one new module
`BoringMath/CategoryTheory/Sites/ConstantSheafCommute.lean` plus this note.
The upstream TODO comment is upstream's and is not edited.

## Verdict of the hypothesis hunt

* **Pullback side: the hunt succeeds.** Under purely site-theoretic
  hypotheses — `G : C ⥤ D` continuous (`Functor.IsContinuous G J K`), the
  sheaf pushforward `G.sheafPushforwardContinuous A J K` a right adjoint, and
  `G` taking a terminal object `T` of `C` to a terminal object of `D` — there
  is a natural isomorphism
  `constantSheaf J A ⋙ G.sheafPullback A J K ≅ constantSheaf K A`
  (`CategoryTheory.pullbackCommuteConstant`), proved by
  `Adjunction.leftAdjointUniq` exactly as in the in-file
  `equivCommuteConstant` (both sides are left adjoint to evaluation at
  `op T`, resp. `op (G.obj T)`; the two right adjoints agree definitionally
  because pushforward is precomposition with `G.op`).
* **Pushforward side: the hunt isolates an explicit obstruction (FINDING 1).**
  `constantSheaf K A ⋙ G.sheafPushforwardContinuous A J K ≅ constantSheaf J A`
  (`CategoryTheory.pushforwardCommuteConstant`) is proven under the explicit
  candidate hypothesis `hG` below, but `hG` is *not* implied by continuity
  (nor by cocontinuity/cover-lifting) in general.

## Statements (declaration list of the new module)

1. `CategoryTheory.pullbackCommuteConstant`
   `{C D A} [Category C] [Category D] [Category A] (J : GrothendieckTopology C)
   (K : GrothendieckTopology D) (G : C ⥤ D) [Functor.IsContinuous G J K]
   [HasWeakSheafify J A] [HasWeakSheafify K A]
   [(G.sheafPushforwardContinuous A J K).IsRightAdjoint]
   {T : C} (hT : IsTerminal T) (hT' : IsTerminal (G.obj T)) :
   constantSheaf J A ⋙ G.sheafPullback A J K ≅ constantSheaf K A`
   — fully proven, no sorry.
2. `CategoryTheory.pushforwardCommuteConstant`
   (same ambient variables, plus the explicit hypothesis)
   `(hG : presheafToSheaf K A ⋙ G.sheafPushforwardContinuous A J K ≅
   (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj G.op ⋙ presheafToSheaf J A) :
   constantSheaf K A ⋙ G.sheafPushforwardContinuous A J K ≅ constantSheaf J A`
   — fully proven from `hG`, no sorry. `hG` says: precomposition with `G.op`
   commutes with sheafification across the two topologies (sheafify on `K`,
   then push forward, equals push forward, then sheafify on `J`). The proof
   whiskers `hG` with the constant functor and closes with
   `Functor.constCompWhiskeringLeftIso` (`const ⋙ whiskeringLeft.obj G.op ≅
   const`).

## FINDING 1 (obstruction, pushforward side)

Continuity alone does not commute the constant sheaf with pushforward. At the
presheaf level the pushforward commutes with the constant *presheaf* on the
nose (`G.op ⋙ const ≅ const`), so the whole content is the commutation of
`G.op ⋙ –` with sheafification across `(K, J)` — exactly `hG`. For a
continuous map of topological spaces `f : X → Y` (so `G = f⁻¹` on opens),
`f_*` of the constant sheaf `A_X` is the sheaf `U ↦ {locally constant
f⁻¹(U) → A}`, which is `A_Y` only when the fibers of `f` are connected (and
`f` is surjective); a map with a disconnected fiber (e.g. two points mapping
to one point) gives `f_* A_X ≠ A_Y`. Mathlib has no instance deriving `hG`
from `Functor.IsContinuous`/`IsCocontinuous` (grep over
`Mathlib/CategoryTheory` at pin v4.35.0-rc3: the only
`PreservesSheafification` instances are for value-category functors `A ⥤ B`
— left adjoints, plus/plus-construction, and dense-subsite equivalences —
none of which is precomposition by a functor between *sites*). So the
candidate hypothesis set `{IsContinuous, IsCocontinuous, CoverPreserving}`
fails; the honest candidate is `hG` itself (or a fiber-connectedness
condition on `G`, not currently formalized in Mathlib). Recorded as a
finding, not silently absorbed into a weaker statement.

## Where this would live in Mathlib

Next to the TODO: `Mathlib/CategoryTheory/Sites/ConstantSheaf.lean`
(Equivalence section), with the pullback iso alternatively in
`Mathlib/CategoryTheory/Sites/Pullback.lean` beside `sheafPullbackIso`.

## Does Mathlib already have it?

No. At pin v4.35.0-rc3 the commutation of `constantSheaf` with pullback/
pushforward of sheaves exists only for
* dense subsites (`equivCommuteConstant`, `equivCommuteConstant'`, via
  `sheafEquiv`), and
* value-category postcomposition (`constantCommuteCompose`, needing
  `J.PreservesSheafification U` and `J.HasSheafCompose U` for `U : D ⥤ B`).
`Sites/LocalSite.lean` has the dual `coconstantSheaf` for local sites, not
this commutation. The TODO quoted above is open upstream.

## Literature

* SGA 4, Exposé III, *Fonctorialité des catégories de faisceaux* (J.-L.
  Verdier), §1 — morphisms of sites, `f*`/`f_*` on sheaf categories; the
  constant-sheaf behavior is the fiber-connectedness discussion.
  REVIEW(citation): exposé/section verified via web mirrors of SGA 4
  (normalesup.org, fabrice.orgogozo); the exact proposition number is not
  pinned. Citation-pin resolution is owned by W5 (#13) per issue #43.
* Stacks Project, chapter *Sites and Sheaves*, Section 14 "Morphisms of
  sites" (tag 00X0) — web-verified; chapter *Étale Cohomology*, Section 64
  "Locally constant sheaves" (tag 09Y8) — web-verified, for constant sheaves
  on sites.
* D. Asgeirsson, `Mathlib.CategoryTheory.Sites.ConstantSheaf` (the file
  anchor named in the issue): `constantSheaf`, `constantSheafAdj`,
  `equivCommuteConstant`, and the TODO.

## Verification (this branch)

* `lake build BoringMath.CategoryTheory.Sites.ConstantSheafCommute` —
  success, warning-clean (recompiled from scratch; no warnings, no sorries).
* `bash scripts/check-style.sh BoringMath/CategoryTheory/Sites/ConstantSheafCommute.lean`
  — 0 violations, 0 sorries.
* All mathlib names used (`sheafPullback`, `sheafAdjunctionContinuous`,
  `sheafPushforwardContinuous`, `sheafSections`, `constantSheafAdj`,
  `leftAdjointUniq`, `Functor.associator`, `Functor.isoWhiskerLeft/Right`,
  `Functor.constCompWhiskeringLeftIso`, `presheafToSheaf`,
  `Functor.whiskeringLeft`) were grepped in the pinned mathlib checkout
  (v4.35.0-rc3) before use.

## Open questions for the human

1. Should the dual statement for the cocontinuous pushforward
   (`G.sheafPushforwardCocontinuous`, right Kan extension along `G.op`,
   `Sites/CoverLifting.lean`) also be stated? It needs the analogous
   ran-side hypothesis and was left out of scope.
2. Is the explicit iso hypothesis `hG` the right packaging, or should a
   Prop-level W-condition candidate (`K.W ≤ J.W.inverseImage
   (whiskeringLeft.obj G.op)`-style) be stated as a separate declaration?
3. REVIEW(citation) tags on the SGA 4 Exposé III proposition numbers remain
   for W5 (#13).
