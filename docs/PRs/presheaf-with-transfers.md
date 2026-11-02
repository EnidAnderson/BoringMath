# Candidate PR: presheaves with transfers (C.3, #25)

Branch: `pr/correspondence-presheaf` (proposed). Module:
`BoringMath/AlgebraicGeometry/Correspondence/Presheaf.lean` (new; imports
`Correspondence/SmCor.lean`).

## Statement

* `smoothOverCategory : Category.{u} (SmoothSchemeOver S)` — the smooth site
  `Sm/S`: morphisms are the `S`-morphisms (a subtype of scheme morphisms).
* `graphFunctor : SmoothSchemeOver S ⥤ SmCor S` — the graph construction; its
  functoriality is `graphFiniteCorrespondence_comp` (C.2, sorried there) and
  the landed cycle-level `graphCorrespondence_comp` (PR #72).
* `PresheafWithTransfer S` — structure with explicit data per STYLE §2.3: the
  functor `toFunctor : (SmCor S)ᵒᵖ ⥤ AddCommGrpCat` plus the `additive`
  field. The transfer along `c : X ⇸ Y` is `toFunctor.map (op c)`.
* Laws (named): `transfer_add` (transfers additive in the correspondence —
  the `additive` field, via `Functor.map_add`), `transfer_comp` (transfers
  compose with correspondence composition — functoriality),
  `toPresheaf_map_graph` + `graphFunctor_map` + `graphFunctor_op_map`
  (transfers restrict to the underlying presheaf's action on morphisms when
  the correspondence is a graph — primitive definitional lemmas, rfl).
* `PresheafWithTransfer.toPresheaf` — the underlying presheaf on `Sm/S`
  (precomposition along the graph functor); `forgetful` — the forgetful
  functor on the presheaf categories via `Functor.whiskeringLeft`.
* `PresheafWithTransfer.zTr X` — the representable `ℤ_tr(X) = Hom_{SmCor}(-, X)`
  (preadditive Yoneda), with `zTr_obj : zTr(X)(op Y) = AddCommGrpCat.of (Y ⟶ X)`
  (rfl) — `Y ↦` the finite correspondences `Y ⇸ X`, i.e. zero-cycles on
  `X ×_S Y` finite over `Y`, exactly the #25 clause (2).

Out of scope per #25: the DM-side axioms (homotopy invariance, Mayer–Vietoris)
— they are C.4.

## Literature

* MVW (2006), Lecture 2 "Presheaves with transfers" (p. 13; TOC
  web-verified). REVIEW(citation): exact definition numbers.
* Voevodsky–Suslin–Friedlander, *Cycles, Transfers, and Motivic Homology
  Theories*, Annals of Math. Studies 143, Princeton Univ. Press, 2000,
  definitions chapter. REVIEW(citation): chapter/section to be pinned.

## Where it would live in Mathlib

`Mathlib/AlgebraicGeometry/Correspondence/Presheaf.lean` (new directory at the
pin).

## Does Mathlib already have it?

No. No presheaves-with-transfers anywhere in `Mathlib/` at the pin
(foundation-audit GOLD in #25); sheaf/presheaf machinery on sites is mature
and is used as-is.

## Review notes

* Build: warning-clean, zero sorries; check-style 0 violations.
* Computability: `PresheafWithTransfer` takes the functor explicitly (no
  instance-chosen data, STYLE §2.3); `zTr`/`graphFunctor`/`forgetful` are
  `noncomputable` because the `SmCor` instance is choice-backed, flagged.
