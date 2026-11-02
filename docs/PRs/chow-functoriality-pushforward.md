# Candidate PR: pushforward on Chow groups `f_* : A_*(X) → A_*(Y)` (I.2 part 1, #283)

Branch: `pr/algebraic-cycle-chow-functoriality` (proposed). Module:
`BoringMath/AlgebraicGeometry/AlgebraicCycle/ChowFunctoriality.lean` (new).

## Statement

* `prodMapAffineLine f : X × 𝔸¹ ⟶ Y × 𝔸¹` (the map `(x, t) ↦ (f x, t)`), with
  the projection laws `prodMapAffineLine_fst`/`_snd` (proved) and
  `sectionIncl_prodMap` (`i_t ≫ (f × 𝔸¹) = f ≫ i_t`, proved by the pullback
  universal property).
* `quasiCompact_prodMapAffineLine` — SORRIED Tier-2 peel (pullback stability
  of `QuasiCompact`; plan names `MorphismProperty.pullback_fst`).
* `pushforward_sectionPullback` — `f_*(i_t*γ) = i_t'*((f × 𝔸¹)_*γ)` — SORRIED
  Tier-2 peel; plan names the pointwise fiber-sum bijection (`x ↦ i_t x`,
  `pushforward_apply`) and the residue-degree base-change equality
  (`residueFieldMap_comp` + `sectionIncl_fst` + finrank under algebra isos).
* `pushforward_mem_rationalEquivalence` — PROVED from the above: the
  cycle-level pushforward carries the rational-equivalence subgroup of `X`
  into that of `Y`.
* `chowPushforward f : chowGroup X →+ chowGroup Y` — the pushforward on Chow
  groups (quotient lift), with `chowPushforward_mk` (primitive rfl):
  `f_* [c] = [f_* c]`.

Out of scope here (I.2 part 2, named peel): the **flat pullback** `f*` on
Chow groups — needs the flat pullback of general cycles (Serre intersection
multiplicities beyond the landed reduced `fiberCycle`).

## Literature

* Fulton, *Intersection Theory*, 2nd ed., Springer 1998, ch. 1, §1.4
  (pushforward on Chow groups). REVIEW(citation): pin the proposition.
* Stacks Project, Chow Homology, §42.12 (proper pushforward; tag 02R5 is the
  composition law), rational-equivalence compatibility tags 02R9 ff.
  REVIEW(citation): pin the tags.
* Hartshorne, GTM 52, App. A, §1-2. REVIEW(citation).
* Local reference PDF: `refs/eisenbud-harris-3264-final-draft.pdf` (3264 final
  draft, ch. 3? — the pushforward; REVIEW(citation)) and
  `refs/mvw-lecture-notes-motivic-cohomology.pdf` (MVW, downloaded
  2026-11-02 from claymath.org).

## Where it would live in Mathlib

`Mathlib/AlgebraicGeometry/AlgebraicCycle/ChowFunctoriality.lean`, extending
the `AlgebraicCycle/` directory.

## Does Mathlib already have it?

No — Chow groups themselves don't exist at the pin (see the I.1 PR note).

## Review notes

* Build: warning-clean except the 2 deliberate sorry-warnings (each with a
  TEMPORARY SORRY + peeling plan); check-style 0 violations on the
  AlgebraicCycle + Scheme directories.
* Feeds: I.5 (#290) Chow ring (needs the projection formula next), G.2 (#289)
  Chow motives (composition of correspondences = pushforward of products),
  C.2 (#24).
