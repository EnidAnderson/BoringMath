# Candidate PR: the correspondence category `SmCor(S)` (C.2, #24)

Branch: `pr/correspondence-smcor` (proposed). Module:
`BoringMath/AlgebraicGeometry/Correspondence/SmCor.lean` (new; imports
`Correspondence/Finite.lean`).

## Statement

* `SmoothSchemeOver S` — objects: `carrier`, `proj`, `smooth : Smooth proj`,
  `separated : IsSeparated proj`, `noetherian : IsNoetherian carrier`.
* `SmCorObj S` / `SmCor S` — the object type of the correspondence category.
* `quasiCompact_graph_of_isSeparated` — the graph into a separated target is
  quasicompact (pullback of the diagonal). SORRIED, Tier-2 peel with plan:
  graph square as `IsPullback`, `IsClosedImmersion.pullback`, closed
  immersion ⇒ quasicompact, quasicompactness stable under pullback.
* `correspondenceComp` — the **Suslin–Voevodsky composition**
  `d ∘ c = (pr₁₃)_* (pr₁₂^* c · pr₂₃^* d)` on the triple fiber product.
  SORRIED, statement layer: peeling plan names the landed consumers
  (`pushforward_comp`, `pushforward_add`, `pushforward_single`,
  `Scheme.Hom.residueDegree_comp`, `AlgebraicCycle.fiberCycle`) and the ONE
  missing substrate: the intersection product / fiber-product cycle of two
  cycles on `X ×_S Y ×_S Z` (Fulton ch. 1–6 vicinity) — the C-line's first
  genuinely Tier 2–3 peel, recorded as an obstruction per #24.
* `identityCorrespondence` — the graph of the identity.
* Laws `correspondenceComp_identityCorrespondence_left/right`,
  `correspondenceComp_assoc`, `correspondenceComp_add_left/right` — all
  SORRIED with peeling plans through `correspondenceComp`.
* `graphFiniteCorrespondence_comp` — **graphs compose to graphs** (the #24
  acceptance criterion) at the finite-correspondence level; SORRIED, reduces
  to the landed sorry-free `graphCorrespondence_comp` (PR #72) via
  `graphFiniteCorrespondence_toCycle` + `FiniteCorrespondence.ext_iff`.
* `smCorCategory : Category.{u} (SmCor S)` — the category instance over C.1's
  structure-of-record, stated ONCE per the human ruling (alternative
  presentations enter later as named lemmas, never as a second instance).
* `smCorPreadditive : Preadditive (SmCor S)` — hom groups are the C.1
  `AddCommGroup`s, composition bilinear via the sorried laws.

## Literature

* MVW (2006), Appendix 1A "The category Cor_S" (p. 7; TOC web-verified):
  composition, identity, the additive structure. REVIEW(citation): exact
  proposition numbers.
* Suslin–Voevodsky (1996), the composition formula `(pr₁₃)_*(pr₁₂^*c · pr₂₃^*d)`.
  REVIEW(citation): section to be pinned.
* Voevodsky, *A¹-homotopy theory*, DMV Seminar 48 (2000), correspondences
  section. REVIEW(citation).

## Where it would live in Mathlib

`Mathlib/AlgebraicGeometry/Correspondence/SmCor.lean` (new directory at the
pin, same as `Graph.lean`).

## Does Mathlib already have it?

No. No `SmCor`/`Cor`/finite-correspondence category anywhere in `Mathlib/` at
the pin (grep-verified in C.1/C.2 prep).

## Review notes

* Build: `lake build ...SmCor` warning-clean except the 10 deliberate
  sorry-warnings (each with a TEMPORARY SORRY + peeling plan); check-style 0
  violations.
* `noncomputable` on the category/preadditive instances: the identity
  correspondence is choice-backed (fundamental cycle), flagged inline.
