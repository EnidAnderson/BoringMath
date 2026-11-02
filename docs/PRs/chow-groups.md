# Candidate PR: rational equivalence and the Chow groups `A_*(X)` (I.1, #281)

Branch: `pr/algebraic-cycle-chow` (proposed). Modules:
`BoringMath/AlgebraicGeometry/AlgebraicCycle/RationalEquivalence.lean`,
`BoringMath/AlgebraicGeometry/AlgebraicCycle/ChowGroup.lean`, and the small
`BoringMath/AlgebraicGeometry/Scheme/Hom.lean` (moved `Scheme.id_apply` →
`Scheme.Hom.id_apply`, next to mathlib's `Scheme.Hom.comp_apply`;
`Correspondence/Finite.lean` updated to import it).

## Statement

* `specZ`, `affineLine` (`𝔸¹ = Spec ℤ[t]`), `affineLineProj`, the zero/one
  sections `affineLineZero`/`affineLineOne` with `affineLineZero_proj`/
  `affineLineOne_proj` (proved by terminal uniqueness), `prodAffineLine X`
  (`X × 𝔸¹` over `Spec ℤ`), `sectionIncl` with `sectionIncl_fst`.
* `section_injective` — a section is injective on points (retraction law).
* `sectionPullback i r h γ` — pullback of a cycle along a section:
  precomposition on points, well defined because the section is injective
  (support stays locally finite); laws `sectionPullback_zero`/`_add` and the
  bundled `sectionPullbackHom : →+`.
* `rationalEquivalenceHom X : Z_*(X × 𝔸¹) →+ Z_*(X)`, `γ ↦ i₀*γ - i₁*γ`, with
  the primitive `rationalEquivalenceHom_apply`; `rationalEquivalenceAddSubgroup X`
  := its range.
* `chowGroup X := Z_*(X) ⧸ rationalEquivalenceAddSubgroup X` (AddCommGroup),
  `chowClass X : Z_*(X) →+ A_*(X)`, and **`chowClass_eq_iff`**: same class iff
  `c - d = i₀*γ - i₁*γ` for some `γ` on `X × 𝔸¹`.

All sorry-free.

## Scope notes / named peels

* Structure-of-record = the A¹-family presentation of rational equivalence
  (multiple-presentations directive, cf. the ratified C.1 ruling). The
  equivalence with Fulton's div-of-rational-functions definition (Fulton ch. 1,
  §1.3; the P¹-family characterization ch. 10) is the named Tier-2 peel —
  needs Weil divisors on integral closed subschemes (absent at pin).
* Graded pieces `A_k(X)` by support dimension and functoriality on Chow groups
  are I.2 (#283), not here.

## Literature

* W. Fulton, *Intersection Theory*, 2nd ed., Springer 1998, ch. 1, §1.3
  (rational equivalence), ch. 10 (family characterization — REVIEW(citation):
  pin Prop. 10.3? in review).
* Stacks Project, Chow Homology, Def. 42.8.1 (tag 02QR), rational equivalence
  tags 02R9 ff. — REVIEW(citation): pin tags.
* Hartshorne, *Algebraic Geometry*, GTM 52, App. A, §1 — REVIEW(citation).

## Where it would live in Mathlib

`Mathlib/AlgebraicGeometry/AlgebraicCycle/RationalEquivalence.lean` and
`.../ChowGroup.lean`, extending the existing single-file
`Mathlib/AlgebraicGeometry/AlgebraicCycle/Basic.lean`; plus
`Scheme.Hom.id_apply` in `Mathlib/AlgebraicGeometry/Scheme.lean`.

## Does Mathlib already have it?

No — grep-verified 2026-11-02: `AlgebraicCycle/` is a single `Basic.lean`
(cycles + weighted `map`); no rational equivalence, no Chow groups.

## Review notes

* Build: `lake build` of all touched modules warning-clean, zero sorries;
  check-style 0 violations on `BoringMath/AlgebraicGeometry/`.
* Computability: `sectionPullback` is computable (precomposition); the
  product/subgroup/class map are `noncomputable` (chosen fiber product), each
  flagged inline per STYLE §2.3.
* Feeds: I.2 (#283) functoriality, I.5 (#290) Chow ring, G.2 (#289) pure Chow
  motives, and (via the fiber-product cycle) C.2 (#24) composition.
