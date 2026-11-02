# Candidate PR: the A¹-station and `DM^eff` (C.4, #117) — statement layer

Branches: `pr/motives-a1` and `pr/motives-dm` (proposed). Modules:
`BoringMath/AlgebraicGeometry/Motives/A1.lean` and
`BoringMath/AlgebraicGeometry/Motives/DM.lean` (new directory
`AlgebraicGeometry/Motives/`, the mathlib-mirror path for motives; no such
directory exists in `Mathlib/` at the pin).

## Statement

`Motives/A1.lean`:

* `affineLineOver S := 𝔸(ULift.{u} Unit; S)`, `affineLineProj S := 𝔸(...) ↘ S`
  (mathlib's `AffineSpace`; the projection is smooth at the pin by the
  `SmoothOfRelativeDimension` instances).
* `smCorAffineLineProduct X` — `X ×_S 𝔸¹` as a `SmCor` object: smoothness is
  PROVED (base change + composition of `Smooth`); separatedness and
  Noetherianness are SORRIED Tier-2 peels with plans
  (`isSeparated_fst_affineLineProj_comp`, `isNoetherian_pullback_affineLineProj`).
* `affineLineProductIncl pt hpt` — the inclusion `X × {pt} → X ×_S 𝔸¹` from a
  section `pt : S ⟶ 𝔸¹_S`, with the over-`S` law proved
  (`affineLineProductIncl_over`).
* `correspondenceRestrict g hg c` — restriction of a correspondence along an
  `S`-morphism (precomposition with the graph).
* `IsA1Homotopic pt₀ pt₁ c d` — **A¹-homotopy of finite correspondences** (MVW:
  restrictions along `X × {pt₀}`, `X × {pt₁}` of one correspondence on
  `X ×_S 𝔸¹`); `refl`/`symm`/`trans` SORRIED with peeling plans.

`Motives/DM.lean`:

* `forgetSmoothOver`, `nisnevichTopologySmOver S` — the Nisnevich topology on
  `Sm/S`, pulled back from the landed big Nisnevich site (B.2, #9) via
  `Functor.restrictedTopology`; the intrinsic small site over `S` is the
  B-line Tier-2 target (recorded).
* `IsNisnevichSheafWithTransfers F` — MVW's criterion: the underlying presheaf
  on `Sm/S` is a Nisnevich sheaf; `NisnevichSheafWithTransfers S` — the full
  subcategory of presheaves on `SmCor(S)`.
* `smCorAffineLineProj`, `a1Projection X` — the A¹-projection morphism of
  representables `ℤ_tr(X ×_S 𝔸¹) ⟶ ℤ_tr(X)`.
* `EffectiveMotiveCategory S` — the DM^eff localization datum (hypotheses as
  structure fields, no `axiom` decls, per #117): sheafification functor,
  A¹-class `W` containing the sheafified A¹-projections.
* `dmEff D := D.W.Localization` — **`DM^eff(S)`** as the Gabriel–Zisman
  localization of Nisnevich sheaves with transfers at the A¹-class.
* `a1Projection_isIso_dmEff` — PROVED: the A¹-projection is invertible in
  `DM^eff` (the construction's `wIso`).
* `dmEff_lift` — PROVED: universal property (`Localization.lift`).
* Named next peels (recorded in the module, not sorried): the triangulated
  Verdier form of the localization sequence (rides T.1/#23 + B.4/#26), Day
  convolution tensor structure, the Tate object `ℚ(1)` as the reduced motive of
  `(P¹, ∞)`, and the cancellation theorem.

## Shape ledger (oracle, #117 acceptance 4)

Filed as `docs/AUDITS/2026-11-02-dm-eff-shape-ledger.md`. Naive form (trap):
motives as pieces of varieties / value-level. Right home: the localization of
PWT(Nis) at A¹ — here landed in the 1-categorical Gabriel–Zisman form with the
triangulated Verdier form as named supersession (the ∞-categorical upgrade
likewise). Extraction: realizations as additive functors out — named later
peel. Mathlib audit at pin: A¹-localization ABSENT; `CategoryTheory.Localization`
(Gabriel–Zisman) PRESENT and used; `derivedCategory` ABSENT.

## Literature

* Voevodsky, *Three Lectures on Motivic Cohomology*, MPI Bonn (2000),
  Def. 2.4 (`DM^eff(k)` = localization of `D(NST(k))` at the A¹-cones).
  REVIEW(citation): preprint number. Web-verified text of Def. 2.4 this session.
* MVW (2006), Lectures 11–14 (Nisnevich sheaves with transfers; `DM`).
  REVIEW(citation): lectures/sections. A¹-homotopy definition web-verified in
  the TOC/front matter ("restrictions along `X × 0` and `X × 1`").
* Voevodsky, *A¹-homotopy theory*, DMV Seminar 48 (2000). REVIEW(citation).
* Voevodsky, *Homotopy theory of simplicial sheaves in completely decomposable
  topologies*, JPAA 214 (2010), 1399–1406, §2 (Nisnevich cd-structure) — the
  landed B.2 anchor.

## Review notes

* Builds: `lake build ...Motives.A1 ...Motives.DM` warning-clean except the 5
  deliberate sorry-warnings in A1.lean (each with peeling plan); check-style 0
  violations on both directories.
* Gating honesty: C.4's gates (#24 C.2, #25 C.3, #30 B.5, #23 T.1) are all
  landed or statement-layered now; the B.5 small-Nisnevich-site refinement and
  the triangulated upgrade remain named Tier-2 peels, recorded above.
