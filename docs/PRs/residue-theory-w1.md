# Candidate PR: residue theory W.1 — section residue-field isos and residue degrees

**Line:** W.1 (tickets #358–#361 area; supports I.2 #283)
**Files:**
- `BoringMath/AlgebraicGeometry/ResidueTheory/Basic.lean` (new)
- `BoringMath/AlgebraicGeometry/AlgebraicCycle/ChowFunctoriality.lean` (refactor + one lemma proved)

**Statement.** For a section `i : X ⟶ W` with retraction `r` (`i ≫ r = 𝟙 X`):
- `section_point_retraction`: `r (i x) = x` (proved);
- `residueFieldMap_section_split`: `i.residueFieldMap x (r.residueFieldMap (i x) ((X.residueFieldCongr …).inv y)) = y` — **proved** from `Scheme.residueFieldMap_comp` + `Scheme.Hom.residueFieldMap_congr` + `Scheme.residueFieldMap_id`, closing via `Scheme.residueFieldCongr_trans_hom` and proof irrelevance;
- `isIso_residueFieldMap_section`: the section's residue-field map is an iso — **proved**;
- `finrank_residueField_of_residueFieldMap_isIso` / `residueDegree_of_residueFieldMap_isIso` / `residueDegree_section`: the residue degree of a section is 1 — **proved** (`LinearEquiv.finrank_eq` + `CommSemiring.finrank_self`).

In `ChowFunctoriality.lean` the local copies of the section lemmas were replaced
by the W.1 import, and **`residueDegree_prodMap_sectionIncl` is proved**: the
section square `i_t ≫ (f × 𝔸¹) = f ≫ i_t'` gives a commutative square of
residue-field maps, the section maps are isos (W.1), and
`Algebra.finrank_eq_of_equiv_equiv` transports the finrank.

**Remaining hole (named, peeling plan in-file):** `pushforward_sectionPullback`
(fiber bijection `x ↦ i_t x` between the fibers; needs point-extensionality on
the `t`-slice via `Scheme.Pullback.carrierEquiv` + field-ness of the tensor
along a section; summand equality already available from
`residueDegree_prodMap_sectionIncl`).

**Literature.** Stacks Project tags 01HX ff. (residue fields/degrees of morphisms
of schemes; REVIEW: pin tags); Fulton, *Intersection Theory*, ch. 1, §1.4
(base change along sections); Serre, *Local Fields*, ch. II.

**Mathlib status at pin v4.35.0-rc3.** `Scheme.Hom.residueFieldMap`,
`residueDegree`, `residueFieldCongr`, `Scheme.Pullback.carrierEquiv` exist;
the section lemmas above are new.
