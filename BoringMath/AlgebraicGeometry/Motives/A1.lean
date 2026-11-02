/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringMath.AlgebraicGeometry.Correspondence.Presheaf
import Mathlib.AlgebraicGeometry.AffineSpace

/-!
# The affine line and A¹-homotopy of correspondences (C.4 station, part 1)

The affine line `𝔸¹_S` over the base, its product `X ×_S 𝔸¹` as an object of
`SmCor(S)`, the restriction of a finite correspondence along an `S`-morphism
(precomposition with the graph), and **A¹-homotopy of correspondences**: two
finite correspondences `c, d : X ⇸ Y` are A¹-homotopic when they are the
restrictions along the two sections `X × {pt₀} → X ×_S 𝔸¹` and
`X × {pt₁} → X ×_S 𝔸¹` of one correspondence on `X ×_S 𝔸¹`. This is the
relation whose localization builds `DM^eff` (C.4, #117).

Statement layer (Tier 1): the product's separatedness/Noetherianness and the
equivalence-relation laws are sorried with peeling plans; the smoothness of
the product projection rides the pin's instances (smoothness is stable under
base change and composition, `Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean`).

## References
* C. Mazza, V. Voevodsky, C. Weibel, *Lecture Notes on Motivic Cohomology*,
  Clay Mathematics Monographs 2, Amer. Math. Soc. / Clay Math. Inst., 2006,
  the A¹-homotopy definition (two finite correspondences from `X` to `Y` are
  A¹-homotopic if they are the restrictions along `X × 0` and `X × 1` of an
  element of `Cor(X × A¹, Y)`).
  REVIEW(citation): pin the exact lecture/section in review.
* V. Voevodsky, *A¹-homotopy theory*, Proc. Sympos. Pure Math. 67 (1998) /
  DMV Seminar 48, Birkhäuser, 2000.
  REVIEW(citation): pin the section in review.
-/

universe u

namespace AlgebraicGeometry

open CategoryTheory Limits

variable (S : Scheme.{u})

-- Reference: MVW (2006), the affine line `A¹_S = Spec S[t]`; mathlib's
-- `AlgebraicGeometry.AffineSpace` with the singleton index type.
-- `noncomputable`: the fiber product underlying `𝔸¹_S` carries chosen limit
-- data.
/-- The **affine line over `S`**: `𝔸¹_S = 𝔸¹_S`, the affine space with a
singleton index type. -/
noncomputable def affineLineOver (S : Scheme.{u}) : Scheme.{u} := 𝔸(ULift.{u} Unit; S)

-- Reference: MVW (2006), the structure morphism `A¹_S → S`.
/-- The structure morphism `𝔸¹_S ⟶ S`. -/
noncomputable def affineLineProj (S : Scheme.{u}) : affineLineOver S ⟶ S :=
  𝔸(ULift.{u} Unit; S) ↘ S

variable {S : Scheme.{u}}

-- Reference: MVW (2006), Appendix 1A p. 7 (fiber products of `Cor_S`
-- objects); smoothness is stable under base change and composition at the pin
-- (`smooth_isStableUnderBaseChange`, `smooth_comp`).
-- REVIEW(citation): pin the exact proposition in review.
/-- The structure morphism of the product `X ×_S 𝔸¹` with the affine line is
smooth: the first projection is a base change of the smooth
`𝔸¹_S ⟶ S`, and the structure morphism of `X` is smooth. -/
theorem smooth_fst_affineLineProj_comp (X : SmoothSchemeOver S) :
    Smooth (pullback.fst X.proj (affineLineProj S) ≫ X.proj) := by
  have hX : Smooth X.proj := X.smooth
  have hS : Smooth (affineLineProj S) :=
    inferInstanceAs (Smooth (𝔸(ULift.{u} Unit; S) ↘ S))
  have h1 : Smooth (pullback.fst X.proj (affineLineProj S)) := inferInstance
  exact smooth_comp _ _

-- Reference: MVW (2006), Appendix 1A p. 7 (products in `Cor_S` are separated
-- when the factors are).
-- REVIEW(citation): pin the exact proposition in review.
/-- The structure morphism of the product `X ×_S 𝔸¹` is separated: separated
morphisms are stable under base change and composition. TEMPORARY SORRY:
peeling plan — `IsSeparated` is stable under base change
(`MorphismProperty.IsStableUnderBaseChange`) and closed under composition
(`IsSeparated.comp`), applied to `X.proj` and `affineLineProj S` (the affine
line is separated over `S`). -/
theorem isSeparated_fst_affineLineProj_comp (X : SmoothSchemeOver S) :
    IsSeparated (pullback.fst X.proj (affineLineProj S) ≫ X.proj) := by
  have hX : IsSeparated X.proj := X.separated
  have hS : IsSeparated (affineLineProj S) :=
    inferInstanceAs (IsSeparated (𝔸(ULift.{u} Unit; S) ↘ S))
  have h1 : IsSeparated (pullback.fst X.proj (affineLineProj S)) := inferInstance
  exact inferInstance

-- Reference: MVW (2006), Appendix 1A p. 7 (products in `Cor_S` are Noetherian
-- over a Noetherian base).
-- REVIEW(citation): pin the exact proposition in review.
/-- The product `X ×_S 𝔸¹` is Noetherian when the base `S` is: finite type
over a Noetherian base is Noetherian, and smooth morphisms are of finite
presentation. TEMPORARY SORRY: peeling plan — `IsNoetherian` of a pullback
over a Noetherian base (`pullback` of `X ⟶ S` along `𝔸¹_S ⟶ S`), via
finite-presentation + Noetherian base ⇒ Noetherian source. -/
theorem isNoetherian_pullback_affineLineProj (X : SmoothSchemeOver S) [IsNoetherian S] :
    IsNoetherian (pullback X.proj (affineLineProj S)) := by
  haveI := X.smooth
  haveI := X.noetherian
  haveI : Smooth (affineLineProj S) :=
    inferInstanceAs (Smooth (𝔸(ULift.{u} Unit; S) ↘ S))
  haveI : LocallyOfFiniteType X.proj := inferInstance
  haveI : IsLocallyNoetherian S := inferInstance
  haveI : LocallyOfFiniteType (affineLineProj S) := inferInstance
  haveI : QuasiCompact (affineLineProj S) :=
    inferInstanceAs (QuasiCompact (𝔸(ULift.{u} Unit; S) ↘ S))
  haveI : QuasiCompact X.proj := inferInstance
  haveI : CompactSpace ↥S := inferInstance
  haveI : CompactSpace ↥(affineLineOver S) := by
    change CompactSpace ↥(pullback (terminal.from S)
      (terminal.from (Spec (CommRingCat.of (MvPolynomial (ULift.{u} Unit) (ULift.{u} ℤ))))))
    exact inferInstance
  exact (isNoetherian_iff _).mpr ⟨inferInstance, inferInstance⟩

-- Reference: MVW (2006), Appendix 1A p. 7 (the object `X ×_S A¹` of `Cor_S`).
-- REVIEW(citation): pin the exact proposition in review.
/-- The **product of `X` with the affine line**, as an object of `SmCor(S)`.
`noncomputable`: the fiber product carries chosen limit data. -/
noncomputable def smCorAffineLineProduct (X : SmoothSchemeOver S) [IsNoetherian S] : SmCor S :=
  ⟨⟨pullback X.proj (affineLineProj S),
    pullback.fst X.proj (affineLineProj S) ≫ X.proj,
    smooth_fst_affineLineProj_comp X,
    isSeparated_fst_affineLineProj_comp X,
    isNoetherian_pullback_affineLineProj X⟩⟩

-- Reference: MVW (2006), Lecture 1, p. 3 (the section `X × {pt} → X ×_S A¹`
-- induced by a point `pt : S → A¹`).
-- REVIEW(citation): pin the exact construction in review.
/-- The inclusion `X × {pt} ≅ X → X ×_S 𝔸¹` induced by a section
`pt : S ⟶ 𝔸¹_S` of the affine line: the lift of `(𝟙 X, pX ≫ pt)` against the
projections of the fiber product. `noncomputable`: the fiber product carries
chosen limit data. -/
noncomputable def affineLineProductIncl (X : SmoothSchemeOver S) (pt : S ⟶ affineLineOver S)
    (hpt : pt ≫ affineLineProj S = 𝟙 S) :
    X.carrier ⟶ pullback X.proj (affineLineProj S) :=
  pullback.lift (𝟙 X.carrier) (X.proj ≫ pt)
    (Eq.trans (Category.id_comp X.proj)
      (Eq.trans (Category.assoc X.proj pt (affineLineProj S))
        (Eq.trans (congrArg (X.proj ≫ ·) hpt) (Category.id_comp X.proj))).symm)

-- Reference: MVW (2006), Appendix 1A p. 7 (the inclusion is a morphism over
-- `S`).
-- REVIEW(citation): pin the exact proposition in review.
/-- The inclusion `X × {pt} → X ×_S 𝔸¹` is a morphism over `S`: composed with
the product's structure morphism it is `X.proj`. -/
theorem affineLineProductIncl_over (X : SmoothSchemeOver S) (pt : S ⟶ affineLineOver S)
    (hpt : pt ≫ affineLineProj S = 𝟙 S) :
    affineLineProductIncl X pt hpt ≫
        (pullback.fst X.proj (affineLineProj S) ≫ X.proj) = X.proj := by
  calc affineLineProductIncl X pt hpt ≫ (pullback.fst X.proj (affineLineProj S) ≫ X.proj)
      = (affineLineProductIncl X pt hpt ≫ pullback.fst X.proj (affineLineProj S)) ≫ X.proj :=
        (Category.assoc _ _ _).symm
    _ = (𝟙 X.carrier ≫ X.proj) :=
        congrArg (· ≫ X.proj) (pullback.lift_fst _ _ _)
    _ = X.proj := Category.id_comp X.proj

variable {X Y Z : SmoothSchemeOver S}

-- Reference: MVW (2006), Appendix 1A p. 7 (restriction of a correspondence
-- along a morphism = composition with the graph of the morphism).
-- REVIEW(citation): pin the exact proposition in review.
/-- **Restriction of a finite correspondence along an `S`-morphism**:
precomposition with the graph correspondence of `g`. -/
noncomputable def correspondenceRestrict [IsNoetherian X.carrier]
    (g : X.carrier ⟶ Y.carrier) (hg : g ≫ Y.proj = X.proj)
    (c : FiniteCorrespondence Y.proj Z.proj) :
    FiniteCorrespondence X.proj Z.proj :=
  correspondenceComp X.proj Y.proj Z.proj
    (graphFiniteCorrespondence X.proj Y.proj g hg
      (quasiCompact_graph_of_isSeparated X.proj Y.proj g hg Y.separated))
    c

-- Reference: MVW (2006), the A¹-homotopy definition (two finite
-- correspondences from `X` to `Y` are A¹-homotopic if they are the
-- restrictions along `X × 0` and `X × 1` of an element of `Cor(X × A¹, Y)`).
-- REVIEW(citation): pin the exact lecture/section in review.
/-- **A¹-homotopy of finite correspondences**: `c` and `d` from `X` to `Y` over
`S` are A¹-homotopic (with respect to the sections `pt₀ pt₁ : S ⟶ 𝔸¹_S`) when
they are the restrictions along the inclusions `X × {pt₀} → X ×_S 𝔸¹` and
`X × {pt₁} → X ×_S 𝔸¹` of a single finite correspondence on `X ×_S 𝔸¹`. -/
def IsA1Homotopic [IsNoetherian S] [IsNoetherian X.carrier]
    (pt₀ pt₁ : S ⟶ affineLineOver S)
    (hpt₀ : pt₀ ≫ affineLineProj S = 𝟙 S) (hpt₁ : pt₁ ≫ affineLineProj S = 𝟙 S)
    (c d : FiniteCorrespondence X.proj Y.proj) : Prop :=
  ∃ h : FiniteCorrespondence (smCorAffineLineProduct X).over.proj Y.proj,
    correspondenceRestrict (X := X) (Y := (smCorAffineLineProduct X).over) (Z := Y)
      (affineLineProductIncl X pt₀ hpt₀)
      (affineLineProductIncl_over X pt₀ hpt₀) h = c ∧
    correspondenceRestrict (X := X) (Y := (smCorAffineLineProduct X).over) (Z := Y)
      (affineLineProductIncl X pt₁ hpt₁)
      (affineLineProductIncl_over X pt₁ hpt₁) h = d

-- Reference: MVW (2006), the A¹-homotopy definition (reflexivity: the
-- constant homotopy `X × A¹ × {pt}`).
-- REVIEW(citation): pin the exact lecture/section in review.
/-- A¹-homotopy is reflexive. TEMPORARY SORRY: peeling plan — the constant
homotopy is the graph of the projection `X ×_S 𝔸¹ → X` pulled back along
itself; the two restrictions agree by `graphFiniteCorrespondence_comp` and the
identity laws of `correspondenceComp`. -/
theorem IsA1Homotopic.refl [IsNoetherian S] [IsNoetherian X.carrier]
    (pt₀ pt₁ : S ⟶ affineLineOver S) (hpt₀ : pt₀ ≫ affineLineProj S = 𝟙 S)
    (hpt₁ : pt₁ ≫ affineLineProj S = 𝟙 S) (c : FiniteCorrespondence X.proj Y.proj) :
    IsA1Homotopic pt₀ pt₁ hpt₀ hpt₁ c c := by
  -- TEMPORARY SORRY: peeling plan above.
  sorry

-- Reference: MVW (2006), the A¹-homotopy definition (symmetry).
-- REVIEW(citation): pin the exact lecture/section in review.
/-- A¹-homotopy is symmetric. TEMPORARY SORRY: peeling plan — swap the roles
of `pt₀` and `pt₁` in the witnessing correspondence. -/
theorem IsA1Homotopic.symm [IsNoetherian S] [IsNoetherian X.carrier]
    (pt₀ pt₁ : S ⟶ affineLineOver S) (hpt₀ : pt₀ ≫ affineLineProj S = 𝟙 S)
    (hpt₁ : pt₁ ≫ affineLineProj S = 𝟙 S) {c d : FiniteCorrespondence X.proj Y.proj}
    (h : IsA1Homotopic pt₀ pt₁ hpt₀ hpt₁ c d) :
    IsA1Homotopic pt₀ pt₁ hpt₀ hpt₁ d c := by
  -- TEMPORARY SORRY: peeling plan above.
  sorry

-- Reference: MVW (2006), the A¹-homotopy definition (transitivity: concatenate
-- homotopies along `A¹`).
-- REVIEW(citation): pin the exact lecture/section in review.
/-- A¹-homotopy is transitive. TEMPORARY SORRY: peeling plan — concatenate
the two witnessing correspondences along the affine line (gluing at the common
section), using `correspondenceComp` and the associativity law. -/
theorem IsA1Homotopic.trans [IsNoetherian S] [IsNoetherian X.carrier]
    (pt₀ pt₁ : S ⟶ affineLineOver S) (hpt₀ : pt₀ ≫ affineLineProj S = 𝟙 S)
    (hpt₁ : pt₁ ≫ affineLineProj S = 𝟙 S) {c d e : FiniteCorrespondence X.proj Y.proj}
    (h1 : IsA1Homotopic pt₀ pt₁ hpt₀ hpt₁ c d)
    (h2 : IsA1Homotopic pt₀ pt₁ hpt₀ hpt₁ d e) :
    IsA1Homotopic pt₀ pt₁ hpt₀ hpt₁ c e := by
  -- TEMPORARY SORRY: peeling plan above.
  sorry

end AlgebraicGeometry
