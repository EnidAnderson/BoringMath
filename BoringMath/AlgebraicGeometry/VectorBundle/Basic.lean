/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-!
# Vector bundles on schemes (V.1, part 1)

An algebraic **vector bundle** on a scheme `X` (ticket V.1, #280) is a bundled
sheaf of `X.Modules` (`SheafOfModules` over `X.ringCatSheaf`) that is locally
free **of finite rank** — witnessed by local-generator data whose generating
index sets are finite. Mathlib at the pin has the `IsLocallyFree` class
(`Mathlib/Algebra/Category/ModuleCat/Sheaf/LocallyFree.lean`, Stacks tag 01C6)
and the abelian category `X.Modules`, but no bundled vector-bundle type.

This module provides: the `VectorBundle X` structure, its category instance
(morphisms = module-sheaf maps), the forgetful functor, the free bundle, the
direct sum (biproduct), and the statement layer for dual / tensor / determinant
(those need the sheaf-level internal Hom / tensor product, ABSENT at the pin —
named Tier-2 peels: sheafification of the presheaf-level Hom/tensor).

## References
* Hartshorne, *Algebraic Geometry*, GTM 52, ch. II, §5 (vector bundles as
  locally free sheaves). REVIEW(citation): pin the section.
* Stacks Project, tag 01C6 (locally free sheaves), tag 01C7? —
  REVIEW(citation): pin the tags.
* EGA I (new ed.), §1.7? — REVIEW(citation).
-/

universe u

namespace AlgebraicGeometry

open CategoryTheory Limits

variable (X : Scheme.{u})

-- Reference: Hartshorne, GTM 52, ch. II, §5 (a vector bundle is a locally
-- free sheaf of finite rank); Stacks tag 01C6 + finite presentation.
-- REVIEW(citation): pin.
-- Reference: Stacks tag 01C6 + finite presentation — a locally free sheaf of
-- finite rank is one admitting local-generator data with finite generating
-- sets.
-- REVIEW(citation): pin.
/-- A sheaf of `O_X`-modules is **locally free of finite rank** when it admits
local-generator data whose generating index sets are all finite. -/
def IsLocallyFreeOfFiniteRank (X : Scheme.{u}) (M : X.Modules) : Prop :=
  ∃ q : SheafOfModules.LocalGeneratorsData.{u} M,
    q.IsLocallyFreeData ∧ ∀ i, Finite (q.generators i).I

-- Reference: Hartshorne, GTM 52, ch. II, §5 (a vector bundle is a locally
-- free sheaf of finite rank); Stacks tag 01C6 + finite presentation.
-- REVIEW(citation): pin.
/-- A **vector bundle** on a scheme `X`: a sheaf of `O_X`-modules that is
locally free of finite rank. -/
structure VectorBundle (X : Scheme.{u}) where
  /-- the underlying sheaf of modules -/
  toModule : X.Modules
  /-- local freeness -/
  isLocallyFree : SheafOfModules.IsLocallyFree (R := X.ringCatSheaf) toModule
  /-- finite rank -/
  finiteRank : IsLocallyFreeOfFiniteRank X toModule

namespace VectorBundle

variable {X : Scheme.{u}}

-- Reference: the category of vector bundles has module-sheaf maps as
-- morphisms (Hartshorne II.5).
/-- The **category of vector bundles** on `X`: morphisms are sheaf-of-modules
maps between the underlying modules. -/
instance : Category.{u} (VectorBundle X) where
  Hom E F := E.toModule ⟶ F.toModule
  id E := 𝟙 E.toModule
  comp f g := f ≫ g
  id_comp f := Category.id_comp f
  comp_id f := Category.comp_id f
  assoc f g h := Category.assoc f g h

-- Reference: the forgetful functor to sheaves of modules (definitional).
/-- The **forgetful functor** from vector bundles to `X.Modules`. -/
def forget : VectorBundle X ⥤ X.Modules where
  obj E := E.toModule
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

-- Reference: finite-rank local-generator data for the free sheaf
-- (Stacks 01C6 + the generating sections of `free`).
-- REVIEW(citation): pin.
/-- The free sheaf on a finite index set has finite-rank local-generator data.
TEMPORARY SORRY: peeling plan — take the covering by the terminal object
`⊤` (`CoversTop` of the constant family) and `free.generatingSections I`
transported along `M.over ⊤ ≅ M`; the generating index set is `I`, finite. -/
theorem free_finiteRankData (I : Type u) [Finite I] :
    IsLocallyFreeOfFiniteRank X (SheafOfModules.free (R := X.ringCatSheaf) I) := by
  -- TEMPORARY SORRY: peeling plan above.
  sorry

-- Reference: Hartshorne II.5, Ex. 5.1? — the free bundle `O_X^I` for finite `I`
-- is a vector bundle (locally free of rank `Nat.card I`).
-- REVIEW(citation): pin.
/-- The **free vector bundle** `O_X^I` on a finite index set `I`. -/
noncomputable def free (I : Type u) [Finite I] : VectorBundle X :=
  { toModule := SheafOfModules.free (R := X.ringCatSheaf) I
    isLocallyFree := inferInstance
    finiteRank := free_finiteRankData I }

-- Reference: local freeness is closed under finite direct sums (Stacks 01C6;
-- locally, a direct sum of free modules is free).
/-- The direct sum of locally free sheaves is locally free. TEMPORARY SORRY:
peeling plan — union of the two local-generator coverings; on overlaps the
direct sum of the free presentations is the free presentation of the sum
(`freeSumIso`). -/
theorem isLocallyFree_biprod (M N : X.Modules) [M.IsLocallyFree] [N.IsLocallyFree] :
    (Limits.biprod M N).IsLocallyFree := by
  -- TEMPORARY SORRY: peeling plan above.
  sorry

-- Reference: finite-rank local-generator data of a direct sum (finite ×
-- finite generating sets).
/-- The direct sum of finite-rank locally free sheaves has finite-rank data.
TEMPORARY SORRY: peeling plan — pair the two coverings; generating index
`I ⊕ J`, finite. -/
theorem finiteRank_biprod (M N : X.Modules)
    (hM : IsLocallyFreeOfFiniteRank X M) (hN : IsLocallyFreeOfFiniteRank X N) :
    IsLocallyFreeOfFiniteRank X (Limits.biprod M N) := by
  -- TEMPORARY SORRY: peeling plan above.
  sorry

-- Reference: Hartshorne II.5 (direct sum of vector bundles).
/-- The **direct sum** of two vector bundles (the biproduct in `X.Modules`).
`noncomputable`: the biproduct carries chosen limit data. -/
noncomputable def directSum (E F : VectorBundle X) : VectorBundle X := by
  haveI := E.isLocallyFree
  haveI := F.isLocallyFree
  refine ⟨Limits.biprod E.toModule F.toModule, isLocallyFree_biprod _ _, ?_⟩
  exact finiteRank_biprod _ _ E.finiteRank F.finiteRank

-- Reference: Hartshorne II.5, Ex. 5.7? (the dual bundle E∨ = Hom(E, O_X));
-- needs the sheaf-level internal Hom — ABSENT at the pin (no
-- `SheafOfModules.tensorProduct`/internal Hom); Tier-2 peel: sheafify the
-- presheaf-level Hom (sheafification exists for `X.Modules`).
-- REVIEW(citation): pin.
/-- The **dual vector bundle** `E∨`. TEMPORARY SORRY: peeling plan — define the
presheaf-level Hom `U ↦ Hom_{O(U)}(E(U), O(U))`, sheafify to a sheaf of
modules, locally free of the same finite rank (dual of free is free). -/
noncomputable def dual (E : VectorBundle X) : VectorBundle X := by
  -- TEMPORARY SORRY: peeling plan above.
  sorry

-- Reference: the tensor product of vector bundles E ⊗ F; needs the
-- sheaf-level tensor product — ABSENT at the pin; Tier-2 peel: sheafify the
-- presheaf tensor product (exists for `PresheafOfModules`).
/-- The **tensor product** of two vector bundles. TEMPORARY SORRY: peeling plan —
sheafify the presheaf tensor product; locally free of rank `rank E * rank F`
(rank well-definedness is its own named peel). -/
noncomputable def tensorProduct (E F : VectorBundle X) : VectorBundle X := by
  -- TEMPORARY SORRY: peeling plan above.
  sorry

-- Reference: the determinant bundle det E = ⋀^r E (Hartshorne II.5, Ex.
-- 5.16?); needs exterior powers of sheaves of modules — ABSENT at the pin.
-- REVIEW(citation): pin.
/-- The **determinant line bundle** `det E`. TEMPORARY SORRY: peeling plan —
top exterior power via the sheafified exterior power of the presheaf module;
a line bundle (locally free of rank 1). -/
noncomputable def det (E : VectorBundle X) : VectorBundle X := by
  -- TEMPORARY SORRY: peeling plan above.
  sorry

end VectorBundle

end AlgebraicGeometry
