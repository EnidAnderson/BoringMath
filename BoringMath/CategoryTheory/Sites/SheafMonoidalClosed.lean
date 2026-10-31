/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import BoringMath.CategoryTheory.Sites.SheafHomBifunctor

/-!
# The monoidal closed structure on categories of sheaves (TREE H.8, #42)

This module addresses the TODO in the module docstring of
`Mathlib.CategoryTheory.Sites.Monoidal.lean` (Riou), quoted verbatim in issue
#42:

> TODO: show that the monoidal category structure on sheaves is closed,
> and that the internal hom can be defined in such a way that the
> underlying presheaf is the internal hom in the category of presheaves.
> Note that a `MonoidalClosed` instance on sheaves can already be obtained
> abstractly using the material in `CategoryTheory.Monoidal.Braided.Reflection`.

Two peels, floor first:

* Peel (a) (the floor): `Sheaf.monoidalClosed`, the abstract `MonoidalClosed`
  structure on `Sheaf J A` obtained from Day's reflection theorem
  (`Monoidal.Reflective.monoidalClosed`) applied to the sheafification
  adjunction `presheafToSheaf J A ⊣ sheafToPresheaf J A`. It is delivered as
  a `scoped instance`, not a global one: as in
  `Mathlib.CategoryTheory.Sites.Monoidal`, the monoidal structure on sheaves is
  not made a global instance since it can conflict with the structure deduced
  from chosen finite products (for the sheaf-of-types case see H.7, #41).
* Peel (b) (the TODO's real content): `sheafInternalHom`, the internal hom
  whose underlying presheaf is (isomorphic to) the presheaf internal hom
  (`sheafInternalHom_underlying_iso`).

Cross-citation: for sheaves of types, the cartesian closed structure and the
identification of its internal hom with `sheafHom` are TREE H.7 (#41),
`BoringMath.CategoryTheory.Sites.SheafHomBifunctor` (imported above for
cross-reference; not duplicated here).

## References
* [Riou] J. Riou, `Mathlib.CategoryTheory.Sites.Monoidal` (the TODO above).
* [Day] B. Day, *A reflection theorem for closed categories*, J. Pure Appl.
  Algebra 2(1) (1972), 1-11.
* [Day70] B. Day, *On closed categories of functors*, in: Reports of the
  Midwest Category Seminar IV, Lecture Notes in Math. 137, Springer, 1970,
  1-38.
* [SGA4] M. Artin, A. Grothendieck, J. L. Verdier (eds.), *Théorie des topos et
  cohomologie étale des schémas (SGA 4)*, Séminaire de Géométrie Algébrique du
  Bois-Marie 1963-1964, Lecture Notes in Math. 269, 270, 305, Springer,
  1972-73, Exposés I-II.
* [MM] S. Mac Lane, I. Moerdijk, *Sheaves in Geometry and Logic*, Springer,
  1992, Chapter I.
-/

open Opposite
open CategoryTheory Enriched.FunctorCategory MonoidalClosed
open scoped CategoryTheory.MonoidalClosed CategoryTheory.MonoidalClosed.FunctorCategory

universe u₁ v₁ u₃ v₃

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {A : Type u₃} [Category.{v₃} A] [MonoidalCategory A] [MonoidalClosed A]
variable [∀ (F₁ F₂ : Cᵒᵖ ⥤ A), HasFunctorEnrichedHom A F₁ F₂]
variable [∀ (F₁ F₂ : Cᵒᵖ ⥤ A), HasEnrichedHom A F₁ F₂]

-- Reference: [Day70], Lecture Notes in Math. 137 (1970), 1-38 (the internal hom
-- of a Day convolution is the functor enriched hom); [Riou],
-- `Mathlib.CategoryTheory.Sites.Monoidal`, `Presheaf` section
-- (`functorEnrichedHomCoyonedaObjEquiv`).
/-- **The presheaf internal hom is the functor enriched hom** (primitive
definitional lemma): for presheaves `F G : Cᵒᵖ ⥤ A`, the object
`(ihom F).obj G` of the Day-convolution internal hom is `functorEnrichedHom A F G`. -/
theorem ihom_obj_eq_functorEnrichedHom (F G : Cᵒᵖ ⥤ A) :
    (ihom F).obj G = functorEnrichedHom A F G := rfl

variable {J : GrothendieckTopology C} [HasWeakSheafify J A]

-- Reference: [Day], J. Pure Appl. Algebra 2(1) (1972), 1-11 (in a reflective
-- subcategory the internal hom of the reflection is `R ⋙ ihom (R c) ⋙ L`);
-- [SGA4], Exposés I-II.
-- REVIEW(citation): pin the exact SGA 4 proposition in review (W5/#13).
/-- **The sheaf internal hom** (peel (b), the carrier): the functor sending a
sheaf `G` to the sheafification of the presheaf internal hom of the underlying
presheaves. By Day's reflection theorem this is the internal hom of the
monoidal closed structure `Sheaf.monoidalClosed` below. -/
noncomputable def sheafInternalHom (F : Sheaf J A) : Sheaf J A ⥤ Sheaf J A :=
  -- `noncomputable`: sheafification (`HasWeakSheafify`) is chosen data.
  sheafToPresheaf J A ⋙ ihom ((sheafToPresheaf J A).obj F) ⋙ presheafToSheaf J A

-- Reference: [Riou], `Mathlib.CategoryTheory.Sites.Monoidal` TODO, second
-- bullet (quoted verbatim above: "the internal hom can be defined in such a way
-- that the underlying presheaf is the internal hom in the category of
-- presheaves"); [SGA4], Exposés I-II (the presheaf internal hom of a sheaf is
-- a sheaf); [MM], Chapter I.
-- REVIEW(citation): pin the exact propositions in review (W5/#13).
/-- **The underlying presheaf of the sheaf internal hom is the presheaf
internal hom** (peel (b), the TODO's real content): for sheaves `F G`, the
underlying presheaf of `sheafInternalHom F |>.obj G` is isomorphic to
`(ihom ((sheafToPresheaf J A).obj F)).obj ((sheafToPresheaf J A).obj G)`, the
internal hom of the underlying presheaves in `Cᵒᵖ ⥤ A`. -/
noncomputable def sheafInternalHom_underlying_iso (F G : Sheaf J A) :
    (sheafToPresheaf J A).obj (sheafInternalHom F |>.obj G) ≅
      (ihom ((sheafToPresheaf J A).obj F)).obj ((sheafToPresheaf J A).obj G) := by
  -- `noncomputable`: the left-hand side involves the chosen sheafification.
  have h1 : (ihom ((sheafToPresheaf J A).obj F)).obj ((sheafToPresheaf J A).obj G) =
      functorEnrichedHom A ((sheafToPresheaf J A).obj F)
        ((sheafToPresheaf J A).obj G) :=
    ihom_obj_eq_functorEnrichedHom _ _
  have h2 : Presheaf.IsSheaf J (functorEnrichedHom A ((sheafToPresheaf J A).obj F)
      ((sheafToPresheaf J A).obj G)) :=
    Presheaf.isSheaf_functorEnrichedHom _ _ G.property
  have h3 : Presheaf.IsSheaf J ((ihom ((sheafToPresheaf J A).obj F)).obj
      ((sheafToPresheaf J A).obj G)) :=
    Eq.subst (motive := fun P => Presheaf.IsSheaf J P) h1.symm h2
  exact (sheafToPresheaf J A).mapIso (sheafificationIso ⟨_, h3⟩).symm

variable [SymmetricCategory A]

-- Mathlib deliberately keeps `Sheaf.monoidalCategory` a `def` rather than a
-- global instance (it can conflict with the cartesian monoidal structure); we
-- make it a local instance so that the closed structure below can be stated.
attribute [local instance] Sheaf.monoidalCategory

namespace Sheaf

-- Reference: [Riou], `Mathlib.CategoryTheory.Sites.Monoidal` module docstring
-- (the TODO quoted above: "a `MonoidalClosed` instance on sheaves can already
-- be obtained abstractly using ... `CategoryTheory.Monoidal.Braided.Reflection`");
-- [Day], J. Pure Appl. Algebra 2(1) (1972), 1-11 (Day's reflection theorem);
-- [SGA4], Exposés I-II (the sheafification adjunction).
-- REVIEW(citation): pin the exact SGA 4 exposé/proposition in review (W5/#13).
/-- **The sheaf category is monoidal closed** (peel (a), the floor): Day's
reflection theorem (`Monoidal.Reflective.monoidalClosed`) applied to the
sheafification adjunction `presheafToSheaf J A ⊣ sheafToPresheaf J A`, whose
left adjoint is monoidal (`GrothendieckTopology.W.monoidal`) and whose right
adjoint is fully faithful (`Reflective (sheafToPresheaf J A)`). Delivered as a
`scoped instance` because the monoidal structure on sheaves is not a global
instance in Mathlib. -/
@[instance_reducible]
noncomputable scoped instance monoidalClosed : MonoidalClosed (Sheaf J A) :=
  -- `noncomputable`: sheafification (`HasWeakSheafify`) is chosen data.
  Monoidal.Reflective.monoidalClosed (sheafificationAdjunction J A)

end Sheaf

open scoped Sheaf

-- Reference: [Riou], `Mathlib.CategoryTheory.Sites.Monoidal` TODO; [Day], 1972
-- (the reflection's `Closed` structure has
-- `rightAdj = R ⋙ ihom (R.obj c) ⋙ L`).
/-- **The explicit internal hom is `ihom` in the sheaf category** (primitive
definitional lemma): under the scoped instance `Sheaf.monoidalClosed`,
`sheafInternalHom F` is the internal hom functor `ihom F`. -/
theorem sheafInternalHom_eq_ihom (F : Sheaf J A) : sheafInternalHom F = ihom F := rfl

-- Reference: [Riou], `Mathlib.CategoryTheory.Sites.Monoidal` TODO ("the internal
-- hom ... in the category of presheaves").
/-- The same identification through `MonoidalClosed.internalHom` (primitive
definitional lemma). -/
theorem sheafInternalHom_eq_internalHom (F : Sheaf J A) :
    sheafInternalHom F = MonoidalClosed.internalHom.obj (op F) := rfl

-- Reference: [Day], J. Pure Appl. Algebra 2(1) (1972), 1-11; [Mac Lane],
-- *Categories for the Working Mathematician*, 2nd ed., Springer, 1998,
-- Chapter IV (adjoints).
-- REVIEW(citation): pin the exact section in [Mac Lane] in review.
/-- **The tensor functor is left adjoint to the sheaf internal hom**: the
explicit internal hom really is the right adjoint of `tensorLeft F`. -/
noncomputable def tensorLeft_adj_sheafInternalHom (F : Sheaf J A) :
    MonoidalCategory.tensorLeft F ⊣ sheafInternalHom F :=
  -- `noncomputable`: the adjunction data goes through the chosen
  -- sheafification. The right adjoint of the reflection's `Closed` structure is
  -- `sheafInternalHom F` by the definitional lemma `sheafInternalHom_eq_ihom`.
  (Monoidal.Reflective.closed (sheafificationAdjunction J A) F).adj

end CategoryTheory
