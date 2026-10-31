/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.CategoryTheory.Sites.SheafHom
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Sites.CartesianClosed
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes

/-!
# The `sheafHom` bifunctor and the product adjunction for sheaves of types

This module addresses the TODO in the module docstring of
`Mathlib.CategoryTheory.Sites.SheafHom.lean` (Riou), quoted verbatim in
issue #41:

> TODO: turn both `presheafHom` and `sheafHom` into bifunctors; for a sheaf
> of types `F`, the `sheafHom` functor from `F` is right-adjoint to the product
> functor with `F`, i.e. for all `X` and `Y`, there is a natural bijection
> `(X ⨯ F ⟶ Y) ≃ (X ⟶ sheafHom F Y)`; use these results in order to show that
> the category of sheaves of types is Cartesian closed.

The three peels:

* Peel (a): `presheafHomBifunctor` and `sheafHomBifunctor` — the hom presheaf
  and the hom sheaf as bifunctors (contravariant in the first variable).
* Peel (b): `sheafHomAdjunction` — `(- ⨯ F) ⊣ sheafHom F` for sheaves of
  types, built from the bijection `sheafHomProdHomEquiv`.
* Peel (c): `Sheaf J (Type (max u v))` is Cartesian closed; at this pin
  "Cartesian closed" means `CartesianMonoidalCategory` together with
  `MonoidalClosed` (see `Mathlib.CategoryTheory.Monoidal.Closed.Cartesian`),
  and the internal hom is `sheafHom` (`sheafHom_iso_internalHom`).

Universe note: for `A := Type (max u v)` the category instance
`CategoryTheory.types : Category.{w} (Type w)` puts `v' = max u v`, so
`sheafHom F G : Sheaf J (Type (max u v))` lands in the same category
(`max u v v'` reduces to `max u v`).

## References
* [Riou] J. Riou, `Mathlib.CategoryTheory.Sites.SheafHom` (the TODO above).
* [SGA4] A. Grothendieck et al., *Éléments de géométrie algébrique IV*,
  Publ. Math. IHÉS 32 (1967), Exposé I.
* [Stacks] The Stacks Project, Chapter 7 "Sites and Sheaves" (tag 00UZ),
  §7.7 "Sheaves" (tag 00VL).
* [MM] S. Mac Lane, I. Moerdijk, *Sheaves in Geometry and Logic*, Springer,
  1992, Chapter I.
* [Mac Lane] S. Mac Lane, *Categories for the Working Mathematician*, 2nd ed.,
  Springer, 1998, Chapter IV (Adjoints).
-/

universe v u u' v'

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {A : Type u'} [Category.{v'} A]

/-! ### Peel (a): `presheafHom` and `sheafHom` as bifunctors -/

-- Reference: [MM], Chapter I, §5 (restriction along `Over.map h ⋙ Over.forget X =
-- `Over.forget Y`, `Over.mapForget_eq`, Comma/Over/Basic.lean); [Mac Lane],
-- Chapter III, §4 (whiskering is functorial in the left factor).
-- REVIEW(citation): pin the exact propositions in review.
/-- **Coherence of `whiskerLeft` with `Over.map` and `Over.forget`** (primitive
definitional lemma): whiskering by `(Over.map h).op` after whiskering by
`(Over.forget X).op` is whiskering by `(Over.forget Y).op`, because
`Over.map h ⋙ Over.forget X = Over.forget Y` (`Over.mapForget_eq`, rfl). -/
theorem whiskerLeft_overMap_op_whiskerLeft_overForget_op {X Y : C} (h : Y ⟶ X)
    {G H : Cᵒᵖ ⥤ A} (g : G ⟶ H) :
    Functor.whiskerLeft (Over.map h).op (Functor.whiskerLeft (Over.forget X).op g) =
      Functor.whiskerLeft (Over.forget Y).op g := rfl

-- Reference: [Riou], `Mathlib.CategoryTheory.Sites.SheafHom` module docstring
-- (TODO: "turn both `presheafHom` and `sheafHom` into bifunctors"); [MM],
-- Chapter I, §5 (the internal hom of a presheaf category).
-- REVIEW(citation): pin the exact proposition in [MM] in review.
/-- **Post-composition** on `presheafHom`: a morphism `g : G ⟶ G'` induces the
natural transformation `presheafHom F G ⟶ presheafHom F G'` given at `X` by
`α ↦ α ≫ (Over.forget X.unop).op ⋙ g`. -/
def presheafHomPostcomp (F G G' : Cᵒᵖ ⥤ A) (g : G ⟶ G') :
    presheafHom F G ⟶ presheafHom F G' where
  app X := ↾(fun (α : (Over.forget X.unop).op ⋙ F ⟶ (Over.forget X.unop).op ⋙ G) =>
    α ≫ Functor.whiskerLeft (Over.forget X.unop).op g)
  naturality X Y f := by
    refine ConcreteCategory.ext_apply (fun α => ?_)
    change ((presheafHom F G).map f α) ≫ Functor.whiskerLeft (Over.forget Y.unop).op g =
      Functor.whiskerLeft (Over.map f.unop).op
        (α ≫ Functor.whiskerLeft (Over.forget X.unop).op g)
    -- `Functor.whiskerLeft_comp` splits the right factor;
    -- `whiskerLeft_overMap_op_whiskerLeft_overForget_op` rewrites the remaining
    -- factor `whiskerLeft (Over.map f.unop).op (whiskerLeft (Over.forget X.unop).op g)`
    -- to `whiskerLeft (Over.forget Y.unop).op g` (unique occurrence: the only
    -- whiskerLeft of a whiskerLeft in the goal).
    exact (congrArg (fun β => Functor.whiskerLeft (Over.map f.unop).op α ≫ β)
        (whiskerLeft_overMap_op_whiskerLeft_overForget_op f.unop g)).symm.trans
      (Functor.whiskerLeft_comp (Over.map f.unop).op α
        (Functor.whiskerLeft (Over.forget X.unop).op g))

-- Reference: [MM], Chapter I, §5 (functoriality of the presheaf internal hom).
-- REVIEW(citation): pin the exact proposition in [MM] in review.
/-- **Post-composition preserves identities**: `presheafHomPostcomp` of the
identity morphism is the identity natural transformation. -/
theorem presheafHomPostcomp_id (F G : Cᵒᵖ ⥤ A) :
    presheafHomPostcomp F G G (𝟙 G) = 𝟙 (presheafHom F G) := by
  refine NatTrans.ext (funext fun X => ConcreteCategory.ext ?_)
  refine DFunLike.ext _ _ (fun α => ?_)
  change α ≫ Functor.whiskerLeft (Over.forget X.unop).op (𝟙 G) = α
  exact (congrArg (fun β => α ≫ β)
    (Functor.whiskerLeft_id' (Over.forget X.unop).op (G := G))).trans (Category.comp_id α)

-- Reference: [MM], Chapter I, §5 (functoriality of the presheaf internal hom).
-- REVIEW(citation): pin the exact proposition in [MM] in review.
/-- **Post-composition preserves composition**: `presheafHomPostcomp` is a
functor in the morphism of the second variable. -/
theorem presheafHomPostcomp_comp (F G G' G'' : Cᵒᵖ ⥤ A) (f : G ⟶ G') (g : G' ⟶ G'') :
    presheafHomPostcomp F G G'' (f ≫ g) =
      presheafHomPostcomp F G G' f ≫ presheafHomPostcomp F G' G'' g := by
  refine NatTrans.ext (funext fun X => ConcreteCategory.ext ?_)
  refine DFunLike.ext _ _ (fun α => ?_)
  change α ≫ Functor.whiskerLeft (Over.forget X.unop).op (f ≫ g) =
    (α ≫ Functor.whiskerLeft (Over.forget X.unop).op f) ≫
      Functor.whiskerLeft (Over.forget X.unop).op g
  exact (congrArg (fun β => α ≫ β)
    (Functor.whiskerLeft_comp (Over.forget X.unop).op f g)).trans
      (Category.assoc α _ _).symm

-- Reference: [Riou], `Mathlib.CategoryTheory.Sites.SheafHom` module docstring
-- (TODO, first bullet); [MM], Chapter I, §5.
-- REVIEW(citation): pin the exact proposition in [MM] in review.
/-- The **`presheafHom` functor in the second variable**: `G ↦ presheafHom F G`
(peel (a), presheaf half, covariant part). -/
def presheafHomFunctor (F : Cᵒᵖ ⥤ A) :
    (Cᵒᵖ ⥤ A) ⥤ Cᵒᵖ ⥤ Type (max (max u v) v') where
  obj G := presheafHom F G
  map g := presheafHomPostcomp F _ _ g
  map_id G := presheafHomPostcomp_id F G
  map_comp f g := presheafHomPostcomp_comp F _ _ _ f g

-- Reference: [MM], Chapter I, §5 (the presheaf internal hom is contravariant in
-- the first variable).
-- REVIEW(citation): pin the exact proposition in [MM] in review.
/-- **Pre-composition** on `presheafHom`: a morphism `f : F' ⟶ F` induces the
natural transformation `presheafHom F G ⟶ presheafHom F' G` given at `X` by
`α ↦ (Over.forget X.unop).op ⋙ f ≫ α`. -/
def presheafHomPrecomp (F F' G : Cᵒᵖ ⥤ A) (f : F' ⟶ F) :
    presheafHom F G ⟶ presheafHom F' G where
  app X := ↾(fun (α : (Over.forget X.unop).op ⋙ F ⟶ (Over.forget X.unop).op ⋙ G) =>
    Functor.whiskerLeft (Over.forget X.unop).op f ≫ α)
  naturality X Y f' := by
    refine ConcreteCategory.ext_apply (fun α => ?_)
    change Functor.whiskerLeft (Over.forget Y.unop).op f ≫
        Functor.whiskerLeft (Over.map f'.unop).op α =
      Functor.whiskerLeft (Over.map f'.unop).op
        (Functor.whiskerLeft (Over.forget X.unop).op f ≫ α)
    -- `Functor.whiskerLeft_comp` splits the right factor;
    -- `whiskerLeft_overMap_op_whiskerLeft_overForget_op` rewrites the remaining
    -- factor (unique occurrence of a whiskerLeft of a whiskerLeft in the goal).
    exact (congrArg (fun β => β ≫ Functor.whiskerLeft (Over.map f'.unop).op α)
        (whiskerLeft_overMap_op_whiskerLeft_overForget_op f'.unop f)).symm.trans
      (Functor.whiskerLeft_comp (Over.map f'.unop).op
        (Functor.whiskerLeft (Over.forget X.unop).op f) α)

-- Reference: [MM], Chapter I, §5 (contravariant functoriality).
-- REVIEW(citation): pin the exact proposition in [MM] in review.
/-- **Pre-composition preserves identities**. -/
theorem presheafHomPrecomp_id (F G : Cᵒᵖ ⥤ A) :
    presheafHomPrecomp F F G (𝟙 F) = 𝟙 (presheafHom F G) := by
  refine NatTrans.ext (funext fun X => ConcreteCategory.ext ?_)
  refine DFunLike.ext _ _ (fun α => ?_)
  change Functor.whiskerLeft (Over.forget X.unop).op (𝟙 F) ≫ α = α
  exact (congrArg (fun β => β ≫ α)
    (Functor.whiskerLeft_id' (Over.forget X.unop).op (G := F))).trans (Category.id_comp α)

-- Reference: [MM], Chapter I, §5 (contravariant functoriality).
-- REVIEW(citation): pin the exact proposition in [MM] in review.
/-- **Pre-composition reverses composition** (contravariance): for
`f : F' ⟶ F` and `g : F'' ⟶ F'`, precomposition with `g ≫ f` is the composite
of precomposition with `f` followed by precomposition with `g`. -/
theorem presheafHomPrecomp_comp (F F' F'' G : Cᵒᵖ ⥤ A) (f : F' ⟶ F) (g : F'' ⟶ F') :
    presheafHomPrecomp F F'' G (g ≫ f) =
      presheafHomPrecomp F F' G f ≫ presheafHomPrecomp F' F'' G g := by
  refine NatTrans.ext (funext fun X => ConcreteCategory.ext ?_)
  refine DFunLike.ext _ _ (fun α => ?_)
  change Functor.whiskerLeft (Over.forget X.unop).op (g ≫ f) ≫ α =
    Functor.whiskerLeft (Over.forget X.unop).op g ≫
      (Functor.whiskerLeft (Over.forget X.unop).op f ≫ α)
  exact (congrArg (fun β => β ≫ α)
    (Functor.whiskerLeft_comp (Over.forget X.unop).op g f)).trans (Category.assoc _ _ _)

-- Reference: [Riou], `Mathlib.CategoryTheory.Sites.SheafHom` module docstring
-- (TODO, first bullet); [MM], Chapter I, §5.
-- REVIEW(citation): pin the exact proposition in [MM] in review.
/-- The **`presheafHom` bifunctor**, contravariant in the first variable and
covariant in the second (peel (a), presheaf half). -/
def presheafHomBifunctor :
    (Cᵒᵖ ⥤ A)ᵒᵖ ⥤ (Cᵒᵖ ⥤ A) ⥤ Cᵒᵖ ⥤ Type (max (max u v) v') where
  obj F := presheafHomFunctor F.unop
  map f :=
    { app := fun G => presheafHomPrecomp _ _ _ f.unop
      naturality := by
        intro G G' h
        refine NatTrans.ext (funext fun X => ConcreteCategory.ext ?_)
        refine DFunLike.ext _ _ (fun α => ?_)
        change Functor.whiskerLeft (Over.forget X.unop).op f.unop ≫
            (α ≫ Functor.whiskerLeft (Over.forget X.unop).op h) =
          (Functor.whiskerLeft (Over.forget X.unop).op f.unop ≫ α) ≫
            Functor.whiskerLeft (Over.forget X.unop).op h
        -- the interchange law: both sides are the two bracketings of the same
        -- triple composite, related by `Category.assoc` (unique occurrence).
        exact (Category.assoc _ _ _).symm }
  map_id F := NatTrans.ext (funext fun G => presheafHomPrecomp_id _ _)
  map_comp f g :=
    NatTrans.ext (funext fun G => presheafHomPrecomp_comp _ _ _ _ f.unop g.unop)

-- Reference: [SGA4], Exposé I (pullback of sheaves along `Over.map f` composed
-- with pullback along `Over.forget X` is pullback along `Over.forget Y`);
-- `sheafPushforwardContinuousComp` (Sites/Continuous.lean:383, an `Iso.refl`)
-- together with `Over.mapForget_eq` (Comma/Over/Basic.lean).
-- REVIEW(citation): pin the exact section of [SGA4] in review.
/-- **Coherence of `overMapPullback` with `overPullback`** (primitive
definitional lemma): pushing forward along `Over.map f.unop` after pulling
back along `Over.forget X.unop` is pulling back along `Over.forget Y.unop`,
because `Over.map f.unop ⋙ Over.forget X.unop = Over.forget Y.unop`
(`Over.mapForget_eq`, rfl, and `sheafPushforwardContinuousComp` is an
`Iso.refl`). -/
theorem overMapPullback_map_overPullback_map {X Y : Cᵒᵖ} (f : X ⟶ Y)
    {G G' : Sheaf J A} (g : G ⟶ G') :
    (J.overMapPullback A f.unop).map ((J.overPullback A X.unop).map g) =
      (J.overPullback A Y.unop).map g := rfl

-- Reference: [Riou], `Mathlib.CategoryTheory.Sites.SheafHom` (`sheafHom'`,
-- `sheafHom`, and the TODO); [SGA4], Exposé I (the sheaf of morphisms is
-- functorial in both variables).
-- REVIEW(citation): pin the exact section of [SGA4] in review.
/-- **Post-composition** on the underlying presheaf of `sheafHom`: a morphism
`g : G ⟶ G'` of sheaves induces `sheafHom' F G ⟶ sheafHom' F G'`, given at
`X : Cᵒᵖ` by `α ↦ α ≫ (J.overPullback A X.unop).map g`. -/
def sheafHomPostcomp (F G G' : Sheaf J A) (g : G ⟶ G') :
    sheafHom' F G ⟶ sheafHom' F G' where
  app X := ↾(fun (α : (J.overPullback A X.unop).obj F ⟶ (J.overPullback A X.unop).obj G) =>
    α ≫ (J.overPullback A X.unop).map g)
  naturality X Y f := by
    refine ConcreteCategory.ext_apply (fun φ => ?_)
    change (J.overMapPullback A f.unop).map φ ≫ (J.overPullback A Y.unop).map g =
      (J.overMapPullback A f.unop).map (φ ≫ (J.overPullback A X.unop).map g)
    -- `Functor.map_comp` splits the right factor;
    -- `overMapPullback_map_overPullback_map` rewrites the remaining factor
    -- (unique occurrence of `map` applied to `map g` in the goal).
    exact (congrArg (fun β => (J.overMapPullback A f.unop).map φ ≫ β)
        (overMapPullback_map_overPullback_map f g)).symm.trans
      (Functor.map_comp (J.overMapPullback A f.unop) φ ((J.overPullback A X.unop).map g))

-- Reference: [SGA4], Exposé I (contravariant functoriality of the sheaf of
-- morphisms); [Riou], `Mathlib.CategoryTheory.Sites.SheafHom`.
-- REVIEW(citation): pin the exact section of [SGA4] in review.
/-- **Pre-composition** on the underlying presheaf of `sheafHom`: a morphism
`f : F' ⟶ F` of sheaves induces `sheafHom' F G ⟶ sheafHom' F' G`, given at
`X : Cᵒᵖ` by `α ↦ (J.overPullback A X.unop).map f ≫ α`. -/
def sheafHomPrecomp (F F' G : Sheaf J A) (f : F' ⟶ F) :
    sheafHom' F G ⟶ sheafHom' F' G where
  app X := ↾(fun (α : (J.overPullback A X.unop).obj F ⟶ (J.overPullback A X.unop).obj G) =>
    (J.overPullback A X.unop).map f ≫ α)
  naturality X Y f' := by
    refine ConcreteCategory.ext_apply (fun φ => ?_)
    change (J.overPullback A Y.unop).map f ≫ (J.overMapPullback A f'.unop).map φ =
      (J.overMapPullback A f'.unop).map ((J.overPullback A X.unop).map f ≫ φ)
    -- `Functor.map_comp` splits the right factor;
    -- `overMapPullback_map_overPullback_map` rewrites the remaining factor
    -- (unique occurrence of `map` applied to `map f` in the goal).
    exact (congrArg (fun β => β ≫ (J.overMapPullback A f'.unop).map φ)
        (overMapPullback_map_overPullback_map f' f)).symm.trans
      (Functor.map_comp (J.overMapPullback A f'.unop) ((J.overPullback A X.unop).map f) φ)

-- Reference: [SGA4], Exposé I (functoriality of the sheaf of morphisms);
-- `Functor.map_id` (Limits of the diagram of sheaves) and `Category.comp_id`.
-- REVIEW(citation): pin the exact section of [SGA4] in review.
/-- **Post-composition preserves identities** at the sheaf level:
`sheafHomPostcomp` of the identity morphism is the identity natural
transformation. -/
theorem sheafHomPostcomp_id (F G : Sheaf J A) :
    sheafHomPostcomp F G G (𝟙 G) = 𝟙 (sheafHom' F G) := by
  refine NatTrans.ext (funext fun X => ConcreteCategory.ext ?_)
  refine DFunLike.ext _ _ (fun α => ?_)
  change α ≫ (J.overPullback A X.unop).map (𝟙 G) = α
  exact (congrArg (fun β => α ≫ β) (Functor.map_id (J.overPullback A X.unop) G)).trans
    (Category.comp_id α)

-- Reference: [SGA4], Exposé I (functoriality of the sheaf of morphisms);
-- `Functor.map_comp` and `Category.assoc`.
-- REVIEW(citation): pin the exact section of [SGA4] in review.
/-- **Post-composition preserves composition** at the sheaf level. -/
theorem sheafHomPostcomp_comp (F G G' G'' : Sheaf J A) (f : G ⟶ G') (g : G' ⟶ G'') :
    sheafHomPostcomp F G G'' (f ≫ g) =
      sheafHomPostcomp F G G' f ≫ sheafHomPostcomp F G' G'' g := by
  refine NatTrans.ext (funext fun X => ConcreteCategory.ext ?_)
  refine DFunLike.ext _ _ (fun α => ?_)
  change α ≫ (J.overPullback A X.unop).map (f ≫ g) =
    (α ≫ (J.overPullback A X.unop).map f) ≫ (J.overPullback A X.unop).map g
  exact (congrArg (fun β => α ≫ β)
    (Functor.map_comp (J.overPullback A X.unop) f g)).trans (Category.assoc α _ _).symm

-- Reference: [SGA4], Exposé I (contravariant functoriality of the sheaf of
-- morphisms); `Functor.map_id` and `Category.id_comp`.
-- REVIEW(citation): pin the exact section of [SGA4] in review.
/-- **Pre-composition preserves identities** at the sheaf level. -/
theorem sheafHomPrecomp_id (F G : Sheaf J A) :
    sheafHomPrecomp F F G (𝟙 F) = 𝟙 (sheafHom' F G) := by
  refine NatTrans.ext (funext fun X => ConcreteCategory.ext ?_)
  refine DFunLike.ext _ _ (fun α => ?_)
  change (J.overPullback A X.unop).map (𝟙 F) ≫ α = α
  exact (congrArg (fun β => β ≫ α) (Functor.map_id (J.overPullback A X.unop) F)).trans
    (Category.id_comp α)

-- Reference: [SGA4], Exposé I (contravariant functoriality of the sheaf of
-- morphisms); `Functor.map_comp` and `Category.assoc`.
-- REVIEW(citation): pin the exact section of [SGA4] in review.
/-- **Pre-composition reverses composition** at the sheaf level
(contravariance). -/
theorem sheafHomPrecomp_comp (F F' F'' G : Sheaf J A) (f : F' ⟶ F) (g : F'' ⟶ F') :
    sheafHomPrecomp F F'' G (g ≫ f) =
      sheafHomPrecomp F F' G f ≫ sheafHomPrecomp F' F'' G g := by
  refine NatTrans.ext (funext fun X => ConcreteCategory.ext ?_)
  refine DFunLike.ext _ _ (fun α => ?_)
  change (J.overPullback A X.unop).map (g ≫ f) ≫ α =
    (J.overPullback A X.unop).map g ≫ ((J.overPullback A X.unop).map f ≫ α)
  exact (congrArg (fun β => β ≫ α)
    (Functor.map_comp (J.overPullback A X.unop) g f)).trans (Category.assoc _ _ _)

-- Reference: [Mac Lane], Chapter III, §4 (the interchange law for composition
-- of natural transformations); [SGA4], Exposé I.
-- REVIEW(citation): pin the exact sections in review.
/-- **Interchange law** for pre- and post-composition on `sheafHom'`: the two
orders of whiskering commute, by associativity of composition. -/
theorem sheafHom_interchange (F F' G G' : Sheaf J A) (f : F' ⟶ F) (h : G ⟶ G') :
    sheafHomPostcomp F G G' h ≫ sheafHomPrecomp F F' G' f =
      sheafHomPrecomp F F' G f ≫ sheafHomPostcomp F' G G' h := by
  refine NatTrans.ext (funext fun X => ConcreteCategory.ext ?_)
  refine DFunLike.ext _ _ (fun φ => ?_)
  change (J.overPullback A X.unop).map f ≫ (φ ≫ (J.overPullback A X.unop).map h) =
    ((J.overPullback A X.unop).map f ≫ φ) ≫ (J.overPullback A X.unop).map h
  exact (Category.assoc _ _ _).symm

-- Reference: [Riou], `Mathlib.CategoryTheory.Sites.SheafHom` module docstring
-- (TODO, first bullet); [SGA4], Exposé I, §5.
-- REVIEW(citation): pin the exact section of [SGA4] in review.
/-- The **`sheafHom` functor in the second variable**: `G ↦ sheafHom F G`
(peel (a), sheaf half, covariant part). -/
def sheafHomFunctor (F : Sheaf J A) :
    Sheaf J A ⥤ Sheaf J (Type (max (max u v') v)) where
  obj G := sheafHom F G
  map g := (Sheaf.homEquiv).symm (sheafHomPostcomp F _ _ g)
  map_id G := by
    -- `ObjectProperty.hom_ext` reduces to the underlying presheaf map;
    -- `change` uses that `Sheaf.homEquiv.symm τ` has underlying map `τ`
    -- (`FullyFaithful.homEquiv` of the inclusion, `homMk`) and that
    -- `(𝟙 (sheafHom F G)).hom = 𝟙 (sheafHom' F G)` (`FullSubcategory.id_hom`).
    refine ObjectProperty.hom_ext
      (P := Presheaf.IsSheaf (A := Type (max (max u v') v)) J) ?_
    change sheafHomPostcomp F G G (𝟙 G) = 𝟙 (sheafHom' F G)
    exact sheafHomPostcomp_id F G
  map_comp f g := by
    refine ObjectProperty.hom_ext
      (P := Presheaf.IsSheaf (A := Type (max (max u v') v)) J) ?_
    change sheafHomPostcomp F _ _ (f ≫ g) =
      sheafHomPostcomp F _ _ f ≫ sheafHomPostcomp F _ _ g
    exact sheafHomPostcomp_comp F _ _ _ f g

-- Reference: [Riou], `Mathlib.CategoryTheory.Sites.SheafHom` module docstring
-- (TODO, first bullet); [SGA4], Exposé I.
-- REVIEW(citation): pin the exact section of [SGA4] in review.
/-- The **`sheafHom` bifunctor** on `Sheaf J A`, contravariant in the first
variable and covariant in the second (peel (a), sheaf half). -/
def sheafHomBifunctor :
    (Sheaf J A)ᵒᵖ ⥤ Sheaf J A ⥤ Sheaf J (Type (max (max u v') v)) where
  obj F := sheafHomFunctor F.unop
  map f :=
    { app := fun G => (Sheaf.homEquiv).symm (sheafHomPrecomp _ _ _ f.unop)
      naturality := by
        intro G G' h
        -- `ObjectProperty.hom_ext` reduces to the underlying presheaf maps;
        -- the result is the interchange law `sheafHom_interchange`.
        refine ObjectProperty.hom_ext
          (P := Presheaf.IsSheaf (A := Type (max (max u v') v)) J) ?_
        exact sheafHom_interchange _ _ _ _ f.unop h }
  map_id F := by
    refine NatTrans.ext (funext fun G => ?_)
    refine ObjectProperty.hom_ext
      (P := Presheaf.IsSheaf (A := Type (max (max u v') v)) J) ?_
    change sheafHomPrecomp F.unop F.unop G (𝟙 F.unop) = 𝟙 (sheafHom' F.unop G)
    exact sheafHomPrecomp_id F.unop G
  map_comp f g := by
    refine NatTrans.ext (funext fun G => ?_)
    refine ObjectProperty.hom_ext
      (P := Presheaf.IsSheaf (A := Type (max (max u v') v)) J) ?_
    exact sheafHomPrecomp_comp _ _ _ _ f.unop g.unop

/-! ### Peel (b): the product adjunction `(- ⨯ F) ⊣ sheafHom F` for sheaves
of types -/

-- Reference: [Mac Lane], Chapter IV, §6 (in a Cartesian closed category,
-- `- × A ⊣ (-)^A`); [SGA4], Exposé I, §5; [Stacks], Chapter 7, §7.7.
-- REVIEW(citation): pin the exact sections in review.
/-- The **product-with-`F` functor** `X ↦ X ⨯ F` on sheaves of types. -/
noncomputable def prodWith (F : Sheaf J (Type (max u v))) :
    Sheaf J (Type (max u v)) ⥤ Sheaf J (Type (max u v)) where
  -- `noncomputable`: `Limits.prod.map` is built from the chosen binary
  -- products of `Sheaf J (Type _)`.
  obj X := X ⨯ F
  map f := Limits.prod.map f (𝟙 F)
  map_id X := Limits.prod.map_id_id (X := X) (Y := F)
  map_comp f g := Limits.prod.map_comp_id f g

-- Reference: [Mac Lane], Chapter III, §4 (limits are unique up to unique
-- isomorphism); [SGA4], Exposé I (the product of sheaves of types is
-- pointwise).
-- REVIEW(citation): pin the exact sections in review.
/-- The chosen binary product `X ⨯ F` of sheaves of types is isomorphic to the
Cartesian monoidal tensor `X ⊗ F`, whose underlying presheaf is the pointwise
product (peel (b), transport between `Limits.prod` and `⊗`). -/
noncomputable def sheafProdIsoTensor (X F : Sheaf J (Type (max u v))) :
    X ⨯ F ≅ MonoidalCategory.tensorObj X F :=
  -- `noncomputable`: both sides are chosen limits.
  Limits.IsLimit.conePointUniqueUpToIso (Limits.prodIsProd X F)
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct X F)

-- Reference: [Mac Lane], Chapter III, §4 (iso laws); `Iso.inv_hom_id_app`,
-- `CategoryTheory.comp_apply`, `CategoryTheory.id_apply`.
-- REVIEW(citation): pin the exact section in review.
/-- **Pointwise cancellation of a natural isomorphism**: `e.hom.app U` after
`e.inv.app U` is the identity (primitive application of `Iso.inv_hom_id_app`). -/
theorem natIso_hom_inv_app_apply {P Q : Cᵒᵖ ⥤ Type (max u v)} (e : P ≅ Q) (U : Cᵒᵖ)
    (w : Q.obj U) : e.hom.app U (e.inv.app U w) = w := by
  have h := e.inv_hom_id_app U
  have h1 : (e.inv.app U ≫ e.hom.app U) w = e.hom.app U (e.inv.app U w) :=
    CategoryTheory.comp_apply _ _ _
  have h2 : (e.inv.app U ≫ e.hom.app U) w = w := by
    -- rewrite the unique occurrence of `e.inv.app U ≫ e.hom.app U` in the goal
    -- by `e.inv_hom_id_app U` (fully instantiated rule).
    rw [h]
    rfl
  exact h1.symm.trans h2

-- Reference: [Mac Lane], Chapter III, §4 (the canonical isomorphism between two
-- limits of the same diagram commutes with the projections);
-- `IsLimit.conePointUniqueUpToIso_hom_comp` (HasLimits.lean:272).
-- REVIEW(citation): pin the exact section in review.
/-- The canonical isomorphism `sheafProdIsoTensor` commutes with the first
projection: `e.hom ≫ fst = prod.fst`. -/
theorem sheafProdIsoTensor_hom_fst (X F : Sheaf J (Type (max u v))) :
    (sheafProdIsoTensor X F).hom ≫ CartesianMonoidalCategory.fst X F =
      Limits.prod.fst (X := X) (Y := F) :=
  Limits.IsLimit.conePointUniqueUpToIso_hom_comp (Limits.prodIsProd X F)
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct X F) ⟨Limits.WalkingPair.left⟩

-- Reference: [Mac Lane], Chapter III, §4; `IsLimit.conePointUniqueUpToIso_hom_comp`.
-- REVIEW(citation): pin the exact section in review.
/-- The canonical isomorphism `sheafProdIsoTensor` commutes with the second
projection: `e.hom ≫ snd = prod.snd`. -/
theorem sheafProdIsoTensor_hom_snd (X F : Sheaf J (Type (max u v))) :
    (sheafProdIsoTensor X F).hom ≫ CartesianMonoidalCategory.snd X F =
      Limits.prod.snd (X := X) (Y := F) :=
  Limits.IsLimit.conePointUniqueUpToIso_hom_comp (Limits.prodIsProd X F)
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct X F) ⟨Limits.WalkingPair.right⟩

-- Reference: [Mac Lane], Chapter III, §4; `IsLimit.conePointUniqueUpToIso_inv_comp`.
-- REVIEW(citation): pin the exact section in review.
/-- The inverse of `sheafProdIsoTensor` commutes with the first projection:
`e.inv ≫ prod.fst = fst`. -/
theorem sheafProdIsoTensor_inv_fst (X F : Sheaf J (Type (max u v))) :
    (sheafProdIsoTensor X F).inv ≫ Limits.prod.fst (X := X) (Y := F) =
      CartesianMonoidalCategory.fst X F :=
  Limits.IsLimit.conePointUniqueUpToIso_inv_comp (Limits.prodIsProd X F)
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct X F) ⟨Limits.WalkingPair.left⟩

-- Reference: [Mac Lane], Chapter III, §4; `IsLimit.conePointUniqueUpToIso_inv_comp`.
-- REVIEW(citation): pin the exact section in review.
/-- The inverse of `sheafProdIsoTensor` commutes with the second projection:
`e.inv ≫ prod.snd = snd`. -/
theorem sheafProdIsoTensor_inv_snd (X F : Sheaf J (Type (max u v))) :
    (sheafProdIsoTensor X F).inv ≫ Limits.prod.snd (X := X) (Y := F) =
      CartesianMonoidalCategory.snd X F :=
  Limits.IsLimit.conePointUniqueUpToIso_inv_comp (Limits.prodIsProd X F)
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct X F) ⟨Limits.WalkingPair.right⟩

-- Reference: [Mac Lane], Chapter III, §4 (uniqueness of maps out of a product);
-- `Limits.prod.map_fst`, `Limits.prod.map_snd` (BinaryProducts.lean:201,206);
-- `Functor.fst_app` (FunctorCategory.lean:84, pointwise `Prod.fst`).
-- REVIEW(citation): pin the exact section in review.
/-- **Pointwise formula for the product map**: the map
`e'⁻¹ ≫ prod.map f (𝟙 F) ≫ e` between the pointwise products of sheaves of
types is, at `U`, the map `(x, s) ↦ (f.app U x, s)`. -/
theorem sheafProdMap_app (X X' F : Sheaf J (Type (max u v))) (f : X' ⟶ X) (U : Cᵒᵖ)
    (p : X'.1.obj U × F.1.obj U) :
    ((sheafProdIsoTensor X' F).inv ≫ Limits.prod.map f (𝟙 F) ≫
        (sheafProdIsoTensor X F).hom).hom.app U p = (f.hom.app U p.1, p.2) := by
  have hfst : ((sheafProdIsoTensor X' F).inv ≫ Limits.prod.map f (𝟙 F) ≫
        (sheafProdIsoTensor X F).hom) ≫ CartesianMonoidalCategory.fst X F =
      CartesianMonoidalCategory.fst X' F ≫ f := by
    calc ((sheafProdIsoTensor X' F).inv ≫ Limits.prod.map f (𝟙 F) ≫
          (sheafProdIsoTensor X F).hom) ≫ CartesianMonoidalCategory.fst X F
        = (sheafProdIsoTensor X' F).inv ≫ Limits.prod.map f (𝟙 F) ≫
            ((sheafProdIsoTensor X F).hom ≫ CartesianMonoidalCategory.fst X F) :=
          Category.assoc _ _ _
      _ = (sheafProdIsoTensor X' F).inv ≫ Limits.prod.map f (𝟙 F) ≫
            Limits.prod.fst (X := X) (Y := F) :=
          congrArg (fun m => (sheafProdIsoTensor X' F).inv ≫ Limits.prod.map f (𝟙 F) ≫ m)
            (sheafProdIsoTensor_hom_fst X F)
      _ = (sheafProdIsoTensor X' F).inv ≫
            (Limits.prod.map f (𝟙 F) ≫ Limits.prod.fst (X := X) (Y := F)) :=
          Category.assoc _ _ _
      _ = (sheafProdIsoTensor X' F).inv ≫
            (Limits.prod.fst (X := X') (Y := F) ≫ f) :=
          congrArg (fun m => (sheafProdIsoTensor X' F).inv ≫ m)
            (Limits.prod.map_fst f (𝟙 F))
      _ = ((sheafProdIsoTensor X' F).inv ≫ Limits.prod.fst (X := X') (Y := F)) ≫ f :=
          (Category.assoc _ _ _).symm
      _ = CartesianMonoidalCategory.fst X' F ≫ f :=
          congrArg (fun m => m ≫ f) (sheafProdIsoTensor_inv_fst X' F)
  have hsnd : ((sheafProdIsoTensor X' F).inv ≫ Limits.prod.map f (𝟙 F) ≫
        (sheafProdIsoTensor X F).hom) ≫ CartesianMonoidalCategory.snd X F =
      CartesianMonoidalCategory.snd X' F := by
    calc ((sheafProdIsoTensor X' F).inv ≫ Limits.prod.map f (𝟙 F) ≫
          (sheafProdIsoTensor X F).hom) ≫ CartesianMonoidalCategory.snd X F
        = (sheafProdIsoTensor X' F).inv ≫ Limits.prod.map f (𝟙 F) ≫
            ((sheafProdIsoTensor X F).hom ≫ CartesianMonoidalCategory.snd X F) :=
          Category.assoc _ _ _
      _ = (sheafProdIsoTensor X' F).inv ≫ Limits.prod.map f (𝟙 F) ≫
            Limits.prod.snd (X := X) (Y := F) :=
          congrArg (fun m => (sheafProdIsoTensor X' F).inv ≫ Limits.prod.map f (𝟙 F) ≫ m)
            (sheafProdIsoTensor_hom_snd X F)
      _ = (sheafProdIsoTensor X' F).inv ≫
            (Limits.prod.map f (𝟙 F) ≫ Limits.prod.snd (X := X) (Y := F)) :=
          Category.assoc _ _ _
      _ = (sheafProdIsoTensor X' F).inv ≫
            (Limits.prod.snd (X := X') (Y := F) ≫ 𝟙 F) :=
          congrArg (fun m => (sheafProdIsoTensor X' F).inv ≫ m)
            (Limits.prod.map_snd f (𝟙 F))
      _ = (sheafProdIsoTensor X' F).inv ≫ Limits.prod.snd (X := X') (Y := F) :=
          congrArg (fun m => (sheafProdIsoTensor X' F).inv ≫ m) (Category.comp_id _)
      _ = CartesianMonoidalCategory.snd X' F := sheafProdIsoTensor_inv_snd X' F
  have hfst' := congrArg (·.hom) hfst
  have hsnd' := congrArg (·.hom) hsnd
  have h1 : (CartesianMonoidalCategory.fst X.1 F.1).app U
        (((sheafProdIsoTensor X' F).inv ≫ Limits.prod.map f (𝟙 F) ≫
          (sheafProdIsoTensor X F).hom).hom.app U p) = f.hom.app U p.1 :=
    ((CategoryTheory.comp_apply
        (((sheafProdIsoTensor X' F).inv ≫ Limits.prod.map f (𝟙 F) ≫
          (sheafProdIsoTensor X F).hom).hom.app U)
        ((CartesianMonoidalCategory.fst X.1 F.1).app U) p).symm).trans
      ((congrArg (· p) (NatTrans.congr_app hfst' U)).trans
        (CategoryTheory.comp_apply
          ((CartesianMonoidalCategory.fst X'.1 F.1).app U) (f.hom.app U) p))
  have h2 : (CartesianMonoidalCategory.snd X.1 F.1).app U
        (((sheafProdIsoTensor X' F).inv ≫ Limits.prod.map f (𝟙 F) ≫
          (sheafProdIsoTensor X F).hom).hom.app U p) =
      (CartesianMonoidalCategory.snd X'.1 F.1).app U p :=
    ((CategoryTheory.comp_apply
        (((sheafProdIsoTensor X' F).inv ≫ Limits.prod.map f (𝟙 F) ≫
          (sheafProdIsoTensor X F).hom).hom.app U)
        ((CartesianMonoidalCategory.snd X.1 F.1).app U) p).symm).trans
      (congrArg (· p) (NatTrans.congr_app hsnd' U))
  have h1' : (((sheafProdIsoTensor X' F).inv ≫ Limits.prod.map f (𝟙 F) ≫
        (sheafProdIsoTensor X F).hom).hom.app U p).1 = (f.hom.app U p.1, p.2).1 := h1
  have h2' : (((sheafProdIsoTensor X' F).inv ≫ Limits.prod.map f (𝟙 F) ≫
        (sheafProdIsoTensor X F).hom).hom.app U p).2 = (f.hom.app U p.1, p.2).2 := h2
  exact Prod.ext h1' h2'

-- Reference: [SGA4], Exposé I (the restriction functor is pointwise);
-- primitive definitional lemma: `(J.overPullback A X).map g` is
-- `whiskerLeft (Over.forget X).op g.hom`.
-- REVIEW(citation): pin the exact section of [SGA4] in review.
/-- Restriction of a sheaf morphism `g` at an over-object `W` is `g` at
`W.left` (primitive definitional lemma). -/
theorem overPullback_map_hom_app {X : C} {F G : Sheaf J (Type (max u v))} (g : F ⟶ G)
    (W : Over X) :
    ((J.overPullback (Type (max u v)) X).map g).hom.app (Opposite.op W) =
      g.hom.app (Opposite.op W.left) := rfl

-- Reference: [Riou], `Mathlib.CategoryTheory.Sites.SheafHom` TODO (second
-- bullet); [SGA4], Exposé I, §5 (the product with `F`, transported to the
-- pointwise tensor product of presheaves of types).
-- REVIEW(citation): pin the exact sections in review.
/-- The morphism `φ : X ⨯ F ⟶ Y` transported along `sheafProdIsoTensor` to the
pointwise product presheaf `X.1 ⊗ F.1 ⟶ Y.1` (peel (b), currying data). -/
noncomputable def sheafHomCurryTensor (F X Y : Sheaf J (Type (max u v))) (φ : X ⨯ F ⟶ Y) :
    MonoidalCategory.tensorObj X.1 F.1 ⟶ Y.1 :=
  -- `noncomputable`: `sheafProdIsoTensor` uses the chosen binary products.
  ((sheafProdIsoTensor X F).inv ≫ φ).hom

-- Reference: [Riou], `Mathlib.CategoryTheory.Sites.SheafHom` TODO (second
-- bullet); [SGA4], Exposé I, §5; [Stacks], Chapter 7, §7.7 (a morphism out of
-- the product is determined pointwise).
-- REVIEW(citation): pin the exact sections in review.
/-- The **section of the internal hom presheaf** associated to `φ : X ⨯ F ⟶ Y`
at `U` and `x : X.1.obj U`: the natural transformation
`(Over.forget U.unop).op ⋙ F.1 ⟶ (Over.forget U.unop).op ⋙ Y.1` whose component
at `op W` sends `s` to `φ` applied to `(X.map W.hom.op x, s)`. -/
noncomputable def sheafHomCurrySection (F X Y : Sheaf J (Type (max u v))) (φ : X ⨯ F ⟶ Y)
    (U : Cᵒᵖ) (x : X.1.obj U) :
    (Over.forget U.unop).op ⋙ F.1 ⟶ (Over.forget U.unop).op ⋙ Y.1 where
  app W := ↾(fun s : ((Over.forget U.unop).op ⋙ F.1).obj W =>
    (sheafHomCurryTensor F X Y φ).app (Opposite.op W.unop.left)
      (X.1.map W.unop.hom.op x, s))
  naturality := by
    intro W W' g
    refine ConcreteCategory.ext_apply (fun s => ?_)
    change (sheafHomCurryTensor F X Y φ).app (Opposite.op W'.unop.left)
          (X.1.map W'.unop.hom.op x, F.1.map g.unop.left.op s) =
      Y.1.map g.unop.left.op ((sheafHomCurryTensor F X Y φ).app (Opposite.op W.unop.left)
        (X.1.map W.unop.hom.op x, s))
    have hw : g.unop.left ≫ W.unop.hom = W'.unop.hom := Over.w g.unop
    have e2 : (g.unop.left ≫ W.unop.hom).op = W.unop.hom.op ≫ g.unop.left.op :=
      op_comp (f := g.unop.left) (g := W.unop.hom)
    have e3 : X.1.map (W.unop.hom.op ≫ g.unop.left.op) x =
        X.1.map g.unop.left.op (X.1.map W.unop.hom.op x) :=
      Functor.map_comp_apply X.1 W.unop.hom.op g.unop.left.op x
    have hx : X.1.map W'.unop.hom.op x =
        X.1.map g.unop.left.op (X.1.map W.unop.hom.op x) :=
      (congrArg (fun k : W'.unop.left ⟶ U.unop => X.1.map k.op x) hw.symm).trans
        ((congrArg (fun k : Opposite.op U.unop ⟶ Opposite.op W'.unop.left =>
          X.1.map k x) e2).trans
          e3)
    have hnraw : ((MonoidalCategory.tensorObj X.1 F.1).map g.unop.left.op ≫
          (sheafHomCurryTensor F X Y φ).app (Opposite.op W'.unop.left))
        ((X.1.map W.unop.hom.op x, s) :
          (MonoidalCategory.tensorObj X.1 F.1).obj (Opposite.op W.unop.left)) =
        ((sheafHomCurryTensor F X Y φ).app (Opposite.op W.unop.left) ≫ Y.1.map g.unop.left.op)
        ((X.1.map W.unop.hom.op x, s) :
          (MonoidalCategory.tensorObj X.1 F.1).obj (Opposite.op W.unop.left)) :=
      ConcreteCategory.congr_hom
        ((sheafHomCurryTensor F X Y φ).naturality g.unop.left.op)
        ((X.1.map W.unop.hom.op x, s) :
          (MonoidalCategory.tensorObj X.1 F.1).obj (Opposite.op W.unop.left))
    have hL := CategoryTheory.comp_apply
      ((MonoidalCategory.tensorObj X.1 F.1).map g.unop.left.op)
      ((sheafHomCurryTensor F X Y φ).app (Opposite.op W'.unop.left))
      ((X.1.map W.unop.hom.op x, s) :
        (MonoidalCategory.tensorObj X.1 F.1).obj (Opposite.op W.unop.left))
    have hR := CategoryTheory.comp_apply
      ((sheafHomCurryTensor F X Y φ).app (Opposite.op W.unop.left)) (Y.1.map g.unop.left.op)
      ((X.1.map W.unop.hom.op x, s) :
        (MonoidalCategory.tensorObj X.1 F.1).obj (Opposite.op W.unop.left))
    have hn : Y.1.map g.unop.left.op ((sheafHomCurryTensor F X Y φ).app (Opposite.op W.unop.left)
          (X.1.map W.unop.hom.op x, s)) =
        (sheafHomCurryTensor F X Y φ).app (Opposite.op W'.unop.left)
          ((MonoidalCategory.tensorObj X.1 F.1).map g.unop.left.op
            (X.1.map W.unop.hom.op x, s)) :=
      hR.symm.trans (hnraw.symm.trans hL)
    have hp : (MonoidalCategory.tensorObj X.1 F.1).map g.unop.left.op
          (X.1.map W.unop.hom.op x, s) =
        (X.1.map g.unop.left.op (X.1.map W.unop.hom.op x), F.1.map g.unop.left.op s) := rfl
    exact (congrArg (fun a => (sheafHomCurryTensor F X Y φ).app (Opposite.op W'.unop.left)
        (a, F.1.map g.unop.left.op s)) hx).trans
      ((congrArg (fun p => (sheafHomCurryTensor F X Y φ).app (Opposite.op W'.unop.left)
          p) hp).trans hn.symm)

-- Reference: [Riou], `Mathlib.CategoryTheory.Sites.SheafHom` TODO (second
-- bullet); [SGA4], Exposé I, §5.
-- REVIEW(citation): pin the exact sections in review.
/-- The **presheaf-level currying**: `φ : X ⨯ F ⟶ Y` induces the natural
transformation `X.1 ⟶ presheafHom F.1 Y.1` (peel (b)). -/
noncomputable def sheafHomCurryVal (F X Y : Sheaf J (Type (max u v))) (φ : X ⨯ F ⟶ Y) :
    X.1 ⟶ presheafHom F.1 Y.1 where
  app U := ↾(fun x : X.1.obj U => sheafHomCurrySection F X Y φ U x)
  naturality U V f := by
    refine ConcreteCategory.ext_apply (fun x => ?_)
    refine NatTrans.ext (funext fun W => ConcreteCategory.ext ?_)
    refine DFunLike.ext _ _ (fun s => ?_)
    change (sheafHomCurryTensor F X Y φ).app (Opposite.op W.unop.left)
          (X.1.map W.unop.hom.op (X.1.map f x), s) =
      (((presheafHom F.1 Y.1).map f (sheafHomCurrySection F X Y φ U x)).app W) s
    have hpm : ((presheafHom F.1 Y.1).map f (sheafHomCurrySection F X Y φ U x)).app
          (Opposite.op (Over.mk W.unop.hom)) =
        (sheafHomCurrySection F X Y φ U x).app
          (Opposite.op (Over.mk (W.unop.hom ≫ f.unop))) :=
      presheafHom_map_app W.unop.hom f.unop (W.unop.hom ≫ f.unop) rfl
        (sheafHomCurrySection F X Y φ U x)
    have hx2 : X.1.map W.unop.hom.op (X.1.map f x) =
        X.1.map (W.unop.hom ≫ f.unop).op x :=
      ((Functor.map_comp_apply X.1 f W.unop.hom.op x).symm).trans
        ((congrArg (fun k : Opposite.op U.unop ⟶ Opposite.op W.unop.left => X.1.map k x)
          (op_comp (f := W.unop.hom) (g := f.unop))).symm)
    exact (congrArg (fun a => (sheafHomCurryTensor F X Y φ).app (Opposite.op W.unop.left)
        (a, s)) hx2).trans (ConcreteCategory.congr_hom hpm s).symm

-- Reference: [Riou], `Mathlib.CategoryTheory.Sites.SheafHom` TODO (second
-- bullet); [SGA4], Exposé I, §5; [Stacks], Chapter 7, §7.7.
-- REVIEW(citation): pin the exact sections in review.
/-- The **presheaf-level uncurrying**: `ψ : X ⟶ sheafHom F Y` induces the
natural transformation `X.1 ⊗ F.1 ⟶ Y.1` sending `(x, s)` at `U` to the value
of the internal-hom section `ψ.app U x` at `Over.mk (𝟙 U.unop)` applied to `s`
(peel (b)). -/
def sheafHomUncurryVal (F X Y : Sheaf J (Type (max u v))) (ψ : X ⟶ sheafHom F Y) :
    MonoidalCategory.tensorObj X.1 F.1 ⟶ Y.1 where
  app U := ↾(fun p : X.1.obj U × F.1.obj U =>
    (((sheafHom'Iso F Y).hom.app U (ψ.hom.app U p.1)).app
      (Opposite.op (Over.mk (𝟙 U.unop)))) p.2)
  naturality U V f := by
    refine ConcreteCategory.ext_apply (fun p => ?_)
    change (((sheafHom'Iso F Y).hom.app V (ψ.hom.app V (X.1.map f p.1))).app
          (Opposite.op (Over.mk (𝟙 V.unop)))) (F.1.map f p.2) =
      Y.1.map f ((((sheafHom'Iso F Y).hom.app U (ψ.hom.app U p.1)).app
        (Opposite.op (Over.mk (𝟙 U.unop)))) p.2)
    have h1 : ψ.hom.app V (X.1.map f p.1) =
        (sheafHom' F Y).map f (ψ.hom.app U p.1) :=
      ConcreteCategory.congr_hom (ψ.hom.naturality f) p.1
    have h2 : ((sheafHom'Iso F Y).hom.app V ((sheafHom' F Y).map f (ψ.hom.app U p.1))) =
        (presheafHom F.1 Y.1).map f ((sheafHom'Iso F Y).hom.app U (ψ.hom.app U p.1)) :=
      ConcreteCategory.congr_hom ((sheafHom'Iso F Y).hom.naturality f) (ψ.hom.app U p.1)
    have h3 : ((presheafHom F.1 Y.1).map f
          ((sheafHom'Iso F Y).hom.app U (ψ.hom.app U p.1))).app
          (Opposite.op (Over.mk (𝟙 V.unop))) =
        ((sheafHom'Iso F Y).hom.app U (ψ.hom.app U p.1)).app (Opposite.op (Over.mk f.unop)) :=
      presheafHom_map_app_op_mk_id f.unop _
    have h4 : ((sheafHom'Iso F Y).hom.app U (ψ.hom.app U p.1)).app
          (Opposite.op (Over.mk f.unop)) (F.1.map f p.2) =
        Y.1.map f (((sheafHom'Iso F Y).hom.app U (ψ.hom.app U p.1)).app
          (Opposite.op (Over.mk (𝟙 U.unop))) p.2) :=
      ConcreteCategory.congr_hom
        (((sheafHom'Iso F Y).hom.app U (ψ.hom.app U p.1)).naturality
          ((Over.homMk (U := Over.mk f.unop) (V := Over.mk (𝟙 U.unop)) f.unop
            (Category.comp_id f.unop)).op)) p.2
    exact (congrArg (fun α => ((sheafHom'Iso F Y).hom.app V α).app
          (Opposite.op (Over.mk (𝟙 V.unop))) (F.1.map f p.2)) h1).trans
      ((congrArg (fun β => β.app (Opposite.op (Over.mk (𝟙 V.unop))) (F.1.map f p.2)) h2).trans
        ((congrArg (fun γ => γ (F.1.map f p.2)) h3).trans h4))

-- Reference: [Riou], `Mathlib.CategoryTheory.Sites.SheafHom` TODO (second
-- bullet, verbatim in issue #41); [SGA4], Exposé I, §5; [Stacks], Chapter 7,
-- §7.7 (the exponential of sheaves of sets).
-- REVIEW(citation): pin the exact sections in review.
/-- **Currying** for sheaves of types: a morphism `φ : X ⨯ F ⟶ Y` transposes
to `X ⟶ sheafHom F Y` (peel (b), forward direction of
`sheafHomProdHomEquiv`). -/
noncomputable def sheafHomCurry (F X Y : Sheaf J (Type (max u v))) (φ : X ⨯ F ⟶ Y) :
    X ⟶ sheafHom F Y :=
  -- `noncomputable`: `sheafProdIsoTensor` uses the chosen binary products.
  (Sheaf.homEquiv).symm (sheafHomCurryVal F X Y φ ≫ (sheafHom'Iso F Y).inv)

-- Reference: [Riou], `Mathlib.CategoryTheory.Sites.SheafHom` TODO (second
-- bullet); [SGA4], Exposé I, §5; [Stacks], Chapter 7, §7.7.
-- REVIEW(citation): pin the exact sections in review.
/-- **Uncurrying**: a morphism `ψ : X ⟶ sheafHom F Y` transposes to
`X ⨯ F ⟶ Y` (peel (b), backward direction of `sheafHomProdHomEquiv`). -/
noncomputable def sheafHomUncurry (F X Y : Sheaf J (Type (max u v))) (ψ : X ⟶ sheafHom F Y) :
    X ⨯ F ⟶ Y :=
  -- `noncomputable`: `sheafProdIsoTensor` uses the chosen binary products.
  (sheafProdIsoTensor X F).hom ≫ (Sheaf.homEquiv).symm (sheafHomUncurryVal F X Y ψ)

-- Reference: [Mac Lane], Chapter III, §4 (iso laws); `Iso.hom_inv_id` and
-- `FullSubcategory.comp_hom` (both rfl).
-- REVIEW(citation): pin the exact section in review.
/-- The underlying presheaf map of `sheafProdIsoTensor.hom ≫ sheafProdIsoTensor.inv`
is the identity (primitive application of `Iso.hom_inv_id`). -/
theorem sheafProdIsoTensor_hom_inv_hom (X F : Sheaf J (Type (max u v))) :
    (sheafProdIsoTensor X F).hom.hom ≫ (sheafProdIsoTensor X F).inv.hom = 𝟙 (X ⨯ F).1 :=
  congrArg (·.hom) (Iso.hom_inv_id (sheafProdIsoTensor X F))

-- Reference: [Mac Lane], Chapter III, §4 (iso laws); `Iso.inv_hom_id`.
-- REVIEW(citation): pin the exact section in review.
/-- The underlying presheaf map of `sheafProdIsoTensor.inv ≫ sheafProdIsoTensor.hom`
is the identity (primitive application of `Iso.inv_hom_id`). -/
theorem sheafProdIsoTensor_inv_hom_hom (X F : Sheaf J (Type (max u v))) :
    (sheafProdIsoTensor X F).inv.hom ≫ (sheafProdIsoTensor X F).hom.hom =
      𝟙 (MonoidalCategory.tensorObj X F).1 :=
  congrArg (·.hom) (Iso.inv_hom_id (sheafProdIsoTensor X F))

-- Reference: [Riou], `Mathlib.CategoryTheory.Sites.SheafHom` TODO (second
-- bullet); [SGA4], Exposé I, §5; `natIso_hom_inv_app_apply`,
-- `Functor.map_id_apply`, `Prod.eta`, `presheafHom_map_app_op_mk_id`.
-- REVIEW(citation): pin the exact sections in review.
/-- **Uncurrying a curried morphism at the presheaf level** (peel (b)): the
uncurried underlying map of `curry φ` is the transported `φ` itself. -/
theorem sheafHomUncurryVal_curry (F X Y : Sheaf J (Type (max u v))) (φ : X ⨯ F ⟶ Y) :
    sheafHomUncurryVal F X Y (sheafHomCurry F X Y φ) = sheafHomCurryTensor F X Y φ := by
  refine NatTrans.ext (funext fun U => ConcreteCategory.ext ?_)
  refine DFunLike.ext _ _ (fun p => ?_)
  change (((sheafHom'Iso F Y).hom.app U ((sheafHomCurry F X Y φ).hom.app U p.1)).app
        (Opposite.op (Over.mk (𝟙 U.unop)))) p.2 = (sheafHomCurryTensor F X Y φ).app U p
  have h0 : ((sheafHom'Iso F Y).hom.app U ((sheafHomCurry F X Y φ).hom.app U p.1)) =
      sheafHomCurrySection F X Y φ U p.1 :=
    natIso_hom_inv_app_apply (sheafHom'Iso F Y) U (sheafHomCurryVal F X Y φ |>.app U p.1)
  have h1 : (sheafHomCurrySection F X Y φ U p.1).app (Opposite.op (Over.mk (𝟙 U.unop))) p.2 =
      (sheafHomCurryTensor F X Y φ).app (Opposite.op U.unop)
        (X.1.map (𝟙 U.unop).op p.1, p.2) := rfl
  have h2 : X.1.map (𝟙 U.unop).op p.1 = p.1 := Functor.map_id_apply X.1 (Opposite.op U.unop) p.1
  have h3 : (X.1.map (𝟙 U.unop).op p.1, p.2) = p :=
    (congrArg (fun a => (a, p.2)) h2).trans (Prod.eta p)
  exact (congrArg (fun γ => γ.app (Opposite.op (Over.mk (𝟙 U.unop))) p.2) h0).trans
    (h1.trans (congrArg (fun q => (sheafHomCurryTensor F X Y φ).app U q) h3))

-- Reference: [Riou], `Mathlib.CategoryTheory.Sites.SheafHom` TODO (second
-- bullet); [SGA4], Exposé I, §5; `sheafProdIsoTensor_inv_hom_hom`,
-- `ψ.hom.naturality`, `presheafHom_map_app_op_mk_id`.
-- REVIEW(citation): pin the exact sections in review.
/-- **Currying an uncurried morphism at the presheaf level** (peel (b)). -/
theorem sheafHomCurryVal_uncurry (F X Y : Sheaf J (Type (max u v))) (ψ : X ⟶ sheafHom F Y) :
    sheafHomCurryVal F X Y (sheafHomUncurry F X Y ψ) =
      ψ.hom ≫ (sheafHom'Iso F Y).hom := by
  refine NatTrans.ext (funext fun U => ConcreteCategory.ext ?_)
  refine DFunLike.ext _ _ (fun x => ?_)
  refine NatTrans.ext (funext fun W => ConcreteCategory.ext ?_)
  refine DFunLike.ext _ _ (fun s => ?_)
  change (sheafHomCurryTensor F X Y (sheafHomUncurry F X Y ψ)).app (Opposite.op W.unop.left)
        (X.1.map W.unop.hom.op x, s) =
      (((sheafHom'Iso F Y).hom.app U (ψ.hom.app U x)).app W) s
  have hT : sheafHomCurryTensor F X Y (sheafHomUncurry F X Y ψ) =
      sheafHomUncurryVal F X Y ψ := by
    change (sheafProdIsoTensor X F).inv.hom ≫
        ((sheafProdIsoTensor X F).hom.hom ≫ sheafHomUncurryVal F X Y ψ) =
      sheafHomUncurryVal F X Y ψ
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun m => m ≫ sheafHomUncurryVal F X Y ψ)
          (sheafProdIsoTensor_inv_hom_hom X F)).trans (Category.id_comp _))
  have h1 : ψ.hom.app (Opposite.op W.unop.left) (X.1.map W.unop.hom.op x) =
      (sheafHom' F Y).map W.unop.hom.op (ψ.hom.app U x) :=
    ConcreteCategory.congr_hom (ψ.hom.naturality W.unop.hom.op) x
  have h2 : (sheafHom'Iso F Y).hom.app (Opposite.op W.unop.left)
        ((sheafHom' F Y).map W.unop.hom.op (ψ.hom.app U x)) =
      (presheafHom F.1 Y.1).map W.unop.hom.op
        ((sheafHom'Iso F Y).hom.app U (ψ.hom.app U x)) :=
    ConcreteCategory.congr_hom ((sheafHom'Iso F Y).hom.naturality W.unop.hom.op) (ψ.hom.app U x)
  have h3 : ((presheafHom F.1 Y.1).map W.unop.hom.op
        ((sheafHom'Iso F Y).hom.app U (ψ.hom.app U x))).app
          (Opposite.op (Over.mk (𝟙 W.unop.left))) =
      ((sheafHom'Iso F Y).hom.app U (ψ.hom.app U x)).app (Opposite.op (Over.mk W.unop.hom)) :=
    presheafHom_map_app_op_mk_id W.unop.hom _
  exact (congrArg (fun ν => ν.app (Opposite.op W.unop.left)
      (X.1.map W.unop.hom.op x, s)) hT).trans
    ((congrArg (fun α => ((sheafHom'Iso F Y).hom.app (Opposite.op W.unop.left) α).app
          (Opposite.op (Over.mk (𝟙 W.unop.left))) s) h1).trans
      ((congrArg (fun β => β.app (Opposite.op (Over.mk (𝟙 W.unop.left))) s) h2).trans
        (congrArg (fun γ => γ s) h3)))

-- Reference: [Riou], `Mathlib.CategoryTheory.Sites.SheafHom` TODO (second
-- bullet); [SGA4], Exposé I, §5.
-- REVIEW(citation): pin the exact sections in review.
/-- The two transpositions are inverse: uncurrying a curried morphism returns
the original morphism. -/
theorem sheafHomUncurry_curry (F X Y : Sheaf J (Type (max u v))) (φ : X ⨯ F ⟶ Y) :
    sheafHomUncurry F X Y (sheafHomCurry F X Y φ) = φ := by
  refine ObjectProperty.hom_ext (P := Presheaf.IsSheaf (A := Type (max u v)) J) ?_
  change (sheafProdIsoTensor X F).hom.hom ≫
      sheafHomUncurryVal F X Y (sheafHomCurry F X Y φ) = φ.hom
  have hkey := sheafHomUncurryVal_curry F X Y φ
  exact (congrArg (fun ν => (sheafProdIsoTensor X F).hom.hom ≫ ν) hkey).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun m => m ≫ φ.hom) (sheafProdIsoTensor_hom_inv_hom X F)).trans
        (Category.id_comp φ.hom)))

-- Reference: [Riou], `Mathlib.CategoryTheory.Sites.SheafHom` TODO (second
-- bullet); [SGA4], Exposé I, §5.
-- REVIEW(citation): pin the exact sections in review.
/-- The two transpositions are inverse: currying an uncurried morphism
returns the original morphism. -/
theorem sheafHomCurry_uncurry (F X Y : Sheaf J (Type (max u v)))
    (ψ : X ⟶ sheafHom F Y) :
    sheafHomCurry F X Y (sheafHomUncurry F X Y ψ) = ψ := by
  refine ObjectProperty.hom_ext (P := Presheaf.IsSheaf (A := Type (max u v)) J) ?_
  change sheafHomCurryVal F X Y (sheafHomUncurry F X Y ψ) ≫ (sheafHom'Iso F Y).inv = ψ.hom
  have hkey := sheafHomCurryVal_uncurry F X Y ψ
  exact (congrArg (fun σ => σ ≫ (sheafHom'Iso F Y).inv) hkey).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun m => ψ.hom ≫ m) (Iso.hom_inv_id (sheafHom'Iso F Y))).trans
        (Category.comp_id ψ.hom)))

-- Reference: [Riou], `Mathlib.CategoryTheory.Sites.SheafHom` TODO (second
-- bullet: "for all `X` and `Y`, there is a natural bijection
-- `(X ⨯ F ⟶ Y) ≃ (X ⟶ sheafHom F Y)`"); [SGA4], Exposé I, §5.
-- REVIEW(citation): pin the exact sections in review.
/-- The **natural bijection** `(X ⨯ F ⟶ Y) ≃ (X ⟶ sheafHom F Y)` for sheaves
of types (peel (b), core). -/
noncomputable def sheafHomProdHomEquiv (F X Y : Sheaf J (Type (max u v))) :
    (X ⨯ F ⟶ Y) ≃ (X ⟶ sheafHom F Y) where
  -- `noncomputable`: `sheafHomCurry`/`sheafHomUncurry` use the chosen binary
  -- products via `sheafProdIsoTensor`.
  toFun := sheafHomCurry F X Y
  invFun := sheafHomUncurry F X Y
  left_inv := sheafHomUncurry_curry F X Y
  right_inv := sheafHomCurry_uncurry F X Y

-- Reference: [Riou], `Mathlib.CategoryTheory.Sites.SheafHom` TODO (second
-- bullet); [Mac Lane], Chapter IV, §6 (naturality of the adjunction bijection);
-- `sheafProdMap_app` (the pointwise formula for `prod.map f (𝟙 F)`).
-- REVIEW(citation): pin the exact sections in review.
/-- **Uncurrying is natural in the left variable** (peel (b)): precomposition
with `prod.map f (𝟙 F)` corresponds to precomposition with `f` on the
internal-hom side. -/
theorem sheafHomUncurryVal_naturality_left (F X X' Y : Sheaf J (Type (max u v)))
    (f : X' ⟶ X) (g : X ⟶ sheafHom F Y) :
    sheafHomUncurryVal F X' Y (f ≫ g) =
      ((sheafProdIsoTensor X' F).inv ≫ Limits.prod.map f (𝟙 F) ≫
          (sheafProdIsoTensor X F).hom).hom ≫ sheafHomUncurryVal F X Y g := by
  refine NatTrans.ext (funext fun U => ConcreteCategory.ext ?_)
  refine DFunLike.ext _ _ (fun p => ?_)
  change (((sheafHom'Iso F Y).hom.app U ((f ≫ g).hom.app U p.1)).app
        (Opposite.op (Over.mk (𝟙 U.unop)))) p.2 =
      ((sheafHomUncurryVal F X Y g).app U
        (((sheafProdIsoTensor X' F).inv ≫ Limits.prod.map f (𝟙 F) ≫
          (sheafProdIsoTensor X F).hom).hom.app U p))
  have hfg : (f ≫ g).hom.app U p.1 = g.hom.app U (f.hom.app U p.1) :=
    CategoryTheory.comp_apply (f.hom.app U) (g.hom.app U) p.1
  have hpm := sheafProdMap_app X X' F f U p
  exact (congrArg (fun α => ((sheafHom'Iso F Y).hom.app U α).app
        (Opposite.op (Over.mk (𝟙 U.unop))) p.2) hfg).trans
    ((congrArg (fun q => (sheafHomUncurryVal F X Y g).app U q) hpm).symm)

-- Reference: [Riou], `Mathlib.CategoryTheory.Sites.SheafHom` TODO (second
-- bullet); [Mac Lane], Chapter IV, §6; `sheafHomUncurryVal_naturality_left` and
-- `sheafProdIsoTensor_hom_inv_hom`.
-- REVIEW(citation): pin the exact sections in review.
/-- **Uncurrying is natural in the left variable** (peel (b), sheaf level). -/
theorem sheafHomUncurry_naturality_left (F X X' Y : Sheaf J (Type (max u v)))
    (f : X' ⟶ X) (g : X ⟶ sheafHom F Y) :
    sheafHomUncurry F X' Y (f ≫ g) =
      Limits.prod.map f (𝟙 F) ≫ sheafHomUncurry F X Y g := by
  refine ObjectProperty.hom_ext (P := Presheaf.IsSheaf (A := Type (max u v)) J) ?_
  change (sheafProdIsoTensor X' F).hom.hom ≫ sheafHomUncurryVal F X' Y (f ≫ g) =
    (Limits.prod.map f (𝟙 F)).hom ≫
      ((sheafProdIsoTensor X F).hom.hom ≫ sheafHomUncurryVal F X Y g)
  have h := sheafHomUncurryVal_naturality_left F X X' Y f g
  have hcancel : (sheafProdIsoTensor X' F).hom.hom ≫ (sheafProdIsoTensor X' F).inv.hom =
      𝟙 (X' ⨯ F).1 := sheafProdIsoTensor_hom_inv_hom X' F
  have htau : (sheafProdIsoTensor X' F).hom.hom ≫
      ((sheafProdIsoTensor X' F).inv ≫ Limits.prod.map f (𝟙 F) ≫
        (sheafProdIsoTensor X F).hom).hom =
      (Limits.prod.map f (𝟙 F)).hom ≫ (sheafProdIsoTensor X F).hom.hom := by
    calc (sheafProdIsoTensor X' F).hom.hom ≫
          ((sheafProdIsoTensor X' F).inv ≫ Limits.prod.map f (𝟙 F) ≫
            (sheafProdIsoTensor X F).hom).hom
        = (sheafProdIsoTensor X' F).hom.hom ≫
            ((sheafProdIsoTensor X' F).inv.hom ≫
              ((Limits.prod.map f (𝟙 F)).hom ≫ (sheafProdIsoTensor X F).hom.hom)) := rfl
      _ = ((sheafProdIsoTensor X' F).hom.hom ≫ (sheafProdIsoTensor X' F).inv.hom) ≫
            ((Limits.prod.map f (𝟙 F)).hom ≫ (sheafProdIsoTensor X F).hom.hom) :=
          (Category.assoc _ _ _).symm
      _ = 𝟙 (X' ⨯ F).1 ≫ ((Limits.prod.map f (𝟙 F)).hom ≫
            (sheafProdIsoTensor X F).hom.hom) :=
          congrArg (fun m => m ≫ _) hcancel
      _ = (Limits.prod.map f (𝟙 F)).hom ≫ (sheafProdIsoTensor X F).hom.hom :=
          Category.id_comp _
  calc (sheafProdIsoTensor X' F).hom.hom ≫ sheafHomUncurryVal F X' Y (f ≫ g)
      = (sheafProdIsoTensor X' F).hom.hom ≫
          (((sheafProdIsoTensor X' F).inv ≫ Limits.prod.map f (𝟙 F) ≫
            (sheafProdIsoTensor X F).hom).hom ≫ sheafHomUncurryVal F X Y g) :=
        congrArg (fun ν => (sheafProdIsoTensor X' F).hom.hom ≫ ν) h
    _ = ((sheafProdIsoTensor X' F).hom.hom ≫
          ((sheafProdIsoTensor X' F).inv ≫ Limits.prod.map f (𝟙 F) ≫
            (sheafProdIsoTensor X F).hom).hom) ≫ sheafHomUncurryVal F X Y g :=
        (Category.assoc _ _ _).symm
    _ = ((Limits.prod.map f (𝟙 F)).hom ≫ (sheafProdIsoTensor X F).hom.hom) ≫
          sheafHomUncurryVal F X Y g := congrArg (fun m => m ≫ _) htau
    _ = (Limits.prod.map f (𝟙 F)).hom ≫
          ((sheafProdIsoTensor X F).hom.hom ≫ sheafHomUncurryVal F X Y g) :=
        Category.assoc _ _ _

-- Reference: [Riou], `Mathlib.CategoryTheory.Sites.SheafHom` TODO (second
-- bullet); [Mac Lane], Chapter IV, §6 (naturality of the adjunction bijection);
-- `sheafHomPostcomp`, `overPullback_map_hom_app`.
-- REVIEW(citation): pin the exact sections in review.
/-- **Currying is natural in the right variable at the presheaf level** (peel
(b)): postcomposition with `g` on `Y` corresponds to `sheafHomPostcomp`. -/
theorem sheafHomCurryVal_naturality_right (F X Y Y' : Sheaf J (Type (max u v)))
    (f : X ⨯ F ⟶ Y) (g : Y ⟶ Y') :
    sheafHomCurryVal F X Y' (f ≫ g) ≫ (sheafHom'Iso F Y').inv =
      sheafHomCurryVal F X Y f ≫ (sheafHom'Iso F Y).inv ≫ sheafHomPostcomp F Y Y' g := by
  refine NatTrans.ext (funext fun U => ConcreteCategory.ext ?_)
  refine DFunLike.ext _ _ (fun x => ?_)
  refine ObjectProperty.hom_ext
    (P := Presheaf.IsSheaf (A := Type (max u v)) (J.over U.unop)) ?_
  refine NatTrans.ext (funext fun W => ConcreteCategory.ext ?_)
  refine DFunLike.ext _ _ (fun s => ?_)
  change (sheafHomCurryTensor F X Y' (f ≫ g)).app (Opposite.op W.unop.left)
        (X.1.map W.unop.hom.op x, s) =
      g.hom.app (Opposite.op W.unop.left)
        ((sheafHomCurryTensor F X Y f).app (Opposite.op W.unop.left)
          (X.1.map W.unop.hom.op x, s))
  have hfg : sheafHomCurryTensor F X Y' (f ≫ g) =
      (sheafHomCurryTensor F X Y f) ≫ g.hom := rfl
  have hcomp : (((sheafHomCurryTensor F X Y f) ≫ g.hom).app (Opposite.op W.unop.left))
        (X.1.map W.unop.hom.op x, s) =
      g.hom.app (Opposite.op W.unop.left)
        ((sheafHomCurryTensor F X Y f).app (Opposite.op W.unop.left)
          (X.1.map W.unop.hom.op x, s)) :=
    CategoryTheory.comp_apply _ _ _
  exact (congrArg (fun ν => ν.app (Opposite.op W.unop.left)
      (X.1.map W.unop.hom.op x, s)) hfg).trans hcomp

-- Reference: [Riou], `Mathlib.CategoryTheory.Sites.SheafHom` TODO (second
-- bullet); [Mac Lane], Chapter IV, §6; `sheafHomCurryVal_naturality_right`.
-- REVIEW(citation): pin the exact sections in review.
/-- **Currying is natural in the right variable** (peel (b), sheaf level). -/
theorem sheafHomCurry_naturality_right (F X Y Y' : Sheaf J (Type (max u v)))
    (f : X ⨯ F ⟶ Y) (g : Y ⟶ Y') :
    sheafHomCurry F X Y' (f ≫ g) =
      sheafHomCurry F X Y f ≫
        (sheafHomFunctor (A := Type (max u v)) F).map g := by
  refine Sheaf.homEquiv.injective ?_
  exact sheafHomCurryVal_naturality_right F X Y Y' f g

-- Reference: [Riou], `Mathlib.CategoryTheory.Sites.SheafHom` TODO (second
-- bullet); [Mac Lane], Chapter IV, §6.
-- REVIEW(citation): pin the exact sections in review.
/-- **The product adjunction** for sheaves of types (peel (b)):
`(- ⨯ F) ⊣ sheafHom F`. -/
noncomputable def sheafHomAdjunction (F : Sheaf J (Type (max u v))) :
    prodWith F ⊣ sheafHomFunctor (A := Type (max u v)) F :=
  -- `noncomputable`: the body depends on `prodWith`, whose maps use the
  -- chosen binary products of `Sheaf J (Type _)`.
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y => sheafHomProdHomEquiv F X Y
      homEquiv_naturality_left_symm := by
        intro X' X Y f g
        exact sheafHomUncurry_naturality_left F X X' Y f g
      homEquiv_naturality_right := by
        intro X Y Y' f g
        exact sheafHomCurry_naturality_right F X Y Y' f g }

/-! ### Peel (c): Cartesian closedness of `Sheaf J (Type _)` -/

-- Reference: [Stacks], Chapter 7 "Sites and Sheaves" (tag 00UZ), §7.7
-- "Sheaves" (tag 00VL); [MM], Chapter I, §5; [SGA4], Exposé I.
-- REVIEW(citation): pin the exact Stacks lemma (Cartesian closedness of
-- sheaves of sets) in review.
/-- **Sheaves of types are Cartesian closed** (peel (c)): at this pin,
"Cartesian closed" means `CartesianMonoidalCategory` together with
`MonoidalClosed` (see `Mathlib.CategoryTheory.Monoidal.Closed.Cartesian`).
Both hold for `Sheaf J (Type (max u v))`: the monoidal structure comes from
`Mathlib.CategoryTheory.Sites.CartesianMonoidal`, and `MonoidalClosed` from
`Mathlib.CategoryTheory.Sites.CartesianClosed` via
`HasSheafify J (Type (max u v))` and
`MonoidalClosed (Cᵒᵖ ⥤ Type (max u v))`. -/
noncomputable instance sheafTypesMonoidalClosed :
    MonoidalClosed (Sheaf J (Type (max u v))) :=
  -- `noncomputable`: the Mathlib instance goes through the chosen
  -- sheafification (`HasSheafify`).
  inferInstance

-- Reference: [Mac Lane], Chapter IV, §6 (a functor with a right adjoint is a
-- left adjoint; exponentiable objects).
-- REVIEW(citation): pin the exact section in review.
/-- Peel (b) rephrased: the product functor `prodWith F` **has a right
adjoint**, namely `sheafHom F` — every sheaf of types is exponentiable. -/
theorem prodWith_isLeftAdjoint (F : Sheaf J (Type (max u v))) :
    (prodWith F).IsLeftAdjoint :=
  ⟨sheafHomFunctor (A := Type (max u v)) F, ⟨sheafHomAdjunction F⟩⟩

-- Reference: [Mac Lane], Chapter III, §4 (the braiding of products and naturality
-- of `tensorLeftIsoProd`); [SGA4], Exposé I, §5.
-- REVIEW(citation): pin the exact sections in review.
/-- The product-with-`F` functor `prodWith F` (`X ↦ X ⨯ F`) is naturally
isomorphic to `tensorLeft F` (`X ↦ F ⊗ X`), via the braiding of products and
`tensorLeftIsoProd` (peel (c), transport). -/
noncomputable def prodWithIsoTensorLeft (F : Sheaf J (Type (max u v))) :
    prodWith F ≅ MonoidalCategory.tensorLeft F :=
  -- `noncomputable`: both functors use the chosen binary products.
  NatIso.ofComponents
    (fun X =>
      (Limits.prod.braiding X F) ≪≫
        ((CartesianMonoidalCategory.tensorLeftIsoProd F).app X).symm)
    (by
      intro X Y f
      have h1 := Limits.braid_natural f (𝟙 F)
      have h2 := (CartesianMonoidalCategory.tensorLeftIsoProd F).inv.naturality f
      exact ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun m => m ≫ ((CartesianMonoidalCategory.tensorLeftIsoProd F).app Y).inv)
            h1).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (fun m => (Limits.prod.braiding X F).hom ≫ m) h2).trans
              (Category.assoc _ _ _).symm)))))

-- Reference: [Riou], `Mathlib.CategoryTheory.Sites.SheafHom` TODO (third
-- bullet); [SGA4], Exposé I, §5.
-- REVIEW(citation): pin the exact sections in review.
/-- The internal hom of sheaves of types **is** `sheafHom` (peel (c)): by
uniqueness of right adjoints, `sheafHom F` is isomorphic to the internal hom
`F ⟹ -` of the Cartesian closed structure. -/
noncomputable def sheafHom_iso_internalHom (F G : Sheaf J (Type (max u v))) :
    sheafHom F G ≅ (MonoidalClosed.internalHom.obj (Opposite.op F)).obj G := by
  -- `noncomputable`: the statement's right-hand side is the chosen internal
  -- hom, which depends on the (chosen) sheafification underlying the
  -- `MonoidalClosed (Sheaf J (Type _))` instance.
  -- PEELING: `prodWithIsoTensorLeft` transports `prodWith F` to
  -- `tensorLeft F`; `Adjunction.ofNatIsoLeft` transports `sheafHomAdjunction
  -- F`; `Adjunction.rightAdjointUniq` (Adjunction/Unique.lean:102) against the
  -- internal-hom adjunction `(MonoidalClosed.closed F).adj`.
  exact
    let adj1 : MonoidalCategory.tensorLeft F ⊣ sheafHomFunctor (A := Type (max u v)) F :=
      (sheafHomAdjunction F).ofNatIsoLeft (prodWithIsoTensorLeft F)
    let adj2 : MonoidalCategory.tensorLeft F ⊣
        MonoidalClosed.internalHom.obj (Opposite.op F) :=
      (MonoidalClosed.closed F).adj
    (Adjunction.rightAdjointUniq adj1 adj2).app G

end CategoryTheory
