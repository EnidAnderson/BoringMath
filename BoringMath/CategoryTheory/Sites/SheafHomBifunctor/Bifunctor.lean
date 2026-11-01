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
# The sheaf-Hom bifunctor, part (a): `presheafHom` and `sheafHom` as bifunctors

Split out of `BoringMath.CategoryTheory.Sites.SheafHomBifunctor`.
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

end CategoryTheory
