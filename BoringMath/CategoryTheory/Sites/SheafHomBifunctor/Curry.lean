/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringMath.CategoryTheory.Sites.SheafHomBifunctor.Bifunctor
import Mathlib.CategoryTheory.Sites.SheafHom
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Sites.CartesianClosed
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes

/-!
# The sheaf-Hom bifunctor, part (b): the product adjunction `(- ⨯ F) ⊣ sheafHom F`

Split out of `BoringMath.CategoryTheory.Sites.SheafHomBifunctor`.
-/

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

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
  have h2 : (e.inv.app U ≫ e.hom.app U) w = w :=
    -- `h : e.inv.app U ≫ e.hom.app U = 𝟙 (Q.obj U)`; substitute inside the
    -- application at `w`; `(𝟙 _) w = w` is definitional (`id_apply`).
    Eq.subst (motive := fun φ : Q.obj U ⟶ Q.obj U => φ w = w) h.symm rfl
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

end CategoryTheory
