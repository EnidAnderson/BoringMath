/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringMath.CategoryTheory.Sites.SheafHomBifunctor.Bifunctor
import BoringMath.CategoryTheory.Sites.SheafHomBifunctor.Curry
import Mathlib.CategoryTheory.Sites.SheafHom
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Sites.CartesianClosed
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes

/-!
# The sheaf-Hom bifunctor, part (c): Cartesian closedness of `Sheaf J (Type _)`

Split out of `BoringMath.CategoryTheory.Sites.SheafHomBifunctor`.
-/

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

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
