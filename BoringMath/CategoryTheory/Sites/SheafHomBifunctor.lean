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
    -- TEMPORARY SORRY: the honest proof has not been instantiated yet.
    -- PEELING PLAN: `NatTrans.ext`, `funext`, `ConcreteCategory.ext`,
    -- `DFunLike.ext`, then `funext α`; `Functor.whiskerLeft_comp`
    -- (Whiskering.lean:193) splits the right factor; the remaining factor is
    -- `whiskerLeft ((Over.map f.unop).op ⋙ (Over.forget X.unop).op) g
    --   = whiskerLeft (Over.forget Y.unop).op g`,
    -- because `Over.map f.unop ⋙ Over.forget X.unop = Over.forget Y.unop`
    -- (both send `(V, v : V ⟶ X.unop)` to `V`).
    sorry

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
    -- TEMPORARY SORRY: the honest proof has not been instantiated yet.
    -- PEELING PLAN: `funext α`; `Functor.whiskerLeft_comp`; the remaining
    -- factor is `whiskerLeft ((Over.map f'.unop).op ⋙ (Over.forget X.unop).op) f
    --   = whiskerLeft (Over.forget Y.unop).op f` (as in `presheafHomPostcomp`).
    sorry

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
        -- TEMPORARY SORRY: the honest proof has not been instantiated yet.
        -- PEELING PLAN: `NatTrans.ext`, `funext`; the interchange law: both
        -- sides reduce to `whiskerLeft _ f.unop ≫ α ≫ whiskerLeft _ h` by
        -- `Functor.whiskerLeft_comp` and `Category.assoc` (cf.
        -- `Functor.whiskerLeft_comp_whiskerRight`, Whiskering.lean:203).
        sorry }
  map_id F := NatTrans.ext (funext fun G => presheafHomPrecomp_id _ _)
  map_comp f g :=
    NatTrans.ext (funext fun G => presheafHomPrecomp_comp _ _ _ _ f.unop g.unop)

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
    -- TEMPORARY SORRY: the honest proof has not been instantiated yet.
    -- PEELING PLAN: `funext φ`; `Functor.map_comp` splits
    -- `(J.overMapPullback A f.unop).map (φ ≫ (J.overPullback A X.unop).map g)`;
    -- the remaining factor `(J.overMapPullback A f.unop).map
    -- ((J.overPullback A X.unop).map g) = (J.overPullback A Y.unop).map g` is
    -- `sheafPushforwardContinuousComp` (Sites/Continuous.lean:383, an
    -- `Iso.refl`) for `Over.map f.unop ⋙ Over.forget X.unop =
    -- Over.forget Y.unop`.
    sorry

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
    -- TEMPORARY SORRY: the honest proof has not been instantiated yet.
    -- PEELING PLAN: as in `sheafHomPostcomp`: `funext φ`, `Functor.map_comp`,
    -- `sheafPushforwardContinuousComp`.
    sorry

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
    -- TEMPORARY SORRY: the honest proof has not been instantiated yet.
    -- PEELING PLAN: apply `Sheaf.homEquiv.injective`; reduce to
    -- `sheafHomPostcomp F G G (𝟙 G) = 𝟙 (sheafHom' F G)` (the sheaf-level
    -- analogue of `presheafHomPostcomp_id`: `Functor.map_id`,
    -- `Category.comp_id`, `NatTrans.ext`, `funext`), using that
    -- `Sheaf.homEquiv` sends `𝟙` to `𝟙`.
    sorry
  map_comp f g := by
    -- TEMPORARY SORRY: the honest proof has not been instantiated yet.
    -- PEELING PLAN: as `map_id`, with `Functor.map_comp` and `Category.assoc`.
    sorry

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
        -- TEMPORARY SORRY: the honest proof has not been instantiated yet.
        -- PEELING PLAN: `Sheaf.homEquiv.injective`, `NatTrans.ext`,
        -- `funext`; interchange of pre- and post-composition via
        -- `Functor.map_comp` and `Category.assoc`.
        sorry }
  map_id F := by
    -- TEMPORARY SORRY: the honest proof has not been instantiated yet.
    -- PEELING PLAN: `Sheaf.homEquiv.injective` + `sheafHomPrecomp` of `𝟙`
    -- is `𝟙` (`Functor.map_id`, `Category.id_comp`).
    sorry
  map_comp f g := by
    -- TEMPORARY SORRY: the honest proof has not been instantiated yet.
    -- PEELING PLAN: `Sheaf.homEquiv.injective` + `Functor.map_comp` +
    -- `Category.assoc` (contravariant order, as in `presheafHomPrecomp_comp`).
    sorry

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

-- Reference: [Riou], `Mathlib.CategoryTheory.Sites.SheafHom` TODO (second
-- bullet, verbatim in issue #41); [SGA4], Exposé I, §5; [Stacks], Chapter 7,
-- §7.7 (the exponential of sheaves of sets).
-- REVIEW(citation): pin the exact sections in review.
/-- **Currying** for sheaves of types: a morphism `φ : X ⨯ F ⟶ Y` transposes
to `X ⟶ sheafHom F Y` (peel (b), forward direction of
`sheafHomProdHomEquiv`). -/
def sheafHomCurry (F X Y : Sheaf J (Type (max u v))) (φ : X ⨯ F ⟶ Y) :
    X ⟶ sheafHom F Y := by
  -- TEMPORARY SORRY: the honest proof has not been instantiated yet.
  -- PEELING PLAN: build via `Sheaf.homEquiv.symm` a natural transformation
  -- `X.val ⟶ sheafHom' F Y`; at `U : Cᵒᵖ` it sends `x : X.obj U` to the
  -- morphism `(J.overPullback _ U.unop).obj F ⟶ (J.overPullback _ U.unop).obj Y`
  -- whose component at `op (Over.mk g)` (for `g : V ⟶ U.unop`) is
  -- `s ↦ φ.app (op V) (X.map g.op x, s)` (products of sheaves of types are
  -- pointwise, Sites/Limits.lean:153); naturality is the naturality of `φ`.
  -- Next lemmas: `sheafHomCurry_app`, `sheafHomCurry_naturality`.
  sorry

-- Reference: [Riou], `Mathlib.CategoryTheory.Sites.SheafHom` TODO (second
-- bullet); [SGA4], Exposé I, §5; [Stacks], Chapter 7, §7.7.
-- REVIEW(citation): pin the exact sections in review.
/-- **Uncurrying**: a morphism `ψ : X ⟶ sheafHom F Y` transposes to
`X ⨯ F ⟶ Y` (peel (b), backward direction of `sheafHomProdHomEquiv`). -/
def sheafHomUncurry (F X Y : Sheaf J (Type (max u v))) (ψ : X ⟶ sheafHom F Y) :
    X ⨯ F ⟶ Y := by
  -- TEMPORARY SORRY: the honest proof has not been instantiated yet.
  -- PEELING PLAN: at `U : Cᵒᵖ`, send `(x, s)` to
  -- `((ψ.val.app U x).app (op (Over.mk (𝟙 U.unop)))) s` (evaluate the
  -- internal-hom section at the identity); naturality from the naturality of
  -- `ψ` and `presheafHom_map_app_op_mk_id`. Next lemmas:
  -- `sheafHomUncurry_app`, `sheafHomUncurry_naturality`.
  sorry

-- Reference: [Riou], `Mathlib.CategoryTheory.Sites.SheafHom` TODO (second
-- bullet); [SGA4], Exposé I, §5.
-- REVIEW(citation): pin the exact sections in review.
/-- The two transpositions are inverse: uncurrying a curried morphism returns
the original morphism. -/
theorem sheafHomUncurry_curry (F X Y : Sheaf J (Type (max u v))) (φ : X ⨯ F ⟶ Y) :
    sheafHomUncurry F X Y (sheafHomCurry F X Y φ) = φ := by
  -- TEMPORARY SORRY: the honest proof has not been instantiated yet.
  -- PEELING PLAN: `Sheaf.homEquiv.injective`, then componentwise at `U : Cᵒᵖ`
  -- on `(x, s)`; the composite evaluates the curried section at
  -- `Over.mk (𝟙 _)`; close with `presheafHom_map_app_op_mk_id`.
  sorry

-- Reference: [Riou], `Mathlib.CategoryTheory.Sites.SheafHom` TODO (second
-- bullet); [SGA4], Exposé I, §5.
-- REVIEW(citation): pin the exact sections in review.
/-- The two transpositions are inverse: currying an uncurried morphism
returns the original morphism. -/
theorem sheafHomCurry_uncurry (F X Y : Sheaf J (Type (max u v)))
    (ψ : X ⟶ sheafHom F Y) :
    sheafHomCurry F X Y (sheafHomUncurry F X Y ψ) = ψ := by
  -- TEMPORARY SORRY: the honest proof has not been instantiated yet.
  -- PEELING PLAN: componentwise at `U`, then at `op (Over.mk g)`; a morphism
  -- of restricted sheaves is determined by its values on `Over.mk (𝟙 _)` via
  -- `presheafHom_map_app`; close with `funext` twice and `Sheaf.homEquiv`.
  sorry

-- Reference: [Riou], `Mathlib.CategoryTheory.Sites.SheafHom` TODO (second
-- bullet: "for all `X` and `Y`, there is a natural bijection
-- `(X ⨯ F ⟶ Y) ≃ (X ⟶ sheafHom F Y)`"); [SGA4], Exposé I, §5.
-- REVIEW(citation): pin the exact sections in review.
/-- The **natural bijection** `(X ⨯ F ⟶ Y) ≃ (X ⟶ sheafHom F Y)` for sheaves
of types (peel (b), core). -/
def sheafHomProdHomEquiv (F X Y : Sheaf J (Type (max u v))) :
    (X ⨯ F ⟶ Y) ≃ (X ⟶ sheafHom F Y) where
  toFun := sheafHomCurry F X Y
  invFun := sheafHomUncurry F X Y
  left_inv := sheafHomUncurry_curry F X Y
  right_inv := sheafHomCurry_uncurry F X Y

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
        -- TEMPORARY SORRY: the honest proof has not been instantiated yet.
        -- PEELING PLAN: unfold `sheafHomProdHomEquiv`; naturality in `X` is
        -- precomposition with `Limits.prod.map f (𝟙 F)` and follows from the
        -- component formula of `sheafHomUncurry` (`Limits.prod.map_fst`,
        -- `Limits.prod.map_snd`, `Limits.prod.lift_map`). Next lemma:
        -- `sheafHomProdHomEquiv_naturality_left`.
        sorry
      homEquiv_naturality_right := by
        -- TEMPORARY SORRY: the honest proof has not been instantiated yet.
        -- PEELING PLAN: naturality in `Y` is postcomposition with `g` and
        -- follows from `sheafHomPostcomp`. Next lemma:
        -- `sheafHomProdHomEquiv_naturality_right`.
        sorry }

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
  -- TEMPORARY SORRY: the honest proof has not been instantiated yet.
  -- PEELING PLAN: `Adjunction.rightAdjointUniq` (Adjunction/Unique.lean:102)
  -- applied to `sheafHomAdjunction F` and the internal-hom adjunction
  -- `MonoidalClosed.internalHomAdjunction₂` (Closed/Basic.lean:301), after
  -- transporting `prodWith F` to `MonoidalCategory.tensorLeft F` along
  -- `Limits.prod.braiding` (BinaryProducts.lean:425) and `tensorLeftIsoProd`
  -- (Cartesian/Basic.lean:800). Next lemmas: `prodWith_iso_tensorLeft`,
  -- `sheafHomFunctor_iso_internalHom`.
  sorry

end CategoryTheory
