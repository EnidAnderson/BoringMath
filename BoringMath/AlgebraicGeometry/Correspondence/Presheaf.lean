/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringMath.AlgebraicGeometry.Correspondence.SmCor
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.CategoryTheory.Whiskering

/-!
# Presheaves with transfers (C.3)

A **presheaf with transfers** over `S` (Voevodsky's `PST(S)` / MVW's
`PSh(Cor_S)`) is an additive presheaf of abelian groups on the correspondence
category `SmCor(S)`: for each finite correspondence `c : X ⇸ Y` a transfer
group homomorphism `F(Y) → F(X)`, functorial in `c` (transfers compose with
correspondence composition) and additive in `c`. The data is taken explicitly
(the underlying functor), per STYLE §2.3 — nothing is instance-chosen.

The fundamental example is the **representable** presheaf with transfers
`ℤ_tr(X)`: `Y ↦ Cor_S(Y, X)`, the group of finite correspondences from `Y` to
`X` — zero-cycles on `X ×_S Y` finite over `Y` — given by the preadditive
Yoneda embedding of `SmCor(S)`.

The **graph functor** `Sm/S ⥤ SmCor(S)` sends a morphism over `S` to its
graph correspondence (functorial by the landed `graphCorrespondence_comp`,
PR #72); precomposing along it is the forgetful functor from presheaves with
transfers to presheaves on the smooth site, and the transfer along a graph
correspondence is exactly the underlying presheaf's action on the morphism.

Statement layer (Tier 1, per #25): the Voevodsky DM axioms (homotopy
invariance, Mayer–Vietoris) are NOT here — they belong to the C.4 station.

## References
* C. Mazza, V. Voevodsky, C. Weibel, *Lecture Notes on Motivic Cohomology*,
  Clay Mathematics Monographs 2, Amer. Math. Soc. / Clay Math. Inst., 2006,
  Lecture 2 "Presheaves with transfers" (p. 13).
  REVIEW(citation): pin the exact definition numbers within Lecture 2.
* V. Voevodsky, A. Suslin, E. M. Friedlander, *Cycles, Transfers, and
  Motivic Homology Theories*, Annals of Mathematics Studies 143, Princeton
  University Press, 2000, the definitions chapter (presheaves with
  transfers, `Z_tr(X)`).
  REVIEW(citation): pin the exact chapter/section in review.
-/

universe u

namespace AlgebraicGeometry

open CategoryTheory

variable (S : Scheme.{u})

-- Reference: MVW (2006), Lecture 1, p. 3 (the smooth site `Sm/S`: objects
-- smooth separated `S`-schemes, morphisms the `S`-morphisms).
-- REVIEW(citation): pin the exact definition number within Lecture 1.
/-- The **category of smooth `S`-schemes** `Sm/S`: objects are the
`SmoothSchemeOver S`, morphisms are the morphisms over `S`. -/
noncomputable instance smoothOverCategory : Category.{u} (SmoothSchemeOver S) where
  Hom X Y := {f : X.carrier ⟶ Y.carrier // f ≫ Y.proj = X.proj}
  id X := ⟨𝟙 X.carrier, Category.id_comp X.proj⟩
  comp f g := ⟨f.1 ≫ g.1,
    Eq.trans (Category.assoc f.1 g.1 _) (Eq.trans (congrArg (f.1 ≫ ·) g.2) f.2)⟩
  id_comp f := Subtype.ext (Category.id_comp f.1)
  comp_id f := Subtype.ext (Category.comp_id f.1)
  assoc f g h := Subtype.ext (Category.assoc f.1 g.1 h.1)

variable {S : Scheme.{u}}

-- Reference: MVW (2006), Lecture 1, p. 3, Appendix 1A p. 7 (every morphism
-- over `S` gives the graph correspondence; functorial by the landed
-- `graphCorrespondence_comp`, PR #72).
-- REVIEW(citation): pin the exact proposition in review.
/-- **The graph functor** `Sm/S ⥤ SmCor(S)`: a morphism over `S` is sent to
its graph correspondence. `noncomputable`: the graph correspondence is
choice-backed (the fundamental cycle chooses the generic points). -/
noncomputable def graphFunctor : SmoothSchemeOver S ⥤ SmCor S where
  obj X := ⟨X⟩
  map {X Y} f := by
    haveI := X.noetherian
    exact graphFiniteCorrespondence X.proj Y.proj f.1 f.2
      (quasiCompact_graph_of_isSeparated X.proj Y.proj f.1 f.2 Y.separated)
  map_id X := by
    have := X.noetherian
    exact (FiniteCorrespondence.ext_iff X.proj X.proj).mpr rfl
  map_comp {X Y Z} f g := by
    have := X.noetherian
    have := Y.noetherian
    have := Z.noetherian
    exact (graphFiniteCorrespondence_comp f.1 f.2 g.1 g.2).symm

-- Reference: Voevodsky–Suslin–Friedlander (2000), the definitions chapter; MVW
-- (2006), Lecture 2, p. 13 (a presheaf with transfers is an additive
-- presheaf on `Cor_S`; the transfer maps are the functor's action on
-- correspondences).
-- REVIEW(citation): pin the exact definition numbers in review.
/-- A **presheaf with transfers** over `S`: an additive presheaf of abelian
groups on `SmCor(S)`. The transfer along a finite correspondence `c : X ⇸ Y`
is `toFunctor.map (op c) : F(Y) ⟶ F(X)`; the laws — functoriality in `c`
(automatic from the functor laws) and additivity in `c` (`additive`) — are the
Voevodsky transfer laws. The data is explicit per STYLE §2.3. -/
structure PresheafWithTransfer (S : Scheme.{u}) where
  /-- the underlying additive presheaf on the correspondence category -/
  toFunctor : (SmCor S)ᵒᵖ ⥤ AddCommGrpCat.{u}
  /-- additivity: transfers are additive in the correspondence -/
  additive : toFunctor.Additive

namespace PresheafWithTransfer

variable {S : Scheme.{u}}

-- Reference: MVW (2006), Lecture 2, p. 13 (transfers are additive in the
-- correspondence).
-- REVIEW(citation): pin the exact proposition within Lecture 2.
/-- **Transfers are additive in the correspondence**: the transfer along
`c + d` is the sum of the transfers along `c` and `d`. -/
theorem transfer_add (F : PresheafWithTransfer S) {X Y : SmCor S} {c d : X ⟶ Y} :
    F.toFunctor.map (Opposite.op (c + d)) =
      F.toFunctor.map (Opposite.op c) + F.toFunctor.map (Opposite.op d) := by
  have := F.additive
  exact Functor.map_add F.toFunctor

-- Reference: MVW (2006), Lecture 2, p. 13 (transfers compose with the
-- composition of correspondences: the action is functorial on `Cor_S`).
-- REVIEW(citation): pin the exact proposition within Lecture 2.
/-- **Transfers compose with correspondence composition**: the transfer
along `d ∘ c` is the composite of the transfers. -/
theorem transfer_comp (F : PresheafWithTransfer S) {X Y Z : SmCor S} (c : X ⟶ Y) (d : Y ⟶ Z) :
    F.toFunctor.map (Opposite.op (c ≫ d)) =
      F.toFunctor.map (Opposite.op d) ≫ F.toFunctor.map (Opposite.op c) :=
  F.toFunctor.map_comp (Opposite.op d) (Opposite.op c)

-- Reference: MVW (2006), Lecture 2, p. 13 (the underlying presheaf on `Sm/S`
-- is the restriction along the graph functor; a transfer along a graph is the
-- presheaf's action on the morphism).
-- REVIEW(citation): pin the exact proposition within Lecture 2.
/-- The **underlying presheaf** of a presheaf with transfers: restriction
along the graph functor `Sm/S ⥤ SmCor(S)`. -/
noncomputable def toPresheaf (F : PresheafWithTransfer S) :
    (SmoothSchemeOver S)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (graphFunctor (S := S)).op ⋙ F.toFunctor

-- Reference: MVW (2006), Lecture 1, Appendix 1A p. 7 (the graph functor's
-- value on a morphism); primitive definitional lemma.
/-- The graph functor sends an `S`-morphism to its graph correspondence. -/
theorem graphFunctor_map {X Y : SmoothSchemeOver S} (f : X ⟶ Y) [IsNoetherian X.carrier] :
    (graphFunctor (S := S)).map f =
      (graphFiniteCorrespondence X.proj Y.proj f.1 f.2
        (quasiCompact_graph_of_isSeparated X.proj Y.proj f.1 f.2 Y.separated) :
        (⟨X⟩ : SmCor S) ⟶ ⟨Y⟩) :=
  rfl

-- Reference: MVW (2006), Lecture 2, p. 13 (transfers restrict to the presheaf
-- action on morphisms when the correspondence is a graph); primitive
-- definitional lemmas (precomposition along the graph functor).
/-- The opposite of the graph functor maps `op f` to the opposite of the
graph correspondence. -/
theorem graphFunctor_op_map {X Y : SmoothSchemeOver S} (f : X ⟶ Y) :
    (graphFunctor (S := S)).op.map (Opposite.op f) =
      Opposite.op ((graphFunctor (S := S)).map f) :=
  rfl

-- Reference: MVW (2006), Lecture 2, p. 13 (transfers restrict to the presheaf
-- action on morphisms when the correspondence is a graph); primitive
-- definitional lemma (precomposition along the graph functor).
-- REVIEW(citation): pin the exact proposition within Lecture 2.
/-- **The graph restriction law**: the transfer along the graph
correspondence of an `S`-morphism `f` is exactly the underlying presheaf's
action on `f` (through the graph functor). -/
theorem toPresheaf_map_graph (F : PresheafWithTransfer S) {X Y : SmoothSchemeOver S}
    (f : X ⟶ Y) :
    (F.toPresheaf).map (Opposite.op f) =
      F.toFunctor.map ((graphFunctor (S := S)).op.map (Opposite.op f)) :=
  rfl

-- Reference: Voevodsky–Suslin–Friedlander (2000), the definitions chapter; MVW
-- (2006), Lecture 2, p. 13 (the representable `Z_tr(X)`: `Y ↦ Cor_S(Y, X)`).
-- REVIEW(citation): pin the exact definition numbers in review.
/-- **The representable presheaf with transfers** `ℤ_tr(X)`: `Y ↦` the group
of finite correspondences `Cor_S(Y, X)` — zero-cycles on `X ×_S Y` finite
over `Y` — the preadditive Yoneda embedding of `X`. `noncomputable`: the
`SmCor(S)` category instance is choice-backed. -/
noncomputable def zTr (X : SmCor S) : PresheafWithTransfer S where
  toFunctor := preadditiveYoneda.obj X
  additive := inferInstance

-- Reference: MVW (2006), Lecture 2, p. 13 (`Z_tr(X)(Y) = Cor_S(Y, X)`);
-- primitive definitional lemma (the preadditive Yoneda value).
/-- The value of `ℤ_tr(X)` at `Y` is the group of finite correspondences from
`Y` to `X`. -/
theorem zTr_obj (X Y : SmCor S) :
    (zTr X).toFunctor.obj (Opposite.op Y) = AddCommGrpCat.of (Y ⟶ X) :=
  rfl

end PresheafWithTransfer

-- Reference: MVW (2006), Lecture 2, p. 13 (the forgetful functor from
-- presheaves with transfers to presheaves on `Sm/S`).
-- REVIEW(citation): pin the exact proposition within Lecture 2.
/-- **The forgetful functor** from presheaves on `SmCor(S)` to presheaves on
the smooth site `Sm/S`: precomposition along the graph functor.
`noncomputable`: the graph functor is choice-backed. -/
noncomputable def forgetful (S : Scheme.{u}) :
    ((SmCor S)ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ ((SmoothSchemeOver S)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  (Functor.whiskeringLeft _ _ _).obj (graphFunctor (S := S)).op

end AlgebraicGeometry
