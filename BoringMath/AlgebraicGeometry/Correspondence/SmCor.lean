/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringMath.AlgebraicGeometry.Correspondence.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# The correspondence category `SmCor(S)` (C.2)

The category of finite correspondences over a base scheme `S` (Voevodsky's
`SmCor(S)`, presented in MVW as the category `Cor_S`): objects are the
schemes smooth and separated over `S` (with a Noetherianness witness, so that
the fundamental cycle exists), and morphisms `X ⟶ Y` are the finite
correspondences `FiniteCorrespondence X.proj Y.proj` of C.1. The identity is
the graph of the identity morphism, and composition is the
**Suslin–Voevodsky formula**: for `c ∈ Cor_S(X, Y)` and `d ∈ Cor_S(Y, Z)`,
`d ∘ c = (pr₁₃)_* (pr₁₂^* c · pr₂₃^* d)`, the pushforward along the
first-and-third projection of the intersection of the two pulled-back cycles
on the triple fiber product `X ×_S Y ×_S Z`.

Statement layer (Tier 1, per #24): the composition and the category laws are
stated exactly and sorried with peeling plans. The one missing substrate is
the **intersection product of two cycles on the triple fiber product** (the
fiber-product cycle) — the C-line's first genuinely Tier 2–3 peel, recorded
as an obstruction; everything else it consumes is landed (`pushforward_comp`,
`pushforward_add`, `pushforward_single`, `Scheme.Hom.residueDegree_comp`, the
fiber-cycle layer). The graph-level law `graphCorrespondence_comp` is already
landed sorry-free (PR #72) and is the consistency witness for the composition:
`graphFiniteCorrespondence_comp` below.

## References
* C. Mazza, V. Voevodsky, C. Weibel, *Lecture Notes on Motivic Cohomology*,
  Clay Mathematics Monographs 2, Amer. Math. Soc. / Clay Math. Inst., 2006,
  Appendix 1A "The category Cor_S" (p. 7): composition of correspondences.
  REVIEW(citation): pin the exact definition/proposition numbers.
* A. Suslin, V. Voevodsky, *Singular homology of abstract algebraic
  varieties*, J. reine angew. Math. 481 (1996), 205–232: the composition
  formula `(pr₁₃)_* (pr₁₂^* c · pr₂₃^* d)`.
  REVIEW(citation): pin the section in review.
* V. Voevodsky, *A¹-homotopy theory*, Proc. Sympos. Pure Math. 67 (1998) /
  DMV Seminar 48, Birkhäuser, 2000, the correspondences section.
  REVIEW(citation): pin the section in review.
-/

universe u

namespace AlgebraicGeometry

open CategoryTheory Limits

variable (S : Scheme.{u})

-- Reference: MVW (2006), Lecture 1, p. 3 and Appendix 1A p. 7 (the objects of
-- `Cor_S` are the smooth separated schemes over `S`).
-- REVIEW(citation): pin the exact definition number within Lecture 1.
/-- An object of `SmCor(S)` / of the smooth site `Sm/S`: a scheme smooth and
separated over `S`, with a Noetherianness witness (automatic when `S` is
Noetherian, since smooth morphisms are of finite presentation). -/
structure SmoothSchemeOver (S : Scheme.{u}) where
  /-- the underlying scheme -/
  carrier : Scheme.{u}
  /-- the structure morphism to the base -/
  proj : carrier ⟶ S
  /-- smoothness of the structure morphism -/
  smooth : Smooth proj
  /-- separatedness of the structure morphism -/
  separated : IsSeparated proj
  /-- the Noetherian witness for the fundamental cycle -/
  noetherian : IsNoetherian carrier

-- Reference: MVW (2006), Appendix 1A p. 7 (the category `Cor_S` has the same
-- objects as `Sm/S`).
-- REVIEW(citation): pin the exact definition number.
/-- The object type of the correspondence category `SmCor(S)`. -/
structure SmCorObj (S : Scheme.{u}) where
  /-- the underlying smooth separated `S`-scheme -/
  over : SmoothSchemeOver S

-- Reference: MVW (2006), Appendix 1A p. 7 (the category `Cor_S`).
-- REVIEW(citation): pin the exact definition number.
/-- **The correspondence category** `SmCor(S)`: objects smooth separated
`S`-schemes, morphisms finite correspondences. -/
abbrev SmCor (S : Scheme.{u}) := SmCorObj S

namespace SmCorObj

variable {S : Scheme.{u}}

-- Reference: MVW (2006), Appendix 1A p. 7 (the object projection); primitive
-- definitional lemma.
/-- The underlying smooth `S`-scheme of a `SmCor` object. -/
def toSmoothSchemeOver (X : SmCor S) : SmoothSchemeOver S := X.over

-- Reference: MVW (2006), Appendix 1A p. 7 (the object projection); primitive
-- definitional lemma.
/-- The underlying scheme. -/
def carrier (X : SmCor S) : Scheme.{u} := X.over.carrier

-- Reference: MVW (2006), Appendix 1A p. 7 (the object projection); primitive
-- definitional lemma.
/-- The structure morphism to the base. -/
def proj (X : SmCor S) : X.carrier ⟶ S := X.over.proj

end SmCorObj

open SmCorObj

variable {S : Scheme.{u}}

-- Reference: MVW (2006), Appendix 1A p. 7 (the diagonal of a separated
-- scheme is a closed immersion, hence quasicompact; the graph of a morphism
-- into a separated target is a pullback of the diagonal).
-- REVIEW(citation): pin the exact proposition in review.
/-- The graph of a morphism over `S` into a **separated** target is
quasicompact: it is the pullback of the diagonal of the target along
`(f, 𝟙)`, and closed immersions are stable under pullback and quasicompact. -/
theorem quasiCompact_graph_of_isSeparated {X Y : Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ S)
    (f : X ⟶ Y) (hf : f ≫ pY = pX) (hsep : IsSeparated pY) :
    QuasiCompact (graph pX pY f hf) := by
  haveI : IsSeparated pY := hsep
  -- the canonical iso `pullback pX pY ≅ pullback (f ≫ pY) pY` (proof irrelevance
  -- of `hf`); its legs are the projections (`pullback.congrHom_hom`, the map
  -- legs by `pullback.lift_fst`/`pullback.lift_snd` with identity isos).
  let e : pullback pX pY ≅ pullback (f ≫ pY) pY :=
    pullback.congrHom hf.symm (Category.id_comp pY)
  have hmapfst : e.hom ≫ pullback.fst (f ≫ pY) pY = pullback.fst pX pY :=
    (pullback.lift_fst (pullback.fst pX pY ≫ 𝟙 X) (pullback.snd pX pY ≫ 𝟙 Y) _).trans
      (Category.comp_id _)
  have hmapnsnd : e.hom ≫ pullback.snd (f ≫ pY) pY = pullback.snd pX pY :=
    (pullback.lift_snd (pullback.fst pX pY ≫ 𝟙 X) (pullback.snd pX pY ≫ 𝟙 Y) _).trans
      (Category.comp_id _)
  -- the graph transported along `e` is the Mathlib graph lift, a closed
  -- immersion when the target is separated (instance at the pin,
  -- `Mathlib/AlgebraicGeometry/Morphisms/Separated.lean`)
  have hCI' : IsClosedImmersion (pullback.lift (𝟙 X) f (Category.id_comp (f ≫ pY))) :=
    inferInstance
  have hleg1 : graph pX pY f hf ≫ e.hom ≫ pullback.fst (f ≫ pY) pY
      = pullback.lift (𝟙 X) f (Category.id_comp (f ≫ pY)) ≫ pullback.fst (f ≫ pY) pY := by
    calc graph pX pY f hf ≫ e.hom ≫ pullback.fst (f ≫ pY) pY
        = graph pX pY f hf ≫ pullback.fst pX pY :=
          (Category.assoc _ _ _).trans (congrArg (graph pX pY f hf ≫ ·) hmapfst)
      _ = 𝟙 X := graph_fst pX pY f hf
      _ = pullback.lift (𝟙 X) f (Category.id_comp (f ≫ pY)) ≫ pullback.fst (f ≫ pY) pY :=
          (pullback.lift_fst (𝟙 X) f (Category.id_comp (f ≫ pY))).symm
  have hleg2 : graph pX pY f hf ≫ e.hom ≫ pullback.snd (f ≫ pY) pY
      = pullback.lift (𝟙 X) f (Category.id_comp (f ≫ pY)) ≫ pullback.snd (f ≫ pY) pY := by
    calc graph pX pY f hf ≫ e.hom ≫ pullback.snd (f ≫ pY) pY
        = graph pX pY f hf ≫ pullback.snd pX pY :=
          (Category.assoc _ _ _).trans (congrArg (graph pX pY f hf ≫ ·) hmapnsnd)
      _ = f := graph_snd pX pY f hf
      _ = pullback.lift (𝟙 X) f (Category.id_comp (f ≫ pY)) ≫ pullback.snd (f ≫ pY) pY :=
          (pullback.lift_snd (𝟙 X) f (Category.id_comp (f ≫ pY))).symm
  have hgraph : graph pX pY f hf ≫ e.hom
      = pullback.lift (𝟙 X) f (Category.id_comp (f ≫ pY)) :=
    pullback.hom_ext hleg1 hleg2
  haveI : IsClosedImmersion (graph pX pY f hf) :=
    (MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion (graph pX pY f hf) e.hom).mp
      (Eq.subst (motive := fun m => IsClosedImmersion m) hgraph.symm hCI')
  -- closed immersions are finite, finite morphisms are proper, and proper
  -- morphisms are universally closed, hence quasicompact (instances at the pin)
  exact inferInstance

variable {X Y Z : Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ S) (pZ : Z ⟶ S)

-- Reference: Suslin–Voevodsky (1996), the composition formula; MVW (2006),
-- Appendix 1A p. 7 (composition in `Cor_S`: `d ∘ c = (pr₁₃)_* (pr₁₂^* c ·
-- pr₂₃^* d)` on the triple fiber product).
-- REVIEW(citation): pin the exact formula location in review.
/-- **The Suslin–Voevodsky composition of finite correspondences**: for
`c : X ⇸ Y` and `d : Y ⇸ Z`, the composite `d ∘ c : X ⇸ Z` is the
pushforward along the first-and-third projection `pr₁₃` of the intersection
`pr₁₂^* c · pr₂₃^* d` of the two pulled-back cycles on the triple fiber
product `X ×_S Y ×_S Z`. -/
noncomputable def correspondenceComp (c : FiniteCorrespondence pX pY)
    (d : FiniteCorrespondence pY pZ) : FiniteCorrespondence pX pZ := by
  -- TEMPORARY SORRY: statement layer (Tier 1, #24). PEELING PLAN: (1) the
  -- flat pullback of a finite cycle along `pr₁₂` and `pr₂₃` — the
  -- projections of the triple fiber product are base changes of the smooth
  -- structure morphisms, hence flat; the general flat pullback of a cycle
  -- generalizes the landed `AlgebraicCycle.fiberCycle` (currently the
  -- fundamental cycle of the fiber); (2) the **intersection product** `·` of
  -- the two pulled-back cycles on `X ×_S Y ×_S Z` — the fiber-product cycle,
  -- THE missing substrate (Fulton, *Intersection Theory*, ch. 1–6 vicinity;
  -- recorded obstruction of the C-line); (3) the pushforward along `pr₁₃` via
  -- the landed `AlgebraicCycle.pushforward` (with `pushforward_comp`,
  -- `pushforward_add`, `pushforward_single`); (4) finiteness over the source
  -- of the composite from the finite fibers of the two factors
  -- (`FiniteCorrespondence.finiteOverSource`).
  sorry

-- Reference: MVW (2006), Appendix 1A p. 7 (the identity of `Cor_S` is the
-- graph of the identity).
-- REVIEW(citation): pin the exact proposition in review.
/-- **The identity correspondence** is the graph of the identity morphism. -/
noncomputable def identityCorrespondence (X : SmoothSchemeOver S) :
    FiniteCorrespondence X.proj X.proj := by
  haveI := X.noetherian
  exact graphFiniteCorrespondence X.proj X.proj (𝟙 X.carrier) (Category.id_comp X.proj)
    (quasiCompact_graph_of_isSeparated X.proj X.proj (𝟙 X.carrier) (Category.id_comp X.proj)
      X.separated)

-- Reference: MVW (2006), Appendix 1A p. 7 (the left identity law in `Cor_S`).
-- REVIEW(citation): pin the exact proposition in review.
/-- The left identity law: composing with the graph of the identity on the
left is the identity. TEMPORARY SORRY: peels through `correspondenceComp`
(plan there) using the landed `pushforward_id` and the fiber-cycle pullback
laws. -/
theorem correspondenceComp_identityCorrespondence_left {X Y : SmoothSchemeOver S}
    (c : FiniteCorrespondence X.proj Y.proj) :
    correspondenceComp X.proj X.proj Y.proj (identityCorrespondence X) c = c := by
  -- TEMPORARY SORRY: peeling plan on `correspondenceComp`.
  sorry

-- Reference: MVW (2006), Appendix 1A p. 7 (the right identity law in `Cor_S`).
-- REVIEW(citation): pin the exact proposition in review.
/-- The right identity law: composing with the graph of the identity on the
right is the identity. TEMPORARY SORRY: peels through `correspondenceComp`
(plan there). -/
theorem correspondenceComp_identityCorrespondence_right {X Y : SmoothSchemeOver S}
    (c : FiniteCorrespondence X.proj Y.proj) :
    correspondenceComp X.proj Y.proj Y.proj c (identityCorrespondence Y) = c := by
  -- TEMPORARY SORRY: peeling plan on `correspondenceComp`.
  sorry

-- Reference: MVW (2006), Appendix 1A p. 7 (associativity of composition in
-- `Cor_S`).
-- REVIEW(citation): pin the exact proposition in review.
/-- Composition of finite correspondences is associative. TEMPORARY SORRY:
peels through `correspondenceComp` (plan there) using the landed
`pushforward_comp` and the associativity of the intersection product. -/
theorem correspondenceComp_assoc {X Y Z W : SmoothSchemeOver S}
    (c : FiniteCorrespondence X.proj Y.proj) (d : FiniteCorrespondence Y.proj Z.proj)
    (e : FiniteCorrespondence Z.proj W.proj) :
    correspondenceComp X.proj Z.proj W.proj (correspondenceComp X.proj Y.proj Z.proj c d) e =
      correspondenceComp X.proj Y.proj W.proj c (correspondenceComp Y.proj Z.proj W.proj d e) := by
  -- TEMPORARY SORRY: peeling plan on `correspondenceComp`.
  sorry

-- Reference: MVW (2006), Appendix 1A p. 7 (addition of correspondences is
-- bilinear for the composition).
-- REVIEW(citation): pin the exact proposition in review.
/-- Composition is additive in the left argument. TEMPORARY SORRY: peels
through `correspondenceComp` using the landed `pushforward_add` and the
additivity of the pullback and intersection product. -/
theorem correspondenceComp_add_left {X Y Z : SmoothSchemeOver S}
    (c₁ c₂ : FiniteCorrespondence X.proj Y.proj) (d : FiniteCorrespondence Y.proj Z.proj) :
    correspondenceComp X.proj Y.proj Z.proj (c₁ + c₂) d =
      correspondenceComp X.proj Y.proj Z.proj c₁ d +
        correspondenceComp X.proj Y.proj Z.proj c₂ d := by
  -- TEMPORARY SORRY: peeling plan on `correspondenceComp`.
  sorry

-- Reference: MVW (2006), Appendix 1A p. 7 (addition of correspondences is
-- bilinear for the composition).
-- REVIEW(citation): pin the exact proposition in review.
/-- Composition is additive in the right argument. TEMPORARY SORRY: peels
through `correspondenceComp` using the landed `pushforward_add` and the
additivity of the pullback and intersection product. -/
theorem correspondenceComp_add_right {X Y Z : SmoothSchemeOver S}
    (c : FiniteCorrespondence X.proj Y.proj) (d₁ d₂ : FiniteCorrespondence Y.proj Z.proj) :
    correspondenceComp X.proj Y.proj Z.proj c (d₁ + d₂) =
      correspondenceComp X.proj Y.proj Z.proj c d₁ +
        correspondenceComp X.proj Y.proj Z.proj c d₂ := by
  -- TEMPORARY SORRY: peeling plan on `correspondenceComp`.
  sorry

-- Reference: MVW (2006), Appendix 1A p. 7 (the graph construction is
-- functorial); the cycle-level law is the landed `graphCorrespondence_comp`
-- (PR #72, sorry-free).
-- REVIEW(citation): pin the exact proposition in review.
/-- **Graphs compose to graphs**: the composite of the graph
correspondences of two composable morphisms over `S` is the graph
correspondence of the composite — the acceptance criterion of #24, at the
level of finite correspondences. TEMPORARY SORRY: reduces to the landed
`graphCorrespondence_comp` via `graphFiniteCorrespondence_toCycle` and
`FiniteCorrespondence.ext_iff` once `correspondenceComp` is the
Suslin–Voevodsky formula. -/
theorem graphFiniteCorrespondence_comp {X Y Z : SmoothSchemeOver S}
    [IsNoetherian X.carrier] [IsNoetherian Y.carrier] [IsNoetherian Z.carrier]
    (f : X.carrier ⟶ Y.carrier) (hf : f ≫ Y.proj = X.proj)
    (g : Y.carrier ⟶ Z.carrier) (hg : g ≫ Z.proj = Y.proj) :
    correspondenceComp X.proj Y.proj Z.proj
        (graphFiniteCorrespondence X.proj Y.proj f hf
          (quasiCompact_graph_of_isSeparated X.proj Y.proj f hf Y.separated))
        (graphFiniteCorrespondence Y.proj Z.proj g hg
          (quasiCompact_graph_of_isSeparated Y.proj Z.proj g hg Z.separated)) =
      graphFiniteCorrespondence X.proj Z.proj (f ≫ g)
        (Eq.trans (Eq.trans (Category.assoc f g Z.proj).symm (congrArg (f ≫ ·) hg)) hf)
        (quasiCompact_graph_of_isSeparated X.proj Z.proj (f ≫ g)
          (Eq.trans (Eq.trans (Category.assoc f g Z.proj).symm (congrArg (f ≫ ·) hg)) hf)
          Z.separated) := by
  -- TEMPORARY SORRY: reduce to the landed `graphCorrespondence_comp`.
  sorry

-- Reference: MVW (2006), Appendix 1A p. 7 (the category `Cor_S`: identity,
-- composition, laws).
-- REVIEW(citation): pin the exact definition in review.
/-- The **category instance of `SmCor(S)`**: morphisms are finite
correspondences, the identity is the graph of the identity, composition is the
Suslin–Voevodsky composition; the laws are the sorried named lemmas above.
`noncomputable`: the identity correspondence is choice-backed (the fundamental
cycle chooses the generic points). -/
noncomputable instance smCorCategory : Category.{u} (SmCor S) where
  Hom X Y := FiniteCorrespondence X.proj Y.proj
  id X := identityCorrespondence X.over
  comp c d := correspondenceComp _ _ _ c d
  id_comp c := correspondenceComp_identityCorrespondence_left c
  comp_id c := correspondenceComp_identityCorrespondence_right c
  assoc c d e := correspondenceComp_assoc c d e

-- Reference: MVW (2006), Appendix 1A p. 7 (`Cor_S` is an additive category:
-- the hom groups are abelian and composition is bilinear).
-- REVIEW(citation): pin the exact proposition in review.
/-- `SmCor(S)` is **preadditive**: the hom groups are the abelian groups of
finite correspondences (the C.1 `AddCommGroup` instance) and composition is
bilinear (the sorried named laws). -/
noncomputable instance smCorPreadditive : Preadditive (SmCor S) where
  homGroup P Q := inferInstanceAs (AddCommGroup (FiniteCorrespondence P.proj Q.proj))
  add_comp _P _Q _R f f' g := correspondenceComp_add_left f f' g
  comp_add _P _Q _R f g g' := correspondenceComp_add_right f g g'

end AlgebraicGeometry
