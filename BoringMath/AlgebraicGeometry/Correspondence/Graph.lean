/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringMath.AlgebraicGeometry.AlgebraicCycle.FundamentalCycle
import BoringMath.AlgebraicGeometry.AlgebraicCycle.Pushforward

/-!
# The graph correspondence

The graph of a morphism of schemes over a base, as a morphism to the
fiber product via the universal property, and the graph correspondence:
the pushforward of the fundamental cycle of the source along the graph.

## References
* F. Mazza, V. Voevodsky, C. Weibel, *An Introduction to Motivic
  Cohomology* (the chapter on finite correspondences: the graph of a
  morphism as a correspondence).
  REVIEW(citation): pin down the chapter.
* V. Voevodsky, *Lectures on motivic cohomology* (correspondences).
  REVIEW(citation): pin down the reference.
-/

universe u

namespace AlgebraicGeometry

open CategoryTheory Limits

variable {S X Y : Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ S)

-- Reference: F. Mazza, V. Voevodsky, C. Weibel, *An Introduction to
-- Motivic Cohomology* (the graph of a morphism over a base).
-- REVIEW(citation): pin down the chapter.
/-- **The graph of a morphism over a base**: the lift of the identity
and the morphism against the projections of the fiber product — the
universal property of the fiber product applied to the pair `(𝟙, f)`. -/
noncomputable def graph (f : X ⟶ Y) (hf : f ≫ pY = pX) : X ⟶ pullback pX pY :=
  pullback.lift (𝟙 X) f hf.symm

-- Reference: F. Mazza, V. Voevodsky, C. Weibel, *An Introduction to
-- Motivic Cohomology* (the graph is a section of the first projection).
-- REVIEW(citation): pin down the chapter.
/-- The graph composed with the first projection is the identity. -/
theorem graph_fst (f : X ⟶ Y) (hf : f ≫ pY = pX) :
    graph pX pY f hf ≫ pullback.fst pX pY = 𝟙 X :=
  pullback.lift_fst (𝟙 X) f hf.symm

-- Reference: F. Mazza, V. Voevodsky, C. Weibel, *An Introduction to
-- Motivic Cohomology* (the graph composed with the second projection
-- is the morphism).
-- REVIEW(citation): pin down the chapter.
/-- The graph composed with the second projection is the morphism. -/
theorem graph_snd (f : X ⟶ Y) (hf : f ≫ pY = pX) :
    graph pX pY f hf ≫ pullback.snd pX pY = f :=
  pullback.lift_snd (𝟙 X) f hf.symm

-- Reference: F. Mazza, V. Voevodsky, C. Weibel, *An Introduction to
-- Motivic Cohomology* (the graph of a morphism as a correspondence: the
-- pushforward of the fundamental cycle along the graph).
-- REVIEW(citation): pin down the chapter.
-- The generic points are chosen and the fiber sums are enumerated by
-- choice; the correspondence is noncomputable.
open scoped Classical in
/-- **The graph correspondence** of a morphism over a base: the
pushforward of the fundamental cycle of the source along the graph. -/
noncomputable def graphCorrespondence (f : X ⟶ Y) (hf : f ≫ pY = pX)
    [IsNoetherian X] (hqc : QuasiCompact (graph pX pY f hf)) :
    AlgebraicCycle (pullback pX pY) ℤ :=
  AlgebraicCycle.pushforward (graph pX pY f hf) (Scheme.fundamentalCycle X)

-- Reference: F. Mazza, V. Voevodsky, C. Weibel, *An Introduction to
-- Motivic Cohomology* (the support of the graph correspondence lies on
-- the graph of the support).
-- REVIEW(citation): pin down the chapter.
/-- The support of the graph correspondence is contained in the image
of the support of the fundamental cycle along the graph. -/
theorem support_graphCorrespondence (f : X ⟶ Y) (hf : f ≫ pY = pX)
    [IsNoetherian X] (hqc : QuasiCompact (graph pX pY f hf)) :
    (graphCorrespondence pX pY f hf hqc).support ⊆
      (graph pX pY f hf).base '' (Scheme.fundamentalCycle X).support :=
  AlgebraicCycle.support_pushforward_subset_image (graph pX pY f hf) (Scheme.fundamentalCycle X)

-- Reference: F. Mazza, V. Voevodsky, C. Weibel, *An Introduction to
-- Motivic Cohomology* (the graph correspondence of a Noetherian scheme
-- has finite support).
-- REVIEW(citation): pin down the chapter.
/-- The graph correspondence of a Noetherian scheme has finite
support. -/
theorem isFinite_graphCorrespondence (f : X ⟶ Y) (hf : f ≫ pY = pX)
    [IsNoetherian X] (hqc : QuasiCompact (graph pX pY f hf)) :
    AlgebraicCycle.IsFinite (graphCorrespondence pX pY f hf hqc) :=
  AlgebraicCycle.IsFinite.pushforward (graph pX pY f hf)
    (Scheme.isFinite_fundamentalCycle X)

-- Reference: A. Suslin, V. Voevodsky, *Singular homology of abstract
-- algebraic varieties* (the composite of the graphs: the fiber product
-- of the two graph factors).
-- REVIEW(citation): pin down the section.
variable {Z : Scheme.{u}} (pZ : Z ⟶ S)

/-- The pair of the graphs: the lift into the fiber product of the two
graph factors — the source point maps to its graph points on both
factors. -/
noncomputable def graphComposite (f : X ⟶ Y) (hf : f ≫ pY = pX)
    (g : Y ⟶ Z) (hg : g ≫ pZ = pY) :
    X ⟶ pullback (pullback.snd pX pY) (pullback.fst pY pZ) := by
  have w1 : f ≫ pY = (f ≫ g) ≫ pZ :=
    Eq.trans (congrArg (f ≫ ·) hg.symm) (Category.assoc f g pZ)
  exact pullback.lift (graph pX pY f hf) (pullback.lift f (f ≫ g) w1)
    (Eq.trans (graph_snd pX pY f hf)
      (pullback.lift_fst f (f ≫ g) w1).symm)

-- Reference: A. Suslin, V. Voevodsky, *Singular homology of abstract
-- algebraic varieties* (the fiber product of the two graph factors).
-- REVIEW(citation): pin down the section.
/-- The first-and-third components of the fiber product of the two graph
factors agree on the base: the structure maps match through the fiber
product conditions. -/
theorem graphComposite_condition :
    (pullback.fst (pullback.snd pX pY) (pullback.fst pY pZ) ≫
        pullback.fst pX pY) ≫ pX =
      (pullback.snd (pullback.snd pX pY) (pullback.fst pY pZ) ≫
        pullback.snd pY pZ) ≫ pZ :=
  calc (pullback.fst (pullback.snd pX pY) (pullback.fst pY pZ) ≫
          pullback.fst pX pY) ≫ pX
      = pullback.fst (pullback.snd pX pY) (pullback.fst pY pZ) ≫
          (pullback.fst pX pY ≫ pX) :=
        Category.assoc _ _ _
    _ = pullback.fst (pullback.snd pX pY) (pullback.fst pY pZ) ≫
          (pullback.snd pX pY ≫ pY) :=
        congrArg (pullback.fst (pullback.snd pX pY)
          (pullback.fst pY pZ) ≫ ·) pullback.condition
    _ = (pullback.fst (pullback.snd pX pY) (pullback.fst pY pZ) ≫
          pullback.snd pX pY) ≫ pY :=
        (Category.assoc _ _ _).symm
    _ = (pullback.snd (pullback.snd pX pY) (pullback.fst pY pZ) ≫
          pullback.fst pY pZ) ≫ pY :=
        congrArg (· ≫ pY) pullback.condition
    _ = pullback.snd (pullback.snd pX pY) (pullback.fst pY pZ) ≫
          (pullback.fst pY pZ ≫ pY) :=
        Category.assoc _ _ _
    _ = pullback.snd (pullback.snd pX pY) (pullback.fst pY pZ) ≫
          (pullback.snd pY pZ ≫ pZ) :=
        congrArg (pullback.snd (pullback.snd pX pY)
          (pullback.fst pY pZ) ≫ ·) pullback.condition
    _ = (pullback.snd (pullback.snd pX pY) (pullback.fst pY pZ) ≫
          pullback.snd pY pZ) ≫ pZ :=
        (Category.assoc _ _ _).symm

-- Reference: A. Suslin, V. Voevodsky, *Singular homology of abstract
-- algebraic varieties* (the first-and-third projection).
-- REVIEW(citation): pin down the section.
/-- The first-and-third projection of the fiber product of the two graph
factors. -/
noncomputable def graphCompositeMap :
    pullback (pullback.snd pX pY) (pullback.fst pY pZ) ⟶ pullback pX pZ :=
  pullback.lift
    (pullback.fst (pullback.snd pX pY) (pullback.fst pY pZ) ≫
      pullback.fst pX pY)
    (pullback.snd (pullback.snd pX pY) (pullback.fst pY pZ) ≫
      pullback.snd pY pZ)
    (graphComposite_condition pX pY pZ)

-- Reference: A. Suslin, V. Voevodsky, *Singular homology of abstract
-- algebraic varieties* (the composite of the graph correspondences is
-- the graph correspondence of the composite).
-- REVIEW(citation): pin down the section.
/-- **The factorization of the composite of the graphs**: the composite
of the pair of the graphs with the first-and-third projection is the
graph of the composite morphism. -/
theorem graphCompositeMap_comp (f : X ⟶ Y) (hf : f ≫ pY = pX)
    (g : Y ⟶ Z) (hg : g ≫ pZ = pY) :
    graphComposite pX pY pZ f hf g hg ≫
      graphCompositeMap pX pY pZ =
      graph pX pZ (f ≫ g)
        (Eq.trans (Eq.trans (Category.assoc f g pZ).symm
          (congrArg (f ≫ ·) hg)) hf) := by
  have w1 : f ≫ pY = (f ≫ g) ≫ pZ :=
    Eq.trans (congrArg (f ≫ ·) hg.symm) (Category.assoc f g pZ)
  have hg' : (f ≫ g) ≫ pZ = pX :=
    Eq.trans (Eq.trans (Category.assoc f g pZ).symm
      (congrArg (f ≫ ·) hg)) hf
  -- the first components: both are the identity on the source
  have hfst : (graphComposite pX pY pZ f hf g hg ≫
      graphCompositeMap pX pY pZ) ≫ pullback.fst pX pZ = 𝟙 X := by
    calc (graphComposite pX pY pZ f hf g hg ≫
            graphCompositeMap pX pY pZ) ≫ pullback.fst pX pZ
        = graphComposite pX pY pZ f hf g hg ≫
            (graphCompositeMap pX pY pZ ≫
              pullback.fst pX pZ) :=
          Category.assoc _ _ _
      _ = graphComposite pX pY pZ f hf g hg ≫
            (pullback.fst (pullback.snd pX pY) (pullback.fst pY pZ) ≫
              pullback.fst pX pY) :=
          congrArg (graphComposite pX pY pZ f hf g hg ≫ ·)
            (pullback.lift_fst _ _ _)
      _ = (graphComposite pX pY pZ f hf g hg ≫
            pullback.fst (pullback.snd pX pY) (pullback.fst pY pZ)) ≫
            pullback.fst pX pY :=
          (Category.assoc _ _ _).symm
      _ = graph pX pY f hf ≫ pullback.fst pX pY :=
          congrArg (· ≫ pullback.fst pX pY) (pullback.lift_fst _ _ _)
      _ = 𝟙 X := graph_fst pX pY f hf
  -- the second components: both are the composite morphism
  have hsnd : (graphComposite pX pY pZ f hf g hg ≫
      graphCompositeMap pX pY pZ) ≫ pullback.snd pX pZ =
      f ≫ g := by
    calc (graphComposite pX pY pZ f hf g hg ≫
            graphCompositeMap pX pY pZ) ≫ pullback.snd pX pZ
        = graphComposite pX pY pZ f hf g hg ≫
            (graphCompositeMap pX pY pZ ≫
              pullback.snd pX pZ) :=
          Category.assoc _ _ _
      _ = graphComposite pX pY pZ f hf g hg ≫
            (pullback.snd (pullback.snd pX pY) (pullback.fst pY pZ) ≫
              pullback.snd pY pZ) :=
          congrArg (graphComposite pX pY pZ f hf g hg ≫ ·)
            (pullback.lift_snd _ _ _)
      _ = (graphComposite pX pY pZ f hf g hg ≫
            pullback.snd (pullback.snd pX pY) (pullback.fst pY pZ)) ≫
            pullback.snd pY pZ :=
          (Category.assoc _ _ _).symm
      _ = pullback.lift f (f ≫ g) w1 ≫ pullback.snd pY pZ :=
          congrArg (· ≫ pullback.snd pY pZ) (pullback.lift_snd _ _ _)
      _ = f ≫ g := pullback.lift_snd f (f ≫ g) w1
  -- the two morphisms agree by the universal property
  refine pullback.hom_ext ?_ ?_
  · refine Eq.trans hfst (graph_fst pX pZ (f ≫ g) hg').symm
  · refine Eq.trans hsnd (graph_snd pX pZ (f ≫ g) hg').symm

end AlgebraicGeometry
