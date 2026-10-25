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

end AlgebraicGeometry
