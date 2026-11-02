/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringMath.AlgebraicGeometry.Correspondence.Graph
import BoringMath.AlgebraicGeometry.Scheme.Hom

/-!
# Finite correspondences as data (C.1)

A **finite correspondence** from `X` to `Y` over a base `S` is the
structure-of-record chosen by the C.1/C.2 ownership ruling: a formal cycle
on the fiber product `X ×_S Y` with `ℤ` coefficients that has finite support
and is **finite over the source** — every fiber of the first projection
`X ×_S Y → X` meets the support in a finite set. This is the point-set
shadow of Voevodsky's definition (the free abelian group on the integral
closed subschemes `Z ⊆ X ×_S Y` for which `Z → X` is finite and surjective
over a connected component of `X`); the decomposition of a finite cycle into
its integral components, which identifies the two presentations, is recorded
as a Tier-2 peel in the PR note.

The finite correspondences form an additive subgroup of the cycle group, hence
an abelian group (`FiniteCorrespondence` carries the induced `AddCommGroup`
instance), and the graph correspondence of a morphism over `S` is a finite
correspondence (`graphFiniteCorrespondence`).

## References
* C. Mazza, V. Voevodsky, C. Weibel, *Lecture Notes on Motivic Cohomology*,
  Clay Mathematics Monographs 2, Amer. Math. Soc. / Clay Math. Inst., 2006,
  Lecture 1 "The category of finite correspondences" (p. 3), the definition
  of `Cor_S(X, Y)`.
  REVIEW(citation): pin the exact definition number within Lecture 1.
* A. Suslin, V. Voevodsky, *Singular homology of abstract algebraic
  varieties*, J. reine angew. Math. 481 (1996), 205–232 (finite
  correspondences).
  REVIEW(citation): pin the section in review.
-/

universe u

namespace AlgebraicGeometry

open CategoryTheory Limits

variable {S X Y : Scheme.{u}}

namespace AlgebraicCycle

variable (pX : X ⟶ S) (pY : Y ⟶ S)

-- Reference: MVW (2006), Lecture 1, p. 3 (a finite correspondence is finite
-- over the source scheme).
-- REVIEW(citation): pin the exact definition number within Lecture 1.
/-- A cycle on `W` is **finite over** `X` along `π : W ⟶ X` when every fiber
of `π` meets the support in a finite set. -/
def IsFiniteOverSource {W : Scheme.{u}} (π : W ⟶ X) (c : AlgebraicCycle W ℤ) : Prop :=
  ∀ x : ↥X, (π.base ⁻¹' {x} ∩ c.support).Finite

-- Reference: MVW (2006), Lecture 1, p. 3 (the zero correspondence is finite
-- over the source).
-- REVIEW(citation): pin the exact definition number within Lecture 1.
/-- The zero cycle is finite over the source: its support is empty. -/
theorem isFiniteOverSource_zero (pX : X ⟶ S) (pY : Y ⟶ S) :
    IsFiniteOverSource (pullback.fst pX pY) (0 : AlgebraicCycle (pullback pX pY) ℤ) := by
  have h0 : (0 : AlgebraicCycle (pullback pX pY) ℤ).support = ∅ := Function.support_zero
  intro x
  refine Set.Finite.subset Set.finite_empty ?_
  refine Set.Subset.trans inf_le_right ?_
  exact Eq.subset h0

-- Reference: MVW (2006), Lecture 1, p. 3 (finite correspondences are closed
-- under addition).
-- REVIEW(citation): pin the exact definition number within Lecture 1.
/-- Finiteness over the source is closed under addition: the support of a sum
is contained in the union of the supports, and fibers of a union are unions
of fibers. -/
theorem IsFiniteOverSource.add {W : Scheme.{u}} {π : W ⟶ X}
    {c d : AlgebraicCycle W ℤ}
    (hc : IsFiniteOverSource π c) (hd : IsFiniteOverSource π d) :
    IsFiniteOverSource π (c + d) := by
  intro x
  refine Set.Finite.subset (Set.Finite.union (hc x) (hd x)) ?_
  refine Set.Subset.trans
    (Set.inter_subset_inter_right _ (Function.support_add (c : ↥W → ℤ) (d : ↥W → ℤ))) ?_
  exact Eq.subset (Set.inter_union_distrib_left _ _ _)

-- Reference: MVW (2006), Lecture 1, p. 3 (finite correspondences are closed
-- under negation).
-- REVIEW(citation): pin the exact definition number within Lecture 1.
/-- Finiteness over the source is closed under negation: the support is
unchanged by negation. -/
theorem IsFiniteOverSource.neg {W : Scheme.{u}} {π : W ⟶ X} {c : AlgebraicCycle W ℤ}
    (hc : IsFiniteOverSource π c) : IsFiniteOverSource π (-c) :=
  fun x => Eq.subst (motive := fun t => (π.base ⁻¹' {x} ∩ t).Finite)
    (Function.locallyFinsuppWithin.support_neg c).symm (hc x)

end AlgebraicCycle

variable (pX : X ⟶ S) (pY : Y ⟶ S)

-- Reference: MVW (2006), Lecture 1, p. 3, Appendix 1A p. 7 (the group
-- `Cor_S(X, Y)` of finite correspondences as a subgroup of the cycle group
-- of `X ×_S Y`).
-- REVIEW(citation): pin the exact definition number within Lecture 1.
/-- The **additive subgroup of finite correspondences** from `X` to `Y` over
`S`: the cycles on `X ×_S Y` with finite support that are finite over the
source along the first projection. -/
def finiteCorrespondenceAddSubgroup (pX : X ⟶ S) (pY : Y ⟶ S) :
    AddSubgroup (AlgebraicCycle (pullback pX pY) ℤ) where
  carrier := {c | c.IsFinite ∧ AlgebraicCycle.IsFiniteOverSource (pullback.fst pX pY) c}
  zero_mem' := ⟨AlgebraicCycle.isFinite_zero, AlgebraicCycle.isFiniteOverSource_zero pX pY⟩
  add_mem' := by
    intro a b ha hb
    exact ⟨AlgebraicCycle.IsFinite.add ha.1 hb.1,
      AlgebraicCycle.IsFiniteOverSource.add ha.2 hb.2⟩
  neg_mem' := by
    intro a ha
    refine ⟨Eq.subst (motive := fun t => t.Finite)
      (Function.locallyFinsuppWithin.support_neg a).symm ha.1,
      AlgebraicCycle.IsFiniteOverSource.neg ha.2⟩

-- Reference: MVW (2006), Lecture 1, p. 3 (the group `Cor_S(X, Y)` of finite
-- correspondences from `X` to `Y`).
-- REVIEW(citation): pin the exact definition number within Lecture 1.
/-- A **finite correspondence** from `X` to `Y` over `S` (the C.1
structure-of-record): a cycle on `X ×_S Y` with finite support, finite over
the source. It is an abelian group via the additive-subgroup instance. -/
abbrev FiniteCorrespondence (pX : X ⟶ S) (pY : Y ⟶ S) : Type u :=
  ↥(finiteCorrespondenceAddSubgroup pX pY)

namespace FiniteCorrespondence

variable {S X Y : Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ S)

-- Reference: MVW (2006), Lecture 1, p. 3 (a finite correspondence is a cycle
-- on the fiber product).
-- REVIEW(citation): pin the exact definition number within Lecture 1.
/-- The underlying cycle of a finite correspondence. -/
def toCycle (c : FiniteCorrespondence pX pY) : AlgebraicCycle (pullback pX pY) ℤ := c.1

-- Reference: MVW (2006), Lecture 1, p. 3 (the multiplicity of a finite
-- correspondence at a point of the fiber product).
-- REVIEW(citation): pin the exact definition number within Lecture 1.
/-- The multiplicity of a finite correspondence at a point. -/
def multiplicity (c : FiniteCorrespondence pX pY) (z : ↥(pullback pX pY)) : ℤ := c.1 z

-- Reference: MVW (2006), Lecture 1, p. 3 (the support of a finite
-- correspondence).
-- REVIEW(citation): pin the exact definition number within Lecture 1.
/-- The support of a finite correspondence. -/
def support (c : FiniteCorrespondence pX pY) : Set ↥(pullback pX pY) := c.1.support

-- Reference: MVW (2006), Lecture 1, p. 3 (a finite correspondence has finite
-- support).
-- REVIEW(citation): pin the exact definition number within Lecture 1.
/-- A finite correspondence has finite support. -/
theorem isFinite (c : FiniteCorrespondence pX pY) :
    AlgebraicCycle.IsFinite (c.toCycle pX pY) :=
  c.2.1

-- Reference: MVW (2006), Lecture 1, p. 3 (a finite correspondence is finite
-- over the source).
-- REVIEW(citation): pin the exact definition number within Lecture 1.
/-- A finite correspondence is finite over the source. -/
theorem finiteOverSource (c : FiniteCorrespondence pX pY) :
    AlgebraicCycle.IsFiniteOverSource (pullback.fst pX pY) (c.toCycle pX pY) :=
  c.2.2

-- Reference: MVW (2006), Lecture 1, p. 3 (two finite correspondences are equal
-- iff their underlying cycles agree).
-- REVIEW(citation): pin the exact definition number within Lecture 1.
/-- Two finite correspondences are equal iff their underlying cycles are. -/
theorem ext_iff {c d : FiniteCorrespondence pX pY} :
    c = d ↔ c.toCycle pX pY = d.toCycle pX pY :=
  Subtype.ext_iff

-- Reference: Fulton, *Intersection Theory*, ch. 1, §1 (the zero formal sum);
-- primitive definitional lemma (projection of the zero of the subgroup).
/-- The underlying cycle of the zero correspondence is the zero cycle. -/
theorem zero_toCycle : (0 : FiniteCorrespondence pX pY).toCycle pX pY = 0 := rfl

-- Reference: Fulton, *Intersection Theory*, ch. 1, §1 (addition of formal
-- sums); primitive definitional lemma.
/-- The underlying cycle of a sum of correspondences is the sum of the
underlying cycles. -/
theorem add_toCycle (c d : FiniteCorrespondence pX pY) :
    (c + d).toCycle pX pY = c.toCycle pX pY + d.toCycle pX pY := rfl

-- Reference: Fulton, *Intersection Theory*, ch. 1, §1 (negation of formal
-- sums); primitive definitional lemma.
/-- The underlying cycle of the negative of a correspondence is the negative
of the underlying cycle. -/
theorem neg_toCycle (c : FiniteCorrespondence pX pY) :
    (-c).toCycle pX pY = -c.toCycle pX pY := rfl

-- Reference: Fulton, *Intersection Theory*, ch. 1, §1 (multiplicities add);
-- routes through the landed `AlgebraicCycle.multiplicity_add`.
/-- The multiplicity of a sum of correspondences at a point is the sum of the
multiplicities. -/
theorem multiplicity_add (c d : FiniteCorrespondence pX pY) (z : ↥(pullback pX pY)) :
    (c + d).multiplicity pX pY z = c.multiplicity pX pY z + d.multiplicity pX pY z :=
  AlgebraicCycle.multiplicity_add (c.toCycle pX pY) (d.toCycle pX pY) z

end FiniteCorrespondence

variable {X Y : Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ S)

-- Reference: MVW (2006), Lecture 1, p. 3 (the graph of a morphism is a finite
-- correspondence); the support inclusion is the landed
-- `support_graphCorrespondence` (PR #72).
-- REVIEW(citation): pin the exact definition number within Lecture 1.
/-- The graph correspondence of a morphism over `S` is finite over the source:
the fiber of the first projection over `x` meets the support of the graph
correspondence in at most the single point `graph x`, because the graph is a
section of the first projection. -/
theorem isFiniteOverSource_graphCorrespondence (f : X ⟶ Y) (hf : f ≫ pY = pX)
    [IsNoetherian X] (hqc : QuasiCompact (graph pX pY f hf)) :
    AlgebraicCycle.IsFiniteOverSource (pullback.fst pX pY)
      (graphCorrespondence pX pY f hf hqc) := by
  intro x
  refine Set.Finite.subset (Set.finite_singleton ((graph pX pY f hf).base x)) ?_
  intro w hw
  have hw1 : (pullback.fst pX pY).base w = x :=
    Set.mem_singleton_iff.mp (Set.mem_preimage.mp hw.1)
  obtain ⟨s, hs, hws⟩ := support_graphCorrespondence pX pY f hf hqc hw.2
  -- the graph is a section of the first projection: fst (graph s) = s
  have hbase : (pullback.fst pX pY).base ((graph pX pY f hf).base s) = s := by
    have h1 : ((graph pX pY f hf ≫ pullback.fst pX pY) : X ⟶ X) s = (𝟙 X : X ⟶ X) s :=
      congrFun (congrArg (fun (g : X ⟶ X) => (g : ↥X → ↥X)) (graph_fst pX pY f hf)) s
    calc (pullback.fst pX pY).base ((graph pX pY f hf).base s)
        = ((graph pX pY f hf ≫ pullback.fst pX pY) : X ⟶ X) s :=
          (Scheme.Hom.comp_apply _ _ _).symm
      _ = (𝟙 X : X ⟶ X) s := h1
      _ = s := Scheme.Hom.id_apply s
  have hsx : s = x :=
    Eq.trans hbase.symm (Eq.trans (congrArg (pullback.fst pX pY).base hws) hw1)
  exact Set.mem_singleton_iff.mpr (Eq.trans hws.symm (congrArg (graph pX pY f hf).base hsx))

-- Reference: MVW (2006), Lecture 1, p. 3 (the graph of a morphism over `S`
-- is a finite correspondence from `X` to `Y`).
-- REVIEW(citation): pin the exact definition number within Lecture 1.
-- The generic points of the source and the fiber sums of the pushforward are
-- chosen by choice; the correspondence is noncomputable.
open scoped Classical in
/-- **The graph correspondence as a finite correspondence**: the pushforward
of the fundamental cycle along the graph, repackaged with its finiteness and
finite-over-source proofs. -/
noncomputable def graphFiniteCorrespondence (f : X ⟶ Y) (hf : f ≫ pY = pX)
    [IsNoetherian X] (hqc : QuasiCompact (graph pX pY f hf)) :
    FiniteCorrespondence pX pY :=
  ⟨graphCorrespondence pX pY f hf hqc,
    ⟨isFinite_graphCorrespondence pX pY f hf hqc,
      isFiniteOverSource_graphCorrespondence pX pY f hf hqc⟩⟩

-- Reference: MVW (2006), Lecture 1, p. 3 (the cycle of the graph
-- correspondence); primitive definitional lemma.
/-- The underlying cycle of the graph correspondence is the landed
`graphCorrespondence`. -/
theorem graphFiniteCorrespondence_toCycle (f : X ⟶ Y) (hf : f ≫ pY = pX)
    [IsNoetherian X] (hqc : QuasiCompact (graph pX pY f hf)) :
    (graphFiniteCorrespondence pX pY f hf hqc).toCycle pX pY =
      graphCorrespondence pX pY f hf hqc := rfl

end AlgebraicGeometry
