/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic

/-!
# Zero-cycles

A zero-cycle is an algebraic cycle with finite support. This module
introduces the finiteness predicate, the degree (trace) of a cycle along
a morphism — the sum of the coefficients weighted by the residue degrees
of their points — and its basic laws: the degree of the zero cycle, of a
point cycle, and additivity.

The degree is summed over an explicitly given finite set of points
containing the support; the value is independent of the choice, since a
cycle vanishes off its support.

## References
* Stacks Project, *Chow Homology*, tags 02QR–02R9 (algebraic cycles,
  pushforward, residue degrees).
* W. Fulton, *Intersection Theory*, ch. 1 (degrees of zero-cycles).
  REVIEW(citation): pin down the section.
-/

universe u v

namespace AlgebraicGeometry

open CategoryTheory

variable {X Y : Scheme.{u}}

namespace AlgebraicCycle

-- Reference: W. Fulton, *Intersection Theory*, ch. 1, §1 (a cycle is a
-- finite formal sum of points).
-- REVIEW(citation): pin down the exact section in review.
/-- A cycle has finite support. -/
def IsFinite {R : Type*} [Zero R] (D : AlgebraicCycle X R) : Prop :=
  D.support.Finite

-- Reference: W. Fulton, *Intersection Theory*, ch. 1, §1 (the empty
-- formal sum).
-- REVIEW(citation): pin down the exact section in review.
/-- The zero cycle has finite support. -/
theorem isFinite_zero {R : Type*} [AddMonoid R] :
    IsFinite (0 : AlgebraicCycle X R) :=
  Set.Finite.subset Set.finite_empty (Eq.subset Function.support_zero)

-- Reference: W. Fulton, *Intersection Theory*, ch. 1, §1 (the support of
-- a sum of formal sums is the union of the supports).
-- REVIEW(citation): pin down the exact section in review.
/-- Finite support is closed under addition. -/
theorem IsFinite.add {R : Type*} [AddMonoid R] {D E : AlgebraicCycle X R}
    (hD : IsFinite D) (hE : IsFinite E) : IsFinite (D + E) :=
  Set.Finite.subset (Set.Finite.union hD hE) (Function.support_add ↑D ↑E)

-- Reference: W. Fulton, *Intersection Theory*, ch. 1, §1 (a point cycle
-- `[x]` has support `{x}`).
-- REVIEW(citation): pin down the exact section in review.
/-- A point cycle has finite support. -/
theorem isFinite_single {R : Type*} [Zero R] [DecidableEq X] (x : X) (r : R) :
    IsFinite (Function.locallyFinsuppWithin.single x r) :=
  Set.Finite.subset (Set.finite_singleton x)
    (Set.Subset.trans (Eq.subset (congrArg Function.support
        Function.locallyFinsuppWithin.coe_single))
      (Pi.support_single_subset (i := x) (a := r)))

-- Reference: W. Fulton, *Intersection Theory*, ch. 1, §1 (the support of
-- a sum of formal sums is contained in the union of the supports of the
-- summands).
-- REVIEW(citation): pin down the exact section in review.
/-- If two finite sets contain the supports of two cycles, their union
contains the support of the sum. -/
theorem support_add_subset_union {R : Type*} [AddMonoid R] [DecidableEq X]
    {D E : AlgebraicCycle X R} {s t : Finset X}
    (hs : D.support ⊆ ↑s) (ht : E.support ⊆ ↑t) :
    (D + E).support ⊆ ↑(s ∪ t) :=
  Set.Subset.trans (Function.support_add ↑D ↑E)
    (Set.Subset.trans (Set.union_subset_union hs ht)
      (Eq.subset (Finset.coe_union s t).symm))

-- Reference: W. Fulton, *Intersection Theory*, ch. 1, §1.4 (degree as the
-- residue-degree-weighted sum of coefficients).
-- REVIEW(citation): pin down the section.
/-- The **degree** (trace) of a cycle along a morphism `g`, summed over a
finite set of points containing the support: the sum of the coefficients
weighted by the residue degrees of their points over `g`.

The residue degree of a point is the rank of its residue field extension,
which is nonconstructive in general; the degree is therefore
noncomputable. -/
noncomputable def degree (g : X ⟶ Y) (D : AlgebraicCycle X ℤ) (s : Finset X)
    (_hs : D.support ⊆ ↑s) : ℤ :=
  ∑ x ∈ s, D x * (g.residueDegree x : ℤ)

-- Reference: W. Fulton, *Intersection Theory*, ch. 1, §1.4.
-- REVIEW(citation): pin down the section.
/-- The degree of the zero cycle is zero. -/
theorem degree_zero (g : X ⟶ Y) (s : Finset X)
    (hs : (0 : AlgebraicCycle X ℤ).support ⊆ ↑s) :
    degree g 0 s hs = 0 :=
  Finset.sum_eq_zero fun _x _ => zero_mul _

-- Reference: W. Fulton, *Intersection Theory*, ch. 1, §1.4 (the degree of
-- a point cycle `[x]` is the residue degree of `x`).
-- REVIEW(citation): pin down the section.
/-- The degree of the point cycle with coefficient `r` at `x`, summed
over the singleton `{x}`, is `r` times the residue degree of `x`. -/
theorem degree_single [DecidableEq X] (g : X ⟶ Y) (x : X) (r : ℤ)
    (hs : (Function.locallyFinsuppWithin.single x r).support ⊆
      ↑({x} : Finset X)) :
    degree g (Function.locallyFinsuppWithin.single x r) {x} hs =
      r * (g.residueDegree x : ℤ) :=
  Eq.trans
    (Finset.sum_singleton
      (fun y => Function.locallyFinsuppWithin.single x r y *
        (g.residueDegree y : ℤ)) x)
    (congrArg (fun v => v * (g.residueDegree x : ℤ))
      (Eq.trans Function.locallyFinsuppWithin.single_apply (ite_eq_left rfl)))

-- Reference: W. Fulton, *Intersection Theory*, ch. 1, §1.4 (the degree
-- is additive: it is a homomorphism of the group of zero-cycles).
-- REVIEW(citation): pin down the section.
/-- The degree is additive: the degree of a sum, summed over the union of
two containing sets, is the sum of the degrees. -/
theorem degree_add [DecidableEq X] (g : X ⟶ Y) (D E : AlgebraicCycle X ℤ)
    (s t : Finset X) (hs : D.support ⊆ ↑s) (ht : E.support ⊆ ↑t)
    (h : (D + E).support ⊆ ↑(s ∪ t)) :
    degree g (D + E) (s ∪ t) h = degree g D s hs + degree g E t ht := by
  change ∑ x ∈ s ∪ t, (D + E) x * (g.residueDegree x : ℤ) =
    ∑ x ∈ s, D x * (g.residueDegree x : ℤ) +
      ∑ x ∈ t, E x * (g.residueDegree x : ℤ)
  calc ∑ x ∈ s ∪ t, (D + E) x * (g.residueDegree x : ℤ)
      = ∑ x ∈ s ∪ t, (D x + E x) * (g.residueDegree x : ℤ) :=
        Finset.sum_congr rfl fun x _ =>
          congrArg (fun v => v * (g.residueDegree x : ℤ)) (Pi.add_apply ↑D ↑E x)
    _ = ∑ x ∈ s ∪ t, (D x * (g.residueDegree x : ℤ) +
        E x * (g.residueDegree x : ℤ)) :=
        Finset.sum_congr rfl fun x _ => add_mul (D x) (E x) (g.residueDegree x)
    _ = ∑ x ∈ s ∪ t, D x * (g.residueDegree x : ℤ) +
        ∑ x ∈ s ∪ t, E x * (g.residueDegree x : ℤ) :=
        Finset.sum_add_distrib
    _ = ∑ x ∈ s, D x * (g.residueDegree x : ℤ) +
        ∑ x ∈ s ∪ t, E x * (g.residueDegree x : ℤ) :=
        congrArg (fun u => u + ∑ x ∈ s ∪ t, E x * (g.residueDegree x : ℤ))
          (Eq.symm (Finset.sum_subset Finset.subset_union_left
            fun x _ hx' =>
              Eq.trans (congrArg (fun v => v * (g.residueDegree x : ℤ))
                (Function.notMem_support.mp fun hmem => hx' (hs hmem)))
                (zero_mul _)))
    _ = ∑ x ∈ s, D x * (g.residueDegree x : ℤ) +
        ∑ x ∈ t, E x * (g.residueDegree x : ℤ) :=
        congrArg (fun u => ∑ x ∈ s, D x * (g.residueDegree x : ℤ) + u)
          (Eq.symm (Finset.sum_subset Finset.subset_union_right
            fun x _ hx' =>
              Eq.trans (congrArg (fun v => v * (g.residueDegree x : ℤ))
                (Function.notMem_support.mp fun hmem => hx' (ht hmem)))
                (zero_mul _)))

end AlgebraicCycle

end AlgebraicGeometry
