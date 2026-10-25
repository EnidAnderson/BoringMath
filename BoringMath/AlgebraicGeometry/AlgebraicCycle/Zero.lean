/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic

/-!
# Zero-cycles

A zero-cycle is an algebraic cycle with finite support. This module
introduces the finiteness predicate, the local degree of a cycle at a
point along a morphism — the multiplicity of the point weighted by its
residue degree — the degree of the cycle as the sum of the local degrees
over an explicitly given finite set containing the support, and the
basic laws: the local degrees are additive, the local degree of a point
cycle is its weighted residue degree, and the degree is additive.

The degree is summed over an explicitly given finite set of points
containing the support; the value is independent of the choice, since
the local degree vanishes off the support.

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

-- Reference: W. Fulton, *Intersection Theory*, ch. 1, §1 (the
-- multiplicities of a formal sum: the multiplicity of a point in a sum
-- of cycles is the sum of the multiplicities).
-- REVIEW(citation): pin down the exact section in review.
/-- **Multiplicities add**: the multiplicity of a point in a sum of
cycles is the sum of the multiplicities. -/
theorem multiplicity_add {R : Type*} [AddMonoid R] (D E : AlgebraicCycle X R)
    (x : X) : (D + E) x = D x + E x :=
  Pi.add_apply ↑D ↑E x

-- Reference: W. Fulton, *Intersection Theory*, ch. 1, §1 (the multiplicity
-- of a point cycle at its point is the coefficient).
-- REVIEW(citation): pin down the exact section in review.
/-- **The multiplicity of a point cycle at its point**: the point cycle
`r · [x]` has multiplicity `r` at `x`. -/
theorem multiplicity_single [DecidableEq X] (x : X) (r : ℤ) :
    Function.locallyFinsuppWithin.single x r x = r :=
  Eq.trans Function.locallyFinsuppWithin.single_apply (ite_eq_left rfl)

-- Reference: W. Fulton, *Intersection Theory*, ch. 1 (the local degree
-- of a zero-cycle at a point: the multiplicity weighted by the residue
-- degree, as for a finite morphism of curves).
-- REVIEW(citation): pin down the section.
/-- The **local degree** of a cycle at a point along a morphism `g`: the
multiplicity of the point weighted by the residue degree of the point
over `g`.

The residue degree of a point is the rank of its residue field
extension, which is nonconstructive in general; the local degree is
therefore noncomputable. -/
noncomputable def localDegree (g : X ⟶ Y) (D : AlgebraicCycle X ℤ) (x : X) :
    ℤ := D x * (g.residueDegree x : ℤ)

-- Reference: W. Fulton, *Intersection Theory*, ch. 1 (local degrees
-- are additive).
-- REVIEW(citation): pin down the section.
/-- **Local degrees add**: the local degree of a sum of cycles at a
point is the sum of the local degrees. -/
theorem localDegree_add (g : X ⟶ Y) (D E : AlgebraicCycle X ℤ) (x : X) :
    localDegree g (D + E) x = localDegree g D x + localDegree g E x :=
  Eq.trans (congrArg₂ HMul.hMul (multiplicity_add D E x) rfl)
    (add_mul (D x) (E x) (g.residueDegree x))

-- Reference: W. Fulton, *Intersection Theory*, ch. 1 (the local degree
-- of the zero cycle).
-- REVIEW(citation): pin down the section.
/-- The local degree of the zero cycle is zero. -/
theorem localDegree_zero (g : X ⟶ Y) (x : X) :
    localDegree g (0 : AlgebraicCycle X ℤ) x = 0 :=
  zero_mul _

-- Reference: W. Fulton, *Intersection Theory*, ch. 1 (the local degree
-- of a point cycle is the weighted residue degree).
-- REVIEW(citation): pin down the section.
/-- The local degree of the point cycle with coefficient `r` at `x` is
`r` times the residue degree of `x`. -/
theorem localDegree_single [DecidableEq X] (g : X ⟶ Y) (x : X) (r : ℤ) :
    localDegree g (Function.locallyFinsuppWithin.single x r) x =
      r * (g.residueDegree x : ℤ) :=
  congrArg₂ HMul.hMul (multiplicity_single x r) rfl

-- Reference: W. Fulton, *Intersection Theory*, ch. 1 (a cycle has zero
-- multiplicity off its support).
-- REVIEW(citation): pin down the section.
/-- The local degree vanishes at points outside the support. -/
theorem localDegree_eq_zero_of_notMem_support (g : X ⟶ Y)
    (D : AlgebraicCycle X ℤ) {x : X} (hx : x ∉ D.support) :
    localDegree g D x = 0 :=
  Eq.trans (congrArg₂ HMul.hMul (Function.notMem_support.mp hx) rfl)
    (zero_mul _)

-- Reference: W. Fulton, *Intersection Theory*, ch. 1, §1.4 (degree as
-- the sum of the local degrees).
-- REVIEW(citation): pin down the section.
/-- The **degree** (trace) of a cycle along a morphism `g`: the sum of
the local degrees over a finite set of points containing the support.

The local degree is nonconstructive (the residue degree is the rank of
a field extension); the degree is therefore noncomputable. -/
noncomputable def degree (g : X ⟶ Y) (D : AlgebraicCycle X ℤ) (s : Finset X)
    (_hs : D.support ⊆ ↑s) : ℤ :=
  ∑ x ∈ s, localDegree g D x

-- Reference: W. Fulton, *Intersection Theory*, ch. 1, §1.4.
-- REVIEW(citation): pin down the section.
/-- The degree of the zero cycle is zero. -/
theorem degree_zero (g : X ⟶ Y) (s : Finset X)
    (hs : (0 : AlgebraicCycle X ℤ).support ⊆ ↑s) :
    degree g 0 s hs = 0 :=
  Finset.sum_eq_zero fun x _ => localDegree_zero g x

-- Reference: W. Fulton, *Intersection Theory*, ch. 1, §1.4 (the degree
-- of a point cycle `[x]` is the residue degree of `x`).
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
      (localDegree g (Function.locallyFinsuppWithin.single x r)) x)
    (localDegree_single g x r)

-- Reference: W. Fulton, *Intersection Theory*, ch. 1, §1.4 (the degree
-- is additive: it is a homomorphism of the group of zero-cycles).
-- REVIEW(citation): pin down the section.
/-- The degree is additive: the degree of a sum, summed over the union of
two containing sets, is the sum of the degrees. -/
theorem degree_add [DecidableEq X] (g : X ⟶ Y) (D E : AlgebraicCycle X ℤ)
    (s t : Finset X) (hs : D.support ⊆ ↑s) (ht : E.support ⊆ ↑t)
    (h : (D + E).support ⊆ ↑(s ∪ t)) :
    degree g (D + E) (s ∪ t) h = degree g D s hs + degree g E t ht := by
  change ∑ x ∈ s ∪ t, localDegree g (D + E) x =
    ∑ x ∈ s, localDegree g D x + ∑ x ∈ t, localDegree g E x
  calc ∑ x ∈ s ∪ t, localDegree g (D + E) x
      = ∑ x ∈ s ∪ t, (localDegree g D x + localDegree g E x) :=
        Finset.sum_congr rfl fun x _ => localDegree_add g D E x
    _ = ∑ x ∈ s ∪ t, localDegree g D x +
        ∑ x ∈ s ∪ t, localDegree g E x :=
        Finset.sum_add_distrib
    _ = ∑ x ∈ s, localDegree g D x + ∑ x ∈ t, localDegree g E x :=
        congrArg₂ HAdd.hAdd
          (Eq.symm (Finset.sum_subset Finset.subset_union_left
            fun x _ hx => localDegree_eq_zero_of_notMem_support g D
              (Set.notMem_subset hs hx)))
          (Eq.symm (Finset.sum_subset Finset.subset_union_right
            fun x _ hx => localDegree_eq_zero_of_notMem_support g E
              (Set.notMem_subset ht hx)))

end AlgebraicCycle

end AlgebraicGeometry
