/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringMath.AlgebraicGeometry.ResidueField.Preimmersion
import Mathlib.AlgebraicGeometry.Fiber

/-!
# The residue fields of the scheme-theoretic fiber

The residue degree of the fiber embedding at the point of the fiber over a
point is one: the fiber embedding and the canonical map from the spectrum of
the residue field are preimmersions, and the tower law identifies the
degrees along the fiber square. The residue fields of the fiber are those of
the ambient scheme.

## References
* [Fulton] W. Fulton, *Intersection Theory*, ch. 1 (the scheme-theoretic
  fiber at a point carries the residue fields of the ambient scheme).
  REVIEW(citation): pin down the section.
* [Lang] S. Lang, *Algebra*, revised 3rd ed., Springer, 2002 (the tower
  law for the degrees of field extensions).
  REVIEW(citation): pin down the section.
-/

universe u

namespace AlgebraicGeometry

open CategoryTheory

namespace Scheme

namespace Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)

-- Reference: [Fulton], ch. 1 (the residue fields of the fiber are those of
-- the ambient scheme at the points of the fiber).
-- REVIEW(citation): pin down the section.
/-- **The residue degree of the fiber embedding is one**: at the point of
the scheme-theoretic fiber over a point of the ambient scheme, the fiber
embedding induces an isomorphism of residue fields. The fiber square
factors the canonical map from the spectrum of the residue field through
the fiber embedding; the tower law identifies the degrees along the
factorization, and both factors are preimmersions. -/
theorem residueDegree_fiberι :
    (f.fiberι (f x)).residueDegree (f.asFiber x) = 1 := by
  have h1 : (X.fromSpecResidueField x).residueDegree
      (IsLocalRing.closedPoint (X.residueField x)) = 1 :=
    residueDegree_of_isPreimmersion (X.fromSpecResidueField x)
      (IsLocalRing.closedPoint (X.residueField x))
  have h2 : (f.asFiberHom x).residueDegree
      (IsLocalRing.closedPoint (X.residueField x)) = 1 :=
    residueDegree_of_isPreimmersion (f.asFiberHom x)
      (IsLocalRing.closedPoint (X.residueField x))
  have h3 : (X.fromSpecResidueField x).residueDegree
      (IsLocalRing.closedPoint (X.residueField x)) =
      (f.fiberι (f x)).residueDegree
        ((f.asFiberHom x) (IsLocalRing.closedPoint (X.residueField x))) *
      (f.asFiberHom x).residueDegree (IsLocalRing.closedPoint (X.residueField x)) :=
    Eq.subst
      (motive := fun g : Spec (X.residueField x) ⟶ X =>
        Scheme.Hom.residueDegree g (IsLocalRing.closedPoint (X.residueField x)) =
        (f.fiberι (f x)).residueDegree
          ((f.asFiberHom x) (IsLocalRing.closedPoint (X.residueField x))) *
        (f.asFiberHom x).residueDegree (IsLocalRing.closedPoint (X.residueField x)))
      (asFiberHom_fiberι f x)
      (residueDegree_comp (f.asFiberHom x) (f.fiberι (f x))
        (IsLocalRing.closedPoint (X.residueField x)))
  have h4 : (f.fiberι (f x)).residueDegree
        ((f.asFiberHom x) (IsLocalRing.closedPoint (X.residueField x))) =
      (f.fiberι (f x)).residueDegree (f.asFiber x) :=
    congrArg (fun z => (f.fiberι (f x)).residueDegree z)
      (asFiberHom_apply f x (IsLocalRing.closedPoint (X.residueField x)))
  calc (f.fiberι (f x)).residueDegree (f.asFiber x)
      = (f.fiberι (f x)).residueDegree (f.asFiber x) * 1 :=
        Eq.symm (Nat.mul_one _)
    _ = (f.fiberι (f x)).residueDegree
          ((f.asFiberHom x) (IsLocalRing.closedPoint (X.residueField x))) * 1 :=
        congrArg₂ HMul.hMul h4.symm rfl
    _ = (f.fiberι (f x)).residueDegree
          ((f.asFiberHom x) (IsLocalRing.closedPoint (X.residueField x))) *
        (f.asFiberHom x).residueDegree (IsLocalRing.closedPoint (X.residueField x)) :=
        congrArg₂ HMul.hMul rfl h2.symm
    _ = (X.fromSpecResidueField x).residueDegree
          (IsLocalRing.closedPoint (X.residueField x)) :=
        h3.symm
    _ = 1 := h1

end Hom

end Scheme

end AlgebraicGeometry
