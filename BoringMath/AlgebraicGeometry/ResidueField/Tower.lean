/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.AlgebraicGeometry.ResidueField

/-!
# The residue field tower

The residue field of a point is an algebra over the residue field of its
image, via the residue field map. For a composite of morphisms the residue
fields form a scalar tower, and the residue degree of the composite is the
product of the residue degrees — the tower law for the degrees of field
extensions.

## References
* S. Lang, *Algebra*, revised 3rd ed., Springer, 2002 (the tower law:
  the degree of a tower of field extensions is the product of the
  degrees).
  REVIEW(citation): pin down the section.
* Stacks Project, *Chow Homology*, tag 02R4 (the residue degree as the
  weight of the pushforward).
  REVIEW(citation): pin down the exact tag.
-/

universe u

namespace AlgebraicGeometry

open CategoryTheory

namespace Scheme

variable {X Y Z : Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ Z) (x : X)

namespace Hom

-- Reference: S. Lang, *Algebra* (a ring map from a commutative ring
-- gives the target the structure of an algebra).
-- REVIEW(citation): pin down the section.
/-- The residue field of a point is an algebra over the residue field of
its image, via the residue field map. The residue field of a point is
the residue field of a stalk, which is nonconstructive; the algebra is
therefore noncomputable. -/
noncomputable instance residueFieldAlgebra (f : X ⟶ Y) (x : X) :
    Algebra (Y.residueField (f x)) (X.residueField x) :=
  (f.residueFieldMap x).hom.toAlgebra

-- Reference: Stacks Project, tag 02R4 (the residue field map of a
-- composite at the middle point).
-- REVIEW(citation): pin down the exact tag.
/-- The residue field of the middle point is an algebra over the residue
field of the image under the composite, via the residue field map of
the second morphism. -/
noncomputable instance residueFieldAlgebra_comp (g : X ⟶ Y) (h : Y ⟶ Z)
    (x : X) :
    Algebra (Z.residueField ((g ≫ h) x)) (Y.residueField (g x)) :=
  residueFieldAlgebra h (g x)

-- Reference: Stacks Project, tag 02R4 (residue field maps compose).
-- REVIEW(citation): pin down the exact tag.
/-- The residue field map of a composite is the composite of the residue
field maps, at elements. -/
theorem residueFieldMap_comp_apply (r : (Z.residueField (h (g x)))) :
    (g.residueFieldMap x).hom ((h.residueFieldMap (g x)).hom r) =
      ((g ≫ h).residueFieldMap x).hom r :=
  calc (g.residueFieldMap x).hom ((h.residueFieldMap (g x)).hom r)
      = ((g.residueFieldMap x).hom.comp (h.residueFieldMap (g x)).hom) r :=
        Eq.symm (RingHom.comp_apply (g.residueFieldMap x).hom
          (h.residueFieldMap (g x)).hom r)
    _ = (h.residueFieldMap (g x) ≫ g.residueFieldMap x).hom r := rfl
    _ = ((g ≫ h).residueFieldMap x).hom r :=
        DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
          (residueFieldMap_comp g h x).symm) r

-- Reference: S. Lang, *Algebra* (the tower law: scalar multiplication by
-- the top field factors through the middle field).
-- REVIEW(citation): pin down the section.
/-- The residue fields along a composite form a scalar tower: scalar
multiplication by the top residue field factors through the middle
one. -/
theorem residueFieldIsScalarTower :
    @IsScalarTower (Z.residueField ((g ≫ h) x)) (Y.residueField (g x))
      (X.residueField x)
      (@Algebra.toSMul (Z.residueField ((g ≫ h) x)) (Y.residueField (g x))
        _ _ (residueFieldAlgebra h (g x)))
      (@Algebra.toSMul (Y.residueField (g x)) (X.residueField x)
        _ _ (residueFieldAlgebra g x))
      (@Algebra.toSMul (Z.residueField ((g ≫ h) x)) (X.residueField x)
        _ _ (residueFieldAlgebra (g ≫ h) x)) := by
  refine @IsScalarTower.mk _ _ _ _ _ _ fun f k a => ?_
  calc (f • k) • a
      = ((h.residueFieldMap (g x)).hom f * k) • a :=
        congrArg₂ SMul.smul (Algebra.smul_def f k) rfl
    _ = (g.residueFieldMap x).hom ((h.residueFieldMap (g x)).hom f * k) * a :=
        Algebra.smul_def _ a
    _ = ((g.residueFieldMap x).hom ((h.residueFieldMap (g x)).hom f) *
          (g.residueFieldMap x).hom k) * a :=
        congrArg₂ HMul.hMul
          (RingHom.map_mul (g.residueFieldMap x).hom
            ((h.residueFieldMap (g x)).hom f) k)
          rfl
    _ = (((g ≫ h).residueFieldMap x).hom f *
          (g.residueFieldMap x).hom k) * a :=
        congrArg₂ HMul.hMul
          (congrArg₂ HMul.hMul (residueFieldMap_comp_apply g h x f) rfl)
          rfl
    _ = ((g ≫ h).residueFieldMap x).hom f *
        ((g.residueFieldMap x).hom k * a) :=
        mul_assoc _ _ _
    _ = f • (k • a) :=
        Eq.symm (Eq.trans
          (congrArg₂ SMul.smul rfl (Algebra.smul_def k a))
          (Algebra.smul_def f ((g.residueFieldMap x).hom k * a)))

-- Reference: S. Lang, *Algebra* (the tower law: the degree of a tower of
-- field extensions is the product of the degrees).
-- REVIEW(citation): pin down the section.
/-- **The tower law for residue degrees**: the residue degree of a
composite is the product of the residue degrees along the tower. -/
theorem residueDegree_comp :
    (g ≫ h).residueDegree x = h.residueDegree (g x) * g.residueDegree x := by
  exact Eq.symm (@Module.finrank_mul_finrank
    (Z.residueField ((g ≫ h) x)) (Y.residueField (g x)) (X.residueField x)
    _ _ _ _ _ _ (residueFieldIsScalarTower g h x) _ _ _ _)

-- Reference: S. Lang, *Algebra* (the degree of an isomorphism of fields
-- is one).
-- REVIEW(citation): pin down the section.
/-- The residue degree of an isomorphism is one: composing with the
inverse is the identity, and the tower law identifies the factors. -/
theorem residueDegree_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
    (x : X) : f.residueDegree x = 1 :=
  (mul_eq_one.mp (Eq.trans (residueDegree_comp f (inv f) x).symm
    (Eq.trans (congrArg (fun ψ => ψ.residueDegree x) (IsIso.hom_inv_id f))
      (Hom.residueDegree_id x)))).2

end Hom

end Scheme

end AlgebraicGeometry
