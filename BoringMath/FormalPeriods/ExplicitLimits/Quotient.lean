/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Data.Quot
import BoringMath.FormalPeriods.ExplicitLimits.Basic

/-!
# Quotients by a subspace, as explicit quotient data

The quotient of a carrier by a `Subspace` as an explicit `Quot`
(witness-carrying, `Quot.sound` only), with its operations, the quotient map
`quotMk`, and the universal property `quotLift`.
-/

universe u

namespace BoringMath

variable {K : Type u} [Field K]
variable {V W : Type u} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-! ## Quotients by a subspace, as explicit quotient data -/

-- Reference: Mac Lane, CWM 2nd ed., Ch. VIII §1 (p. 191, cokernels/quotients);
-- the witness-carrying quotient form is the `FreeTensor` precedent (quotient
-- by a data relation, `Quot.sound` only).
/-- The quotient relation of `V` by a subspace `S`: `x` and `y` are related
iff `x - y ∈ S`. -/
def quotRel (S : Subspace K V) (x y : V) : Prop := S.carrier (x - y)

-- Reference: Mac Lane, CWM 2nd ed., Ch. VIII §1 (p. 191); Lean 4 core
-- (`Quot`).
/-- The quotient of a vector-space carrier by a subspace, as an explicit
`Quot` (data-parameterized; only `Quot.sound` is ever used). -/
abbrev VecQuot (S : Subspace K V) : Type u := Quot (quotRel S)

-- Reference: Mac Lane, CWM 2nd ed., Ch. VIII §1 (p. 191, the quotient is a
-- vector space); mathlib `add_sub_add_comm` (cancellation in `V`).
/-- The quotient relation is compatible with addition on the left. -/
theorem quotRelAddLeft (S : Subspace K V) (z x y : V) (h : quotRel S x y) :
    quotRel S (z + x) (z + y) :=
  Eq.subst (motive := S.carrier) (add_sub_add_left_cancel z x y).symm (h : S.carrier (x - y))

-- Reference: Mac Lane, CWM 2nd ed., Ch. VIII §1 (p. 191); mathlib
-- `add_sub_add_comm`, `add_zero`.
/-- The quotient relation is compatible with addition on the right. -/
theorem quotRelAddRight (S : Subspace K V) (x y z : V) (h : quotRel S x y) :
    quotRel S (x + z) (y + z) :=
  Eq.subst (motive := S.carrier) (add_sub_add_right_cancel x y z).symm (h : S.carrier (x - y))

-- Reference: Mac Lane, CWM 2nd ed., Ch. VIII §1 (p. 191); mathlib `smul_sub`.
/-- The quotient relation is compatible with scalar multiplication. -/
theorem quotRelSmul (S : Subspace K V) (c : K) (x y : V) (h : quotRel S x y) :
    quotRel S (c • x) (c • y) :=
  Eq.subst (motive := S.carrier) (smul_sub c x y) (S.smul_mem c h)

-- Reference: Mac Lane, CWM 2nd ed., Ch. VIII §1 (p. 191); mathlib `neg_sub`,
-- `neg_neg`, `sub_eq_add_neg`.
/-- The quotient relation is compatible with negation. -/
theorem quotRelNeg (S : Subspace K V) (x y : V) (h : quotRel S x y) :
    quotRel S (-x) (-y) :=
  Eq.subst (motive := S.carrier) (neg_sub_eq_neg_sub x y).symm (S.neg_mem h)

-- Reference: Lean 4 core (`Quot.map₂`); primitive definitional instance.
/-- Zero of the quotient: the class of `0`. -/
instance quotZero (S : Subspace K V) : Zero (VecQuot S) := ⟨Quot.mk (quotRel S) 0⟩

-- Reference: Lean 4 core (`Quot.map₂`); primitive definitional instance.
/-- Addition on the quotient, descended from addition on `V`. -/
instance quotAdd (S : Subspace K V) : Add (VecQuot S) :=
  ⟨Quot.map₂ (fun x y => x + y) (quotRelAddLeft S) (quotRelAddRight S)⟩

-- Reference: Lean 4 core (`Quot.lift`); Dummit–Foote, §10.4 (the quotient's
-- well-defined operations).
/-- The scalar action on the quotient, descended from the scalar action on
`V`. -/
def quotSmulOp (S : Subspace K V) (c : K) : VecQuot S → VecQuot S :=
  Quot.lift (fun x => Quot.mk (quotRel S) (c • x))
    (fun a b h => Quot.sound (quotRelSmul S c a b h))

-- Reference: Lean 4 core (definitional unfolding of the `SMul` instance).
/-- Scalar multiplication on the quotient. -/
instance quotSMul (S : Subspace K V) : SMul K (VecQuot S) := ⟨quotSmulOp S⟩

-- Reference: Lean 4 core (`Quot.lift`); Mac Lane, CWM 2nd ed., Ch. VIII §1.
/-- Negation on the quotient, descended from negation on `V`. -/
def quotNegOp (S : Subspace K V) : VecQuot S → VecQuot S :=
  Quot.lift (fun x => Quot.mk (quotRel S) (-x))
    (fun a b h => Quot.sound (quotRelNeg S a b h))

-- Reference: Lean 4 core (definitional unfolding of the `Neg` instance).
/-- Negation on the quotient. -/
instance quotNeg (S : Subspace K V) : Neg (VecQuot S) := ⟨quotNegOp S⟩

-- Reference: Lean 4 core (definitional unfolding of the instances); primitive
-- definitional lemmas.
/-- The `0` of the quotient is the class of `0`. -/
theorem quotZeroMk (S : Subspace K V) : (0 : VecQuot S) = Quot.mk (quotRel S) 0 := rfl

-- Reference: mathlib `Mathlib/Data/Quot.lean` (`Quot.map₂_mk`); primitive
-- definitional lemma.
/-- Addition of two classes is the class of the sum. -/
theorem quotAddMk (S : Subspace K V) (x y : V) :
    (Quot.mk (quotRel S) x + Quot.mk (quotRel S) y : VecQuot S)
      = Quot.mk (quotRel S) (x + y) :=
  Quot.map₂_mk (fun a b => a + b) (quotRelAddLeft S) (quotRelAddRight S) x y

-- Reference: Lean 4 core (definitional unfolding of the `SMul` instance);
-- primitive definitional lemma.
/-- The `•` on the quotient unfolds to `quotSmulOp`. -/
theorem quotSmulEq (S : Subspace K V) (c : K) (q : VecQuot S) :
    c • q = quotSmulOp S c q := rfl
-- Reference: mathlib `Mathlib/Data/Quot.lean` (`Quot.lift_mk`); primitive
-- definitional lemma.
/-- `quotSmulOp` applied to a class is the class of the scalar multiple. -/
theorem quotSmulOp_mk (S : Subspace K V) (c : K) (x : V) :
    quotSmulOp S c (Quot.mk (quotRel S) x) = Quot.mk (quotRel S) (c • x) :=
  Quot.lift_mk (fun x => Quot.mk (quotRel S) (c • x))
    (fun a b h => Quot.sound (quotRelSmul S c a b h)) x

-- Reference: Lean 4 core (definitional unfolding of the `Neg` instance);
-- primitive definitional lemma.
/-- The `-` on the quotient unfolds to `quotNegOp`. -/
theorem quotNegEq (S : Subspace K V) (q : VecQuot S) : -q = quotNegOp S q := rfl

-- Reference: mathlib `Mathlib/Data/Quot.lean` (`Quot.lift_mk`); primitive
-- definitional lemma.
/-- `quotNegOp` applied to a class is the class of the negation. -/
theorem quotNegOp_mk (S : Subspace K V) (x : V) :
    quotNegOp S (Quot.mk (quotRel S) x) = Quot.mk (quotRel S) (-x) :=
  Quot.lift_mk (fun x => Quot.mk (quotRel S) (-x))
    (fun a b h => Quot.sound (quotRelNeg S a b h)) x


-- Reference: mathlib `Mathlib/Data/Quot.lean` (`Quot.lift_mk`); primitive
-- definitional lemma.
/-- Scalar multiplication of a class is the class of the scalar multiple. -/
theorem quotSmulMk (S : Subspace K V) (c : K) (x : V) :
    (c • Quot.mk (quotRel S) x : VecQuot S) = Quot.mk (quotRel S) (c • x) :=
  Eq.trans (quotSmulEq S c (Quot.mk (quotRel S) x)) (quotSmulOp_mk S c x)

-- Reference: mathlib `Mathlib/Data/Quot.lean` (`Quot.lift_mk`); primitive
-- definitional lemma.
/-- Negation of a class is the class of the negation. -/
theorem quotNegMk (S : Subspace K V) (x : V) :
    (-Quot.mk (quotRel S) x : VecQuot S) = Quot.mk (quotRel S) (-x) :=
  Eq.trans (quotNegEq S (Quot.mk (quotRel S) x)) (quotNegOp_mk S x)

-- Reference: Mac Lane, CWM 2nd ed., Ch. VIII §1 (p. 191, the quotient map).
/-- The quotient map `V → V/S`, as an explicit linear map. -/
def quotMk (S : Subspace K V) : VecHom K V (VecQuot S) where
  toFun := fun x => Quot.mk (quotRel S) x
  map_add' := fun x y => quotAddMk S x y
  map_smul' := fun c x => quotSmulMk S c x

-- Reference: definitional peel of `quotMk`.
/-- The quotient map sends `x` to its class. -/
theorem quotMk_apply (S : Subspace K V) (x : V) : quotMk S x = Quot.mk (quotRel S) x := rfl

variable {X : Type u} [Add X] [Zero X] [SMul K X]
-- Reference: mathlib `Mathlib/Data/Quot.lean` (`Quot.lift_mk`, `Quot.map₂_mk`);
-- Mac Lane, CWM 2nd ed., Ch. VIII §1 (p. 191, the descended operations).
/-- Additivity of the quotient lift on classes, via the beta rule and
`quotAddMk`. -/
theorem quotLift_add_mk (S : Subspace K V) (h : VecHom K V X)
    (hrel : ∀ x y, quotRel S x y → h x = h y) (a b : V) :
    Quot.lift h (fun x y hab => hrel x y hab)
        (Quot.mk (quotRel S) a + Quot.mk (quotRel S) b)
      = Quot.lift h (fun x y hab => hrel x y hab) (Quot.mk (quotRel S) a)
        + Quot.lift h (fun x y hab => hrel x y hab) (Quot.mk (quotRel S) b) :=
  Eq.trans
    (congrArg (Quot.lift h (fun x y hab => hrel x y hab)) (quotAddMk S a b))
    (Eq.trans (Quot.lift_mk h (fun x y hab => hrel x y hab) (a + b))
      (Eq.trans (h.map_add' a b)
        (add_eq_add_of_eq (Quot.lift_mk h (fun x y hab => hrel x y hab) a)
          (Quot.lift_mk h (fun x y hab => hrel x y hab) b)).symm))

-- Reference: mathlib `Mathlib/Data/Quot.lean` (`Quot.lift_mk`);
-- Mac Lane, CWM 2nd ed., Ch. VIII §1 (p. 191).
/-- Homogeneity of the quotient lift on classes, via the beta rule and
`quotSmulMk`. -/
theorem quotLift_smul_mk (S : Subspace K V) (h : VecHom K V X)
    (hrel : ∀ x y, quotRel S x y → h x = h y) (c : K) (a : V) :
    Quot.lift h (fun x y hab => hrel x y hab) (c • Quot.mk (quotRel S) a)
      = c • Quot.lift h (fun x y hab => hrel x y hab) (Quot.mk (quotRel S) a) :=
  Eq.trans
    (congrArg (Quot.lift h (fun x y hab => hrel x y hab)) (quotSmulMk S c a))
    (Eq.trans (Quot.lift_mk h (fun x y hab => hrel x y hab) (c • a))
      (Eq.trans (h.map_smul' c a)
        (congrArg (fun t => c • t) (Quot.lift_mk h (fun x y hab => hrel x y hab) a)).symm))


-- Reference: Mac Lane, CWM 2nd ed., Ch. VIII §1 (p. 191, the universal
-- property of the quotient); Lean 4 core (`Quot.lift`).
/-- The lift of a linear map `h : V → X` to the quotient `V/S`, given that `h`
respects the quotient relation. -/
def quotLift (S : Subspace K V) (h : VecHom K V X)
    (hrel : ∀ x y, quotRel S x y → h x = h y) : VecHom K (VecQuot S) X where
  toFun := Quot.lift h (fun a b hab => hrel a b hab)
  map_add' := fun q₁ q₂ => Quot.induction_on₂ q₁ q₂ (fun a b => quotLift_add_mk S h hrel a b)
  map_smul' := fun c q => Quot.inductionOn (motive := fun q =>
      Quot.lift h (fun a b hab => hrel a b hab) (c • q)
        = c • Quot.lift h (fun a b hab => hrel a b hab) q) q
    (fun a => quotLift_smul_mk S h hrel c a)

-- Reference: mathlib `Mathlib/Data/Quot.lean` (`Quot.lift_mk`).
/-- Beta rule of the quotient's universal property. -/
theorem quotLift_mk (S : Subspace K V) (h : VecHom K V X)
    (hrel : ∀ x y, quotRel S x y → h x = h y) (x : V) :
    quotLift S h hrel (quotMk S x) = h x :=
  Quot.lift_mk h (fun a b hab => hrel a b hab) x

-- Reference: Mac Lane, CWM 2nd ed., Ch. VIII §1 (p. 191, uniqueness of the
-- factorization through the quotient).
/-- Uniqueness: any explicit linear map out of the quotient agreeing with `h`
on classes is the lift of `h`. -/
theorem quotLift_unique (S : Subspace K V) (h : VecHom K V X)
    (hrel : ∀ x y, quotRel S x y → h x = h y) (k : VecHom K (VecQuot S) X)
    (hk : ∀ x, k (quotMk S x) = h x) : k = quotLift S h hrel :=
  vecHom_ext fun q => Quot.inductionOn q (fun a => hk a)

-- Reference: Mac Lane, CWM 2nd ed., Ch. VIII §1 (p. 191); Axler, Ch. 1.
/-- The kills-form of the quotient's universal property: a linear map that
vanishes on `S` factors through the quotient (target a full vector space). -/
def quotLift_of_kills {Y : Type u} [AddCommGroup Y] [Module K Y] (S : Subspace K V)
    (h : VecHom K V Y) (hS : ∀ s, S.carrier s → h s = 0) : VecHom K (VecQuot S) Y :=
  quotLift S h (fun x y hrel =>
    sub_eq_zero.mp
      (Eq.subst (motive := fun t => t = 0) (vecHom_map_sub h x y) (hS (x - y) hrel)))

-- Reference: Lean 4 core (`Quot.exists_rep`).
/-- Every class in the quotient is the class of some element (surjectivity of
the quotient map). -/
theorem quotMk_surj (S : Subspace K V) (q : VecQuot S) : ∃ x, q = quotMk S x := by
  obtain ⟨x, hx⟩ := Quot.exists_rep q
  exact ⟨x, hx.symm⟩

end BoringMath
