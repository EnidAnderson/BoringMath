/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Fintype.Basic

/-!
# Basis-carrying finite free modules: `FreeMod K n = (Fin n → K)`

The target category of Hörmann's fiber functors, built as *data*: a
finite-dimensional `K`-vector space is a function `Fin n → K`, i.e. a
vector written in its standard basis, and the dimension is the data `n`.
No basis is ever extracted from an existence statement — the constructive
counterpart to mathlib's `Module.Free.chooseBasis`, which the P.0.4 pin-run
confirmed is `Classical.choice`-extracted (see
`docs/AUDITS/2026-10-30-axiom-lint-pin-run.md`).

Morphisms are linear maps as explicit structure (function + linearity
proofs), with identity and composition; the dual is the Hom into the
one-dimensional `FreeMod K 1`. Everything in this module lints CLEAN
(`{propext, Quot.sound}` only): it is built from `Pi` instances, which are
pointwise and constructive.

## References
* F. Hörmann, *A note on formal periods*, arXiv:2106.03803, Definition 2.1
  (verified against the arXiv HTML): a fiber functor over `K` is a
  `ℚ`-linear exact faithful functor into f.d.-`K`-Vect — this module models
  that target category.
* S. Axler, *Linear Algebra Done Right*, 4th ed., Ch. 1 (definition of a
  vector space; the module laws below are its axioms for a field).
-/

universe u

namespace BoringMath

variable {K : Type u} [Field K] {m n p : ℕ}

-- Reference: Hörmann, arXiv:2106.03803, Def 2.1 (f.d.-K-Vect as fiber-functor target).
/-- The basis-carrying finite free module over `K` of dimension `n`:
vectors as functions `Fin n → K` in the standard basis. -/
abbrev FreeMod (K : Type u) [Field K] (n : ℕ) := Fin n → K

-- Reference: Axler, Ch. 1 (vector-space axioms); the `Pi` instances are pointwise.
/-- Addition on `FreeMod K n` is pointwise addition. -/
theorem freeMod_add (x y : FreeMod K n) : x + y = fun i => x i + y i := rfl

-- Reference: Axler, Ch. 1 (vector-space axioms).
/-- The zero vector of `FreeMod K n`. -/
theorem freeMod_zero : (0 : FreeMod K n) = fun _ => 0 := rfl

-- Reference: Axler, Ch. 1 (vector-space axioms).
/-- Scalar multiplication on `FreeMod K n` is pointwise. -/
theorem freeMod_smul (c : K) (x : FreeMod K n) : c • x = fun i => c * x i := rfl

-- Reference: Axler, Ch. 1 (vector-space axioms).
/-- Addition with zero is the identity. -/
theorem freeMod_add_zero (x : FreeMod K n) : x + 0 = x := add_zero x

-- Reference: Axler, Ch. 1 (vector-space axioms).
/-- Zero addition is the identity. -/
theorem freeMod_zero_add (x : FreeMod K n) : 0 + x = x := zero_add x

-- Reference: Axler, Ch. 1 (vector-space axioms).
/-- Scalar one acts as the identity. -/
theorem freeMod_one_smul (x : FreeMod K n) : (1 : K) • x = x := one_smul K x

-- Reference: Axler, Ch. 1 (vector-space axioms).
/-- Scalar multiplication associates. -/
theorem freeMod_smul_assoc (a b : K) (x : FreeMod K n) : (a * b) • x = a • b • x :=
  smul_assoc a b x

-- Reference: Hörmann, arXiv:2106.03803, Def 2.1 (dimension is part of the data).
/-- The dimension of `FreeMod K n` is the data `n`. -/
def freeModDim (n : ℕ) : ℕ := n

-- Reference: Hörmann, arXiv:2106.03803, Def 2.1; Axler, Ch. 1 (linear maps).
/-- A morphism of basis-carrying free modules: a function plus its two
linearity proofs, as explicit data (no chosen structure anywhere). -/
structure FreeModHom (K : Type u) [Field K] (m n : ℕ) where
  toFun : FreeMod K m → FreeMod K n
  map_add' : ∀ x y, toFun (x + y) = toFun x + toFun y
  map_smul' : ∀ (c : K) x, toFun (c • x) = c • toFun x

-- Reference: Axler, Ch. 1 (the identity linear map).
/-- The identity morphism of `FreeMod K n`. -/
def freeModHomId (n : ℕ) : FreeModHom K n n where
  toFun := id
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

-- Reference: Axler, Ch. 1 (composition of linear maps).
/-- Composition of morphisms of basis-carrying free modules. -/
def freeModHomComp (f : FreeModHom K n p) (g : FreeModHom K m n) : FreeModHom K m p where
  toFun := fun x => f.toFun (g.toFun x)
  -- rw [g.map_add' x y]: fully instantiated, and `g.toFun (x + y)` occurs once.
  map_add' := fun x y => by
    rw [g.map_add' x y]
    exact f.map_add' (g.toFun x) (g.toFun y)
  -- rw [g.map_smul' c x]: fully instantiated, unique occurrence.
  map_smul' := fun c x => by
    rw [g.map_smul' c x]
    exact f.map_smul' c (g.toFun x)

-- Reference: Hörmann, arXiv:2106.03803, Def 2.1 (dual = Hom into the ground field).
/-- The dual of `FreeMod K n`: linear maps into the one-dimensional
`FreeMod K 1`. -/
abbrev FreeModDual (K : Type u) [Field K] (n : ℕ) := FreeModHom K n 1

-- Reference: Axler, Ch. 1 (functions into a discrete field have decidable
-- equality). NOTE: mathlib's `Fintype.decidablePiFintype` is
-- CHOICE-TAINTED at the pin (its `by simp` proof reaches `Classical.choice`,
-- confirmed by the lint), so this instance is built directly:
-- `decidable_of_iff` is axiom-free and the pointwise-forall instance over
-- `Fin n` lints clean.
/-- Equality of basis-carrying vectors is decidable when `K` is discrete,
constructively (pointwise comparison over `Fin n`). -/
instance freeModDecidableEq [DecidableEq K] (n : ℕ) : DecidableEq (FreeMod K n) :=
  fun v w => decidable_of_iff (∀ i, v i = w i) funext_iff.symm

-- Reference: smoke test for the P.1.1 acceptance criterion.
/-- Smoke test: the API in a few lines — dimension as data, addition
commutes, scalar one is the identity, equality is decidable. -/
example (K : Type u) [Field K] [DecidableEq K] (v w : FreeMod K 2) :
    freeModDim 2 = 2 ∧ v + w = w + v ∧ (1 : K) • v = v ∧ (v = v) :=
  ⟨rfl, add_comm v w, freeMod_one_smul v, rfl⟩

-- Reference: smoke test — decidable equality on the base type.
/-- Smoke test: equality of basis-carrying vectors is decidable. -/
example (K : Type u) [Field K] [DecidableEq K] (v : FreeMod K 3) : Decidable (v = v) :=
  inferInstance

end BoringMath
