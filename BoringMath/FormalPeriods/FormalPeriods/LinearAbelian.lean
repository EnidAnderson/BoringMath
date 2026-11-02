/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Field.Basic

/-!
# The `B`-linear abelian category, carried by typeclass hypotheses

`LinearCat A B` (Hörmann's ℚ-linear preadditive category) and `AbelianCat A`
(Mac Lane's abelian category, stated kernel-free to avoid the
`Classical.choice`-tainted `kernel`/`limit` family at the pin).  Split out
of `BoringMath.FormalPeriods.FormalPeriods`.
-/

universe u

namespace BoringMath.FormalPeriods

open CategoryTheory

/-! ## The ℚ-linear abelian category, carried by typeclass hypotheses -/

-- Reference: Hörmann, arXiv:2106.03803, Def 2.1 ("ℚ-linear" category: Hom sets
-- are ℚ-vector spaces and composition is ℚ-bilinear); Mac Lane, CWM, 2nd ed.,
-- Ch. VIII §1 (additive category = preadditive).  The base field is the variable
-- `B` (Hörmann's ℚ) because `Rat.instField` is choice-tainted at the pin.
/-- A `B`-linear (Hörmann: ℚ-linear) preadditive category: every Hom set is a
`B`-module and composition is `B`-bilinear. -/
class LinearCat (A : Type u) [Category A] [Preadditive A]
    (B : Type u) [Field B] [∀ X Y : A, Module B (X ⟶ Y)] : Prop where
  comp_smul_left : ∀ {X Y Z : A} (c : B) (f : X ⟶ Y) (g : Y ⟶ Z),
    (c • f) ≫ g = c • (f ≫ g)
  comp_smul_right : ∀ {X Y Z : A} (c : B) (f : X ⟶ Y) (g : Y ⟶ Z),
    f ≫ (c • g) = c • (f ≫ g)

-- Reference: Mac Lane, CWM, 2nd ed., Ch. VIII §1 (definition of an abelian
-- category), stated kernel-free: a kernel of `f` is a morphism `k` with
-- `k ≫ f = 0` through which every `g` with `g ≫ f = 0` factors uniquely — this
-- avoids the `kernel`/`HasLimit` names, which are `Classical.choice`-tainted at
-- the pin (P.0.4 pin-run census).
/-- An abelian category, in the kernel-free formulation of Mac Lane, CWM,
2nd ed., Ch. VIII §1: a preadditive category where every morphism has a kernel
and a cokernel (via their universal properties), every monomorphism is a
kernel and every epimorphism is a cokernel. -/
class AbelianCat (A : Type u) [Category A] [Preadditive A] : Prop where
  has_kernel : ∀ {X Y : A} (f : X ⟶ Y), ∃ (K : A) (k : K ⟶ X),
    (k ≫ f = 0) ∧ ∀ {Z : A} (g : Z ⟶ X), g ≫ f = 0 → ∃! h : Z ⟶ K, h ≫ k = g
  has_cokernel : ∀ {X Y : A} (f : X ⟶ Y), ∃ (C : A) (p : Y ⟶ C),
    (f ≫ p = 0) ∧ ∀ {Z : A} (g : Y ⟶ Z), f ≫ g = 0 → ∃! h : C ⟶ Z, p ≫ h = g
  mono_is_kernel : ∀ {X Y : A} (m : X ⟶ Y), Mono m →
    ∃ (Q : A) (p : Y ⟶ Q), (m ≫ p = 0) ∧
      ∀ {Z : A} (g : Z ⟶ Y), g ≫ p = 0 → ∃! h : Z ⟶ X, h ≫ m = g
  epi_is_cokernel : ∀ {X Y : A} (e : X ⟶ Y), Epi e →
    ∃ (Q : A) (k : Q ⟶ X), (k ≫ e = 0) ∧
      ∀ {Z : A} (g : X ⟶ Z), k ≫ g = 0 → ∃! h : Y ⟶ Z, e ≫ h = g

end BoringMath.FormalPeriods
