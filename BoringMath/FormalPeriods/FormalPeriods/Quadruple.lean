/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Field.Basic
import BoringMath.FormalPeriods.FreeMod
import BoringMath.FormalPeriods.FormalPeriods.LinearAbelian
import BoringMath.FormalPeriods.FormalPeriods.BaseChange

/-!
# The fiber functor and the quadruple

`FiberFunctor A B R` (Hörmann's fiber functor into the basis-carrying
`FreeMod R (dim M)`, with the ℚ-linear/exact/faithful properties as `Prop`
fields) and `PeriodQuadruple A B K L` (the quadruple `(𝒜, H_B, H_dR, ∫)`
with `∫` an explicit natural isomorphism in bases).  Split out of
`BoringMath.FormalPeriods.FormalPeriods`.
-/

universe u

namespace BoringMath.FormalPeriods

open CategoryTheory

variable {B K L : Type u} [Field B] [Field K] [Field L] [Algebra B K] [Algebra K L]
variable {A : Type u} [Category A] [Preadditive A] [AbelianCat A]
variable [∀ X Y : A, Module B (X ⟶ Y)]
variable [LinearCat A B]
variable {m n : ℕ}

/-! ## The fiber functor and the quadruple -/

-- Reference: Axler, LADR 4th ed., Ch. 3 (injective = monic, surjective = epic
-- for linear maps between finite-dimensional spaces); Mac Lane, CWM, 2nd ed.,
-- Ch. VIII (exactness of a functor between abelian categories is equivalent to
-- preserving monomorphisms and epimorphisms).
/-- A morphism of basis-carrying free modules is monic iff its underlying
map is injective. -/
def IsMonoFreeModHom {R : Type u} [Field R] {m n : ℕ} (f : FreeModHom R m n) : Prop :=
  ∀ x y : FreeMod R m, f.toFun x = f.toFun y → x = y

-- Reference: Axler, LADR 4th ed., Ch. 3; Mac Lane, CWM, 2nd ed., Ch. VIII.
/-- A morphism of basis-carrying free modules is epic iff its underlying
map is surjective. -/
def IsEpiFreeModHom {R : Type u} [Field R] {m n : ℕ} (f : FreeModHom R m n) : Prop :=
  ∀ z : FreeMod R n, ∃ x : FreeMod R m, f.toFun x = z

-- Reference: Hörmann, arXiv:2106.03803, Def 2.1 (verified against the arXiv
-- HTML, v2): a fiber functor defined over `R` is a `B`-linear (Hörmann:
-- ℚ-linear), exact, faithful functor into f.d.-`R`-Vect; here into P.1's
-- basis-carrying spaces `FreeMod R (dim M)` — the dimension is data, and the
-- ℚ-linear/exact/faithful properties are carried as `Prop` fields (exactness
-- via the standard characterization in abelian categories: preserving
-- monomorphisms and epimorphisms — Mac Lane, CWM, 2nd ed., Ch. VIII).
/-- A fiber functor (Hörmann, Def 2.1) into the basis-carrying finite free
`R`-modules: on objects a dimension `dim M : ℕ` (the space is
`FreeMod R (dim M)`), on morphisms an explicit `FreeModHom`, with the functor
laws and the `B`-linear/exact/faithful properties as `Prop` fields. -/
structure FiberFunctor (A : Type u) [Category A] [Preadditive A]
    (B : Type u) [Field B] [∀ X Y : A, Module B (X ⟶ Y)]
    (R : Type u) [Field R] [Algebra B R] : Type u where
  dim : A → ℕ
  map : ∀ {M N : A}, (M ⟶ N) → FreeModHom R (dim M) (dim N)
  map_id : ∀ M : A, map (𝟙 M) = freeModHomId (dim M)
  map_comp : ∀ {M N P : A} (f : M ⟶ N) (g : N ⟶ P),
    map (f ≫ g) = freeModHomComp (map g) (map f)
  map_add : ∀ {M N : A} (f g : M ⟶ N), map (f + g) = map f + map g
  map_smul : ∀ {M N : A} (c : B) (f : M ⟶ N), map (c • f) = algebraMap B R c • map f
  faithful : ∀ {M N : A} (f g : M ⟶ N), map f = map g → f = g
  exact_mono : ∀ {M N : A} (f : M ⟶ N), Mono f → IsMonoFreeModHom (map f)
  exact_epi : ∀ {M N : A} (f : M ⟶ N), Epi f → IsEpiFreeModHom (map f)

-- Reference: Hörmann, arXiv:2106.03803, 2.2 (verified against the arXiv HTML,
-- v2): a quadruple `(𝒜, H_B, H_dR, ∫)` of a ℚ-linear abelian category with two
-- fiber functors over `B` (Hörmann's ℚ) and `K` (a subfield of `ℂ`), and a
-- natural isomorphism `∫ : H_B ⊗_B L ≅ H_dR ⊗_K L` (Hörmann: `L = ℂ`).  Since
-- the fiber functors land in basis-carrying spaces, base change to `L` keeps
-- the same dimension, and `∫_M` is the explicit matrix `int M : FreeModHom L
-- (hB.dim M) (hD.dim M)`; naturality is `intNat` and the inverse witnesses
-- `intInv` make `∫` an isomorphism.
/-- The formal-periods quadruple (Hörmann, arXiv:2106.03803, 2.2): an abelian
`B`-linear category `𝒜`, fiber functors `H_B` over `B` and `H_dR` over `K`, and
the comparison natural isomorphism `∫ : H_B ⊗_B L ≅ H_dR ⊗_K L` in bases
(`L` is Hörmann's `ℂ`). -/
structure PeriodQuadruple (A : Type u) [Category A] [Preadditive A] [AbelianCat A]
    (B : Type u) [Field B] [∀ X Y : A, Module B (X ⟶ Y)] [LinearCat A B]
    (K : Type u) [Field K] [Algebra B K]
    (L : Type u) [Field L] [Algebra K L] where
  hB : FiberFunctor A B B
  hD : FiberFunctor A B K
  int : ∀ M : A, FreeModHom L (hB.dim M) (hD.dim M)
  intNat : ∀ {M N : A} (α : M ⟶ N),
    freeModHomComp (int N) (baseChangeHomOf (algBL B K L) (hB.map α))
      = freeModHomComp (baseChangeHomOf (algebraMap K L) (hD.map α)) (int M)
  intInv : ∀ M : A, FreeModHom L (hD.dim M) (hB.dim M)
  intInvLeft : ∀ M : A,
    freeModHomComp (intInv M) (int M) = freeModHomId (hB.dim M)
  intInvRight : ∀ M : A,
    freeModHomComp (int M) (intInv M) = freeModHomId (hD.dim M)


end BoringMath.FormalPeriods
