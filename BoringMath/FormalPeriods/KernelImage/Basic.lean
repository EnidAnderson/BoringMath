/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Group.Action.Defs
import BoringMath.FormalPeriods.FreeMod
import BoringMath.FormalPeriods.RowReduction

/-!
# Standard basis, matrix of a hom, matrix–vector product (P.2.2, part 1)

Piece 1 of `BoringMath.FormalPeriods.KernelImage`: the standard basis
`stdBasisVec` of `FreeMod K m`, the matrix `freeModHomMat` of a
`FreeModHom`, and the matrix–vector product `applyMat` as an explicit
`List.sum`, with their definitional peels.
-/

universe u

namespace BoringMath

variable {K : Type u} [Field K] {m n : ℕ}

/-! ## Standard basis, matrix of a hom, matrix–vector product -/

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6 (the standard
-- basis of the coordinate module `Fin m → K`).
/-- The `j`-th standard basis vector of `FreeMod K m`: `1` at `j`, `0`
elsewhere. -/
def stdBasisVec (j : Fin m) : FreeMod K m := fun i => if i = j then 1 else 0

-- Reference: definitional peel of `stdBasisVec`.
/-- Pointwise unfolding of `stdBasisVec`. -/
theorem stdBasisVec_apply (j i : Fin m) :
    stdBasisVec j i = (if i = j then (1 : K) else (0 : K)) :=
  rfl

-- Reference: definitional peel of `stdBasisVec` at `i = j`.
/-- The standard basis vector has entry `1` at its own index. -/
theorem stdBasisVec_self (j : Fin m) : stdBasisVec j j = (1 : K) :=
  ite_eq_left rfl

-- Reference: definitional peel of `stdBasisVec` at `i ≠ j`.
/-- The standard basis vector has entry `0` off its own index. -/
theorem stdBasisVec_ne (j i : Fin m) (h : i ≠ j) : stdBasisVec j i = (0 : K) :=
  ite_eq_right h

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6 (the matrix of a
-- linear map in the standard basis: column `j` is the image of `e_j`).
/-- The matrix of a morphism `f : FreeModHom K m n` in the standard bases:
entry `(i, j)` is the `i`-th coordinate of `f (e_j)`. -/
def freeModHomMat (f : FreeModHom K m n) : FreeMatrix K n m :=
  fun i j => f.toFun (stdBasisVec j) i

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6 (matrix–vector
-- product `A x`, computed as a `List.sum` over `finRange m`; the `Finset`
-- sum API is choice-tainted at the pin, see the module doc).
/-- Matrix–vector product: `(A x) i = ∑_j A i j * x j`, as an explicit
`List.sum` over the columns. -/
def applyMat (A : FreeMatrix K n m) (x : FreeMod K m) : FreeMod K n :=
  fun i => ((List.finRange m).map (fun j => A i j * x j)).sum

-- Reference: definitional peel of `applyMat`.
/-- Pointwise unfolding of `applyMat`. -/
theorem applyMat_apply (A : FreeMatrix K n m) (x : FreeMod K m) (i : Fin n) :
    applyMat A x i = ((List.finRange m).map (fun j => A i j * x j)).sum :=
  rfl

-- Reference: definitional peel of `applyMat` (same anchor as
-- `applyMat_apply`); the pointwise sum form used by every row-operation peel.
/-- Matrix–vector product at a row is the explicit column sum of
row-times-vector entries. -/
theorem applyMat_eq_listSum (A : FreeMatrix K n m) (x : FreeMod K m) (a : Fin n) :
    applyMat A x a = ((List.finRange m).map (fun j => A a j * x j)).sum :=
  rfl

end BoringMath
