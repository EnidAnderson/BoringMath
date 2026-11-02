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
# Pivot columns and kernel/image data of an RREF matrix (P.2.2, part 2)

Piece 2 of `BoringMath.FormalPeriods.KernelImage`: the boolean zero-row
and pivot tests, `pivotRowOfCol`, the kernel basis vectors `kernelVec`
with their peels, and the `pivotCols`/`nonPivotCols`/`kernelBasis`/
`imageBasis` lists with the `rankOf`/`nullityOf` counts.
-/

universe u

namespace BoringMath

variable {K : Type u} [Field K] {m n : ℕ}

/-! ## Pivot columns and the kernel/image data of an RREF matrix -/

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6 (decidable zero-row
-- test, built directly on `List.all` — no choice-tainted instance).
/-- Boolean zero-row test for row `a` of `R`. -/
def rowIsZeroBool [DecidableEq K] (R : FreeMatrix K n m) (a : Fin n) : Bool :=
  ((List.finRange m).all (fun c => Decidable.decide (R a c = 0)))

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6; the landed pivot
-- search `findPivotRow` (RowReduction.lean).
/-- The pivot row of column `c` in an RREF matrix `R`: the first row whose
leading column is `c`, if any. -/
def pivotRowOfCol [DecidableEq K] (R : FreeMatrix K n m) (c : Fin m) : Option (Fin n) :=
  findPivotRow (fun a => Decidable.decide (matLeadingCol R a = c.val)) n 0

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6 (pivot columns).
/-- Boolean pivot-column test: column `c` is a pivot column of `R` iff some
row has leading column `c`. -/
def pivotColBool [DecidableEq K] (R : FreeMatrix K n m) (c : Fin m) : Bool :=
  (pivotRowOfCol R c).isSome

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6 (the solution-space
-- basis vector attached to a non-pivot column `c` of the RREF: entry `1` at
-- `c`, entry `-R a c` at the pivot column of each row `a`, else `0`).
/-- The kernel basis vector of the RREF matrix `R` attached to the column
`c`: entry `1` at `c`, entry `-R a c` at the pivot column of row `a`, and
`0` at every other non-pivot column. -/
def kernelVec [DecidableEq K] (R : FreeMatrix K n m) (c : Fin m) : FreeMod K m :=
  fun j => if j = c then 1 else
    match pivotRowOfCol R j with
    | some a => -(R a c)
    | none => 0

-- Reference: definitional peel of `kernelVec` at `j = c`.
/-- The kernel basis vector has entry `1` at its own column `c`. -/
theorem kernelVec_self [DecidableEq K] (R : FreeMatrix K n m) (c : Fin m) :
    kernelVec R c c = (1 : K) :=
  ite_eq_left rfl

-- Reference: definitional peel of `kernelVec` at a pivot column `j ≠ c`.
/-- At a pivot column `j ≠ c` owned by row `a`, the kernel basis vector has
entry `-R a c`. -/
theorem kernelVec_pivot [DecidableEq K] (R : FreeMatrix K n m) (c j : Fin m) (h : j ≠ c)
    (a : Fin n) (hp : pivotRowOfCol R j = some a) :
    kernelVec R c j = -(R a c) := by
  unfold kernelVec
  exact Eq.trans (ite_eq_right h)
    (Eq.trans (congrArg (fun p => match p with | some b => -(R b c) | none => (0 : K)) hp)
      rfl)

-- Reference: definitional peel of `kernelVec` at a non-pivot column `j ≠ c`.
/-- At a non-pivot column `j ≠ c`, the kernel basis vector has entry `0`. -/
theorem kernelVec_other [DecidableEq K] (R : FreeMatrix K n m) (c j : Fin m) (h : j ≠ c)
    (hp : pivotRowOfCol R j = none) :
    kernelVec R c j = (0 : K) := by
  unfold kernelVec
  exact Eq.trans (ite_eq_right h)
    (Eq.trans (congrArg (fun p => match p with | some b => -(R b c) | none => (0 : K)) hp)
      rfl)

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6 (pivot columns of
-- the RREF, in increasing order).
/-- The pivot columns of `R`, as an explicit list (a sublist of
`List.finRange m`, hence increasing). -/
def pivotCols [DecidableEq K] (R : FreeMatrix K n m) : List (Fin m) :=
  (List.finRange m).filter (pivotColBool R)

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6 (free columns of
-- the RREF: the non-pivot columns carry the kernel basis).
/-- The non-pivot columns of `R`, as an explicit list. -/
def nonPivotCols [DecidableEq K] (R : FreeMatrix K n m) : List (Fin m) :=
  (List.finRange m).filter (fun c => !(pivotColBool R c))

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6 (the kernel basis
-- is indexed by the non-pivot columns).
/-- The kernel basis of the RREF matrix `R`: `kernelVec R c` for each
non-pivot column `c`. -/
def kernelBasis [DecidableEq K] (R : FreeMatrix K n m) : List (FreeMod K m) :=
  (nonPivotCols R).map (kernelVec R)

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6 (the image is
-- spanned by the pivot columns of the *original* matrix; row reduction
-- preserves column relations).
/-- The image basis: the columns of the original matrix `A` at the pivot
columns of its RREF `R`. -/
def imageBasis [DecidableEq K] (A : FreeMatrix K n m) (R : FreeMatrix K n m) : List (FreeMod K n) :=
  (pivotCols R).map (fun c => fun i => A i c)

-- Reference: Hörmann, arXiv:2106.03803, Def. 3.1 / Remark 3.3 (the dimension
-- is computed data); Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6 (rank =
-- number of pivots).
/-- The rank of the matrix `R` in RREF: the number of pivot columns. -/
def rankOf [DecidableEq K] (R : FreeMatrix K n m) : ℕ := (pivotCols R).length

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6 (nullity = number of
-- free columns).
/-- The nullity: the number of kernel basis vectors, i.e. of non-pivot
columns of `R`. -/
def nullityOf [DecidableEq K] (R : FreeMatrix K n m) : ℕ := (kernelBasis R).length

end BoringMath
