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
import BoringMath.FormalPeriods.KernelImage.Basic
import BoringMath.FormalPeriods.KernelImage.ListSum

/-!
# Matrix of a hom and the matrix–vector product (P.2.2, part 4)

Piece 4 of `BoringMath.FormalPeriods.KernelImage`: every vector is an
explicit `List.sum` of scaled standard basis vectors, so
`f x = applyMat (freeModHomMat f) x`.
-/

universe u

namespace BoringMath

variable {K : Type u} [Field K] {m n : ℕ}

/-! ## The matrix of a hom and the matrix–vector product -/

-- Reference: Axler, Ch. 1 (a linear map kills zero); from `map_smul'` at
-- scalar `0`.
/-- A morphism of free modules sends zero to zero. -/
theorem freeModHom_map_zero (f : FreeModHom K m n) : f.toFun 0 = 0 := by
  have h : f.toFun (0 + 0) = f.toFun 0 + f.toFun 0 := f.map_add' (0 : FreeMod K m) 0
  have hz : (0 : FreeMod K m) + 0 = 0 := zero_add 0
  have h1 : f.toFun (0 + 0) = f.toFun 0 := congrArg f.toFun hz
  have h' : f.toFun 0 = f.toFun 0 + f.toFun 0 := Eq.trans h1.symm h
  have haz : f.toFun 0 + 0 = f.toFun 0 := add_zero (f.toFun 0)
  exact add_left_cancel (Eq.trans h'.symm haz.symm)

-- Reference: Axler, Ch. 1 (linear maps commute with finite sums); by
-- structural induction on the index list.
/-- A morphism of free modules commutes with a list sum of vectors. -/
theorem freeModHom_map_listSum (f : FreeModHom K m n) (l : List (Fin m))
    (g : Fin m → FreeMod K m) :
    f.toFun ((l.map g).sum) = (l.map (fun j => f.toFun (g j))).sum := by
  induction l with
  | nil => exact freeModHom_map_zero f
  | cons a l ih =>
      exact Eq.trans (f.map_add' (g a) ((l.map g).sum)) (congrArg (fun t => f.toFun (g a) + t) ih)

-- Reference: definitional peel of the standard-basis component at `i = j`
-- (same anchor as `eq_listSum_stdBasisVec`).
/-- The `i`-th component of `x j • stdBasisVec j` is `x j` when `i = j`. -/
theorem smul_stdBasisVec_apply_eq (x : FreeMod K m) (j i : Fin m) (hij : i = j) :
    (x j • stdBasisVec j) i = x j := by
  have hij' : j = i := hij.symm
  subst hij'
  have hsmul : (x j • stdBasisVec j) j = x j • (stdBasisVec j j : K) :=
    Pi.smul_apply (x j) (stdBasisVec j) j
  have hself : stdBasisVec j j = (1 : K) := stdBasisVec_self j
  have h1 : x j • (stdBasisVec j j : K) = x j • (1 : K) := congrArg (fun t => x j • t) hself
  have h2 : x j • (1 : K) = x j * (1 : K) := smul_eq_mul (x j) (1 : K)
  have h3 : x j * (1 : K) = x j := mul_one (x j)
  exact Eq.trans hsmul (Eq.trans h1 (Eq.trans h2 h3))
-- Reference: definitional peel of the standard-basis component at `i ≠ j`
-- (same anchor as `eq_listSum_stdBasisVec`).
/-- The `i`-th component of `x j • stdBasisVec j` is `0` when `i ≠ j`. -/
theorem smul_stdBasisVec_apply_ne (x : FreeMod K m) (j i : Fin m) (hij : i ≠ j) :
    (x j • stdBasisVec j) i = (0 : K) := by
  have hsmul : (x j • stdBasisVec j) i = x j • (stdBasisVec j i : K) :=
    Pi.smul_apply (x j) (stdBasisVec j) i
  have hne : stdBasisVec j i = (0 : K) := stdBasisVec_ne j i hij
  have h1 : x j • (stdBasisVec j i : K) = x j • (0 : K) := congrArg (fun t => x j • t) hne
  have h2 : x j • (0 : K) = x j * (0 : K) := smul_eq_mul (x j) (0 : K)
  have h3 : x j * (0 : K) = (0 : K) := mul_zero (x j)
  exact Eq.trans hsmul (Eq.trans h1 (Eq.trans h2 h3))
-- Reference: definitional peel of the standard-basis component (same anchor
-- as `eq_listSum_stdBasisVec`).
/-- The `i`-th component of `x j • stdBasisVec j` is the `ite` at `i = j`. -/
theorem smul_stdBasisVec_apply (x : FreeMod K m) (j i : Fin m) :
    (x j • stdBasisVec j) i = (if i = j then x j else 0) := by
  cases (inferInstance : Decidable (i = j)) with
  | isTrue hij => exact Eq.trans (smul_stdBasisVec_apply_eq x j i hij) (ite_eq_left hij).symm
  | isFalse hij => exact Eq.trans (smul_stdBasisVec_apply_ne x j i hij) (ite_eq_right hij).symm

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6 (every vector is
-- the sum of its standard-basis components); proved pointwise via the
-- `ite`-sum peels on `List.finRange m` (nodup).
/-- Every vector of `FreeMod K m` is the explicit sum of its standard-basis
components. -/
theorem eq_listSum_stdBasisVec (x : FreeMod K m) :
    x = ((List.finRange m).map (fun j => x j • stdBasisVec j)).sum := by
  have h : (((List.finRange m).map (fun j => x j • stdBasisVec j)).sum : FreeMod K m) = x := by
    funext i
    exact Eq.trans (list_sum_map_apply (List.finRange m) (fun j => x j • stdBasisVec j) i)
      (Eq.trans (congrArg (fun F => ((List.finRange m).map F).sum)
          (funext (fun j => smul_stdBasisVec_apply x j i)))
        (list_sum_ite_eq_of_mem_nodup (List.finRange m) (List.nodup_finRange m) x i
          (List.mem_finRange i)))
  exact h.symm

-- Reference: Axler, Ch. 1 (linear maps commute with scalars); Mines–Richman–
-- Ruitenburg 1988, Pt. II Ch. 6 (matrix entries); same anchor as
-- `freeModHom_apply_eq_applyMat`.
/-- Pointwise: `f (x j • e_j)` at `i` is the matrix entry `(i, j)` times `x j`. -/
theorem freeModHom_smul_stdBasisVec_apply (f : FreeModHom K m n) (x : FreeMod K m)
    (j : Fin m) (i : Fin n) :
    f.toFun (x j • stdBasisVec j) i = freeModHomMat f i j * x j :=
  Eq.trans (congrFun (f.map_smul' (x j) (stdBasisVec j)) i)
    (Eq.trans (Pi.smul_apply (x j) (f.toFun (stdBasisVec j)) i)
      (mul_comm (x j) (f.toFun (stdBasisVec j) i)))

-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6 (a linear map is
-- its matrix: `f x = A x` with `A` the matrix of `f`); assembled from
-- `eq_listSum_stdBasisVec`, `freeModHom_listSum` and `map_smul'`.
/-- The morphism `f` equals matrix–vector product with its matrix. -/
theorem freeModHom_apply_eq_applyMat (f : FreeModHom K m n) (x : FreeMod K m) :
    f.toFun x = applyMat (freeModHomMat f) x := by
  funext i
  exact Eq.trans (congrFun (congrArg f.toFun (eq_listSum_stdBasisVec x)) i)
    (Eq.trans
      (congrFun (freeModHom_map_listSum f (List.finRange m) (fun j => x j • stdBasisVec j)) i)
      (Eq.trans (list_sum_map_apply (List.finRange m) (fun j => f.toFun (x j • stdBasisVec j)) i)
        (list_sum_map_congr_mem (List.finRange m)
          (fun j _ => freeModHom_smul_stdBasisVec_apply f x j i))))

end BoringMath
