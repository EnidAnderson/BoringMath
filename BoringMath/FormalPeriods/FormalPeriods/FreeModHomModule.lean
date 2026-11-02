/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Field.Basic
import BoringMath.FormalPeriods.FreeMod
import BoringMath.FormalPeriods.FormalPeriods.FinSum

/-!
# Pointwise module structure on `FreeModHom`

Zero, addition, and `K`- resp. `B`-scalar multiplication on morphisms of
basis-carrying free modules, defined pointwise, plus the standard-basis
expansion `freeModEqSumSingle` and commutation with finite sums.  Split out
of `BoringMath.FormalPeriods.FormalPeriods`.
-/

universe u

namespace BoringMath.FormalPeriods

variable {B K L : Type u} [Field B] [Field K] [Field L] [Algebra B K] [Algebra K L]
variable {m n : ℕ}

/-! ## Pointwise module structure on `FreeModHom` -/

-- Reference: Axler, LADR 4th ed., Ch. 1 (linear maps form a vector space:
-- pointwise operations); Hörmann, arXiv:2106.03803, Def 2.1 (the target category
-- of a fiber functor is f.d.-K-Vect, so its Hom sets carry the pointwise
-- module structure).
/-- The zero linear map between basis-carrying free modules. -/
instance freeModHomZeroInst : Zero (FreeModHom K m n) :=
  ⟨⟨fun _ => 0, fun _ _ => (add_zero (0 : FreeMod K n)).symm,
    fun c _ => (smul_zero c).symm⟩⟩

-- Reference: line 273 (freeModHomAddInst, map_add' field: `rw [f.map_add' x y, g.map_add' x y]`).
/-- Peel: pointwise addition unfolds both homs on `x + y`. -/
theorem freeModHomAddMapAdd (f g : FreeModHom K m n) (x y : FreeMod K m) :
    f.toFun (x + y) + g.toFun (x + y)
      = (f.toFun x + g.toFun x) + (f.toFun y + g.toFun y) :=
  Eq.trans (congrArg (fun w => w + g.toFun (x + y)) (f.map_add' x y))
    (Eq.trans (congrArg (fun w => (f.toFun x + f.toFun y) + w) (g.map_add' x y))
      (add_add_add_comm (f.toFun x) (f.toFun y) (g.toFun x) (g.toFun y)))

-- Reference: line 277 (freeModHomAddInst, map_smul' field: `rw [f.map_smul' c x, g.map_smul' c x]`).
/-- Peel: pointwise addition unfolds both homs on `c • x`. -/
theorem freeModHomAddMapSmul (f g : FreeModHom K m n) (c : K) (x : FreeMod K m) :
    f.toFun (c • x) + g.toFun (c • x) = c • (f.toFun x + g.toFun x) :=
  Eq.trans (congrArg (fun w => w + g.toFun (c • x)) (f.map_smul' c x))
    (Eq.trans (congrArg (fun w => c • f.toFun x + w) (g.map_smul' c x))
      (smul_add c (f.toFun x) (g.toFun x)).symm)

-- Reference: line 288 (freeModHomSMulKInst, map_add' field: `rw [f.map_add' x y]`).
/-- Peel: pointwise `K`-scaling unfolds `f` on `x + y`. -/
theorem freeModHomSmulKMapAdd (c : K) (f : FreeModHom K m n) (x y : FreeMod K m) :
    c • f.toFun (x + y) = c • f.toFun x + c • f.toFun y :=
  Eq.trans (congrArg (fun w => c • w) (f.map_add' x y)) (smul_add c (f.toFun x) (f.toFun y))

-- Reference: line 292 (freeModHomSMulKInst, map_smul' field: `rw [f.map_smul' d x]`).
/-- Peel: pointwise `K`-scaling unfolds `f` on `d • x`. -/
theorem freeModHomSmulKMapSmul (c d : K) (f : FreeModHom K m n) (x : FreeMod K m) :
    c • f.toFun (d • x) = d • (c • f.toFun x) :=
  Eq.trans (congrArg (fun w => c • w) (f.map_smul' d x)) (smul_comm c d (f.toFun x))

-- Reference: line 304 (freeModHomSMulBInst, map_add' field: `rw [f.map_add' x y]`).
/-- Peel: pointwise `B`-scaling unfolds `f` on `x + y`. -/
theorem freeModHomSmulBMapAdd (c : B) (f : FreeModHom K m n) (x y : FreeMod K m) :
    algebraMap B K c • f.toFun (x + y)
      = algebraMap B K c • f.toFun x + algebraMap B K c • f.toFun y :=
  Eq.trans (congrArg (fun w => algebraMap B K c • w) (f.map_add' x y))
    (smul_add (algebraMap B K c) (f.toFun x) (f.toFun y))

-- Reference: line 308 (freeModHomSMulBInst, map_smul' field: `rw [f.map_smul' d x]`).
/-- Peel: pointwise `B`-scaling unfolds `f` on `d • x`. -/
theorem freeModHomSmulBMapSmul (c : B) (d : K) (f : FreeModHom K m n) (x : FreeMod K m) :
    algebraMap B K c • f.toFun (d • x) = d • (algebraMap B K c • f.toFun x) :=
  Eq.trans (congrArg (fun w => algebraMap B K c • w) (f.map_smul' d x))
    (smul_comm (algebraMap B K c) d (f.toFun x))

-- Reference: Axler, LADR 4th ed., Ch. 1 (sum of linear maps, pointwise).
/-- Pointwise addition of morphisms of basis-carrying free modules. -/
instance freeModHomAddInst : Add (FreeModHom K m n) :=
  ⟨fun f g => ⟨fun x => f.toFun x + g.toFun x,
    fun x y => freeModHomAddMapAdd f g x y,
    fun c x => freeModHomAddMapSmul f g c x⟩⟩

-- Reference: Axler, LADR 4th ed., Ch. 1 (scalar multiple of a linear map,
-- pointwise).
/-- Pointwise scalar multiplication of morphisms of basis-carrying free
modules by a scalar of `K`. -/
instance freeModHomSMulKInst : SMul K (FreeModHom K m n) :=
  ⟨fun c f => ⟨fun x => c • f.toFun x,
    fun x y => freeModHomSmulKMapAdd c f x y,
    fun d x => freeModHomSmulKMapSmul c d f x⟩⟩

-- Reference: Hörmann, arXiv:2106.03803, Def 2.1 (a fiber functor over `K` is
-- ℚ-linear, i.e. `B`-linear for the base field `B` embedded in `K`); Axler,
-- LADR 4th ed., Ch. 1 (restriction of scalars along `B → K`).
/-- Pointwise scalar multiplication of morphisms of basis-carrying free
`K`-modules by a scalar of the base field `B` (via `algebraMap B K`). -/
instance freeModHomSMulBInst : SMul B (FreeModHom K m n) :=
  ⟨fun c f => ⟨fun x => algebraMap B K c • f.toFun x,
    fun x y => freeModHomSmulBMapAdd c f x y,
    fun d x => freeModHomSmulBMapSmul c d f x⟩⟩

-- Reference: Axler, LADR 4th ed., Ch. 1 (a linear map kills zero); the proof
-- mirrors `TensorBilMap.map_zero_left` in `BoringMath.FormalPeriods.FreeTensor`.
/-- A morphism of basis-carrying free modules sends `0` to `0`. -/
theorem freeModHomMapZero (f : FreeModHom K m n) : f.toFun 0 = 0 :=
  Eq.trans (congrArg f.toFun (zero_smul K (0 : FreeMod K m)).symm)
    (Eq.trans (f.map_smul' (0 : K) 0) (zero_smul K (f.toFun 0)))

-- Reference: definitional peel of `Pi.single` — primitive definitional lemma.
/-- Pointwise unfolding of `Pi.single`. -/
theorem piSingleApply {K : Type u} [Field K] {n : ℕ} (i j : Fin n) (a : K) :
    (Pi.single i a : Fin n → K) j = if j = i then a else (0 : K) := Pi.single_apply i a j

-- Reference: line 334 (freeModEqSumSingle, inner pointwise step).
/-- Peel: `(x • eᵢ) j = if j = i then x else 0`. -/
theorem smulSingleApply {K : Type u} [Field K] {n : ℕ} (x : K) (i j : Fin n) :
    (x • Pi.single i (1 : K)) j = if j = i then x else 0 := by
  cases (inferInstance : Decidable (j = i)) with
  | isTrue h =>
      exact Eq.trans (Pi.smul_apply x (Pi.single (M := fun _ => K) i (1 : K)) j)
        (Eq.trans (smul_eq_mul x (Pi.single (M := fun _ => K) i (1 : K) j))
          (Eq.trans (congrArg (fun w : K => x * w)
              (Eq.trans (congrArg (Pi.single (M := fun _ => K) i (1 : K)) h)
                (Pi.single_eq_same (M := fun _ => K) i (1 : K))))
            (Eq.trans (mul_one x) (ite_eq_left h).symm)))
  | isFalse h =>
      exact Eq.trans (Pi.smul_apply x (Pi.single (M := fun _ => K) i (1 : K)) j)
        (Eq.trans (smul_eq_mul x (Pi.single (M := fun _ => K) i (1 : K) j))
          (Eq.trans (congrArg (fun w : K => x * w)
              (Pi.single_eq_of_ne (M := fun _ => K) h (1 : K)))
            (Eq.trans (mul_zero x) (ite_eq_right h).symm)))

-- Reference: line 325-327 (freeModEqSumSingle, the `h1` step via `listSum_apply`).
/-- Peel: the applied sum equals the sum of the applied summands. -/
theorem finSumSingleApplyEq {K : Type u} [Field K] {n : ℕ} (x : FreeMod K n) (j : Fin n) :
    (((List.finRange n).map (fun i => x i • Pi.single i (1 : K))).sum) j
      = ((List.finRange n).map (fun i => (x i • Pi.single i (1 : K)) j)).sum :=
  listSum_apply (List.finRange n) (fun i => x i • Pi.single i 1) j

-- Reference: line 331-335 (freeModEqSumSingle, the `listSum_congr` step).
/-- Peel: the applied summands equal the `ite` summands. -/
theorem finSumSingleApplyCongr {K : Type u} [Field K] {n : ℕ} (x : FreeMod K n) (j : Fin n) :
    ((List.finRange n).map (fun i => (x i • Pi.single i (1 : K)) j)).sum
      = ((List.finRange n).map (fun i => if j = i then x i else 0)).sum :=
  listSum_congr (List.finRange n) (fun i => (x i • Pi.single i (1 : K)) j)
    (fun i => if j = i then x i else 0) (fun i => smulSingleApply (x i) i j)

-- Reference: line 336 (freeModEqSumSingle, the final `listSum_ite_mem` step).
/-- Peel: the pointwise basis expansion of `x`. -/
theorem freeModEqSumSinglePoint {K : Type u} [Field K] {n : ℕ} (x : FreeMod K n) (j : Fin n) :
    x j = (((List.finRange n).map (fun i => x i • Pi.single i (1 : K))).sum) j :=
  Eq.trans
    (listSum_ite_mem (List.finRange n) (List.nodup_finRange n) j x (List.mem_finRange j)).symm
    (Eq.trans (finSumSingleApplyCongr x j).symm (finSumSingleApplyEq x j).symm)

-- Reference: Axler, LADR 4th ed., Ch. 2 (the standard basis of `F^n`: every
-- vector is the linear combination `∑ i, x i • eᵢ` of the standard basis).
/-- Basis expansion in the standard basis: `x = ∑ i, x i • eᵢ` in `FreeMod K n`. -/
theorem freeModEqSumSingle {K : Type u} [Field K] {n : ℕ} (x : FreeMod K n) :
    x = finSum n (fun i => x i • Pi.single i 1) := by
  funext j
  unfold finSum
  exact freeModEqSumSinglePoint x j


-- Reference: Axler, LADR 4th ed., Ch. 1 (linearity extends to finite sums);
-- proved by hand by `List` induction (`freeModHomMapListSum`).
/-- A morphism of basis-carrying free modules commutes with list sums. -/
theorem freeModHomMapListSum (f : FreeModHom K m n) (k : ℕ) (g : Fin k → FreeMod K m)
    (l : List (Fin k)) :
    f.toFun ((l.map g).sum) = (l.map (fun i => f.toFun (g i))).sum := by
  induction l with
  | nil =>
      exact Eq.trans (congrArg f.toFun (listMapNilSum g))
        (Eq.trans (freeModHomMapZero f) (listMapNilSum (fun i => f.toFun (g i))).symm)
  | cons a l ih =>
      exact Eq.trans (congrArg f.toFun (listMapConsSum g a l))
        (Eq.trans (f.map_add' (g a) ((l.map g).sum))
          (Eq.trans (congrArg (fun w => f.toFun (g a) + w) ih)
            (listMapConsSum (fun i => f.toFun (g i)) a l).symm))

-- Reference: Axler, LADR 4th ed., Ch. 1 (linearity extends to finite sums).
/-- A morphism of basis-carrying free modules commutes with finite sums. -/
theorem freeModHomMapSum (f : FreeModHom K m n) (k : ℕ) (g : Fin k → FreeMod K m) :
    f.toFun (finSum k g) = finSum k (fun i => f.toFun (g i)) :=
  freeModHomMapListSum f k g (List.finRange k)


end BoringMath.FormalPeriods
