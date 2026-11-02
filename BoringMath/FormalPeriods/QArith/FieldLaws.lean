/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/

import Mathlib.Init
import BoringMath.FormalPeriods.QArith.Normalize
import BoringMath.FormalPeriods.QArith.Ops
import BoringMath.FormalPeriods.QArith.CrossEq

/-!
# The field laws, part 1: commutativity, units, additive inverse (`QArith`)

Piece 5 of `BoringMath.FormalPeriods.QArith`: `qadd_comm`, `qmul_comm`,
`qadd_zero`, `qmul_one`, and `qadd_left_neg`.
-/

namespace BoringMath

/-! ### The field laws -/

-- Reference: [MRR], ch. on fields (commutativity of addition).
/-- `qadd` is commutative. -/
theorem qadd_comm (a b : Rat) : qadd a b = qadd b a := by
  unfold qadd
  refine (qmk_eq_iff _ _ (qden_mul a b) _ _ (qden_mul b a)).2 ?_
  exact Eq.mpr (Eq.trans
    (congrArg (fun x : Int => x * ↑(b.den * a.den) =
      (b.num * ↑a.den + a.num * ↑b.den) * ↑(a.den * b.den))
      (Int.add_comm (a.num * ↑b.den) (b.num * ↑a.den)))
    (congrArg (fun z : Nat => (b.num * ↑a.den + a.num * ↑b.den) * ↑(b.den * a.den) =
      (b.num * ↑a.den + a.num * ↑b.den) * ↑z) (Nat.mul_comm a.den b.den))) rfl

-- Reference: [MRR], ch. on fields (commutativity of multiplication).
/-- `qmul` is commutative. -/
theorem qmul_comm (a b : Rat) : qmul a b = qmul b a := by
  unfold qmul
  refine (qmk_eq_iff _ _ (qden_mul a b) _ _ (qden_mul b a)).2 ?_
  exact Eq.mpr (Eq.trans
    (congrArg (fun x : Int => x * ↑(b.den * a.den) = (b.num * a.num) * ↑(a.den * b.den))
      (Int.mul_comm a.num b.num))
    (congrArg (fun z : Nat => (b.num * a.num) * ↑(b.den * a.den) = (b.num * a.num) * ↑z)
      (Nat.mul_comm a.den b.den))) rfl

-- Reference: [MRR], ch. on fields (zero is a right unit of addition).
/-- `qadd a 0 = a`. -/
theorem qadd_zero (a : Rat) : qadd a 0 = a := by
  have e1 : qadd a 0 = qmk a.num a.den a.den_nz := by
    unfold qadd
    exact qmk_congr _ _ (qden_mul a 0) _ _ a.den_nz
      (Eq.trans
        (congrArg (fun x : Int => a.num * x + (0 : Rat).num * ↑a.den) (congrArg (fun y : Nat => (y : Int)) Rat.zero_den))
        (Eq.trans (congrArg (fun x : Int => a.num * x + (0 : Rat).num * ↑a.den) Int.natCast_one)
          (Eq.trans (congrArg (fun x : Int => x + (0 : Rat).num * ↑a.den) (Int.mul_one a.num))
            (Eq.trans (congrArg (fun x : Int => a.num + x * ↑a.den) Rat.zero_num)
              (Eq.trans (congrArg (fun x : Int => a.num + x) (Int.zero_mul (↑a.den)))
                (Int.add_zero a.num))))))
      (Eq.trans (congrArg (fun x : Nat => a.den * x) Rat.zero_den) (Nat.mul_one a.den))
  exact Eq.trans e1 (qmk_self a)

-- Reference: [MRR], ch. on fields (one is a right unit of multiplication).
/-- `qmul a 1 = a`. -/
theorem qmul_one (a : Rat) : qmul a 1 = a := by
  have e1 : qmul a 1 = qmk a.num a.den a.den_nz := by
    unfold qmul
    exact qmk_congr _ _ (qden_mul a 1) _ _ a.den_nz
      (Eq.trans (congrArg (fun x : Int => a.num * x) Rat.one_num) (Int.mul_one a.num))
      (Eq.trans (congrArg (fun x : Nat => a.den * x) Rat.one_den) (Nat.mul_one a.den))
  exact Eq.trans e1 (qmk_self a)

-- Reference: [MRR], ch. on fields (additive inverse).
/-- `qadd (qneg a) a = 0`. -/
theorem qadd_left_neg (a : Rat) : qadd (qneg a) a = 0 := by
  have e1 : qadd (qneg a) a = qmk 0 (a.den * a.den) (qden_mul (qneg a) a) := by
    unfold qadd
    exact qmk_congr _ _ (qden_mul (qneg a) a) _ _ (qden_mul (qneg a) a)
      (Eq.trans (congrArg (fun x : Int => x * ↑a.den + a.num * ↑(qneg a).den) (qneg_num a))
        (Eq.trans (congrArg (fun x : Nat => (-a.num) * ↑a.den + a.num * ↑x) (qneg_den a))
          (Eq.trans (congrArg (fun x : Int => x + a.num * ↑a.den) (Int.neg_mul a.num (↑a.den)))
            (Eq.trans (Int.add_comm (-(a.num * ↑a.den)) (a.num * ↑a.den))
              (Eq.trans (Int.sub_eq_add_neg (a := a.num * ↑a.den) (b := a.num * ↑a.den)).symm
                (Int.sub_self (a.num * ↑a.den)))))))
      (congrArg (fun x : Nat => x * a.den) (qneg_den a))
  exact Eq.trans e1 (qmk_zero (a.den * a.den) (qden_mul (qneg a) a))

end BoringMath
