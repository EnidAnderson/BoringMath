/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/

import Mathlib.Init
import BoringMath.FormalPeriods.QArith.Normalize
import BoringMath.FormalPeriods.QArith.Ops
import BoringMath.FormalPeriods.QArith.CrossEq
import BoringMath.FormalPeriods.QArith.IntLemmas

/-!
# The field laws, part 2: associativity, distributivity, inverse (`QArith`)

Piece 6 of `BoringMath.FormalPeriods.QArith`: `qadd_assoc`, `qmul_assoc`,
`mul_add`, and `qmul_inv_cancel`.
-/

namespace BoringMath

-- Reference: [MRR], ch. on fields (associativity of addition).
/-- `qadd` is associative. -/
theorem qadd_assoc (a b c : Rat) : qadd (qadd a b) c = qadd a (qadd b c) := by
  have hP := qadd_num_gcd_mul (qadd a b) c
  have hPd := qadd_den_gcd_mul (qadd a b) c
  have hQ := qadd_num_gcd_mul a (qadd b c)
  have hQd := qadd_den_gcd_mul a (qadd b c)
  have hGP : (↑(((qadd a b).num * ↑c.den + c.num * ↑(qadd a b).den).natAbs.gcd
      ((qadd a b).den * c.den)) : Int) ≠ 0 := qgcd_ne_zero (qden_mul (qadd a b) c)
  have hGQ : (↑((a.num * ↑(qadd b c).den + (qadd b c).num * ↑a.den).natAbs.gcd
      (a.den * (qadd b c).den)) : Int) ≠ 0 := qgcd_ne_zero (qden_mul a (qadd b c))
  have hNa := qadd_num_gcd_mul a b
  have hDa := qadd_den_gcd_mul a b
  have hNb := qadd_num_gcd_mul b c
  have hDb := qadd_den_gcd_mul b c
  have hga : (↑((a.num * ↑b.den + b.num * ↑a.den).natAbs.gcd (a.den * b.den)) : Int) ≠ 0 :=
    qgcd_ne_zero (qden_mul a b)
  have hgb : (↑((b.num * ↑c.den + c.num * ↑b.den).natAbs.gcd (b.den * c.den)) : Int) ≠ 0 :=
    qgcd_ne_zero (qden_mul b c)
  have eNL : ((qadd a b).num * ↑c.den + c.num * ↑(qadd a b).den) *
      ↑((a.num * ↑b.den + b.num * ↑a.den).natAbs.gcd (a.den * b.den)) =
      (a.num * ↑b.den + b.num * ↑a.den) * ↑c.den + c.num * ↑(a.den * b.den) :=
    Eq.trans (Int.add_mul ((qadd a b).num * ↑c.den) (c.num * ↑(qadd a b).den)
        (↑((a.num * ↑b.den + b.num * ↑a.den).natAbs.gcd (a.den * b.den))))
      (Eq.trans (congrArg (fun x : Int => x + (c.num * ↑(qadd a b).den) *
          ↑((a.num * ↑b.den + b.num * ↑a.den).natAbs.gcd (a.den * b.den)))
          (Int.mul_assoc ((qadd a b).num) (↑c.den)
            (↑((a.num * ↑b.den + b.num * ↑a.den).natAbs.gcd (a.den * b.den)))))
        (Eq.trans (congrArg (fun x : Int => ((qadd a b).num * (↑c.den *
            ↑((a.num * ↑b.den + b.num * ↑a.den).natAbs.gcd (a.den * b.den)))) + x)
            (Int.mul_assoc (c.num) (↑(qadd a b).den)
              (↑((a.num * ↑b.den + b.num * ↑a.den).natAbs.gcd (a.den * b.den)))))
          (Eq.trans (congrArg (fun x : Int => x + c.num * (↑(qadd a b).den *
              ↑((a.num * ↑b.den + b.num * ↑a.den).natAbs.gcd (a.den * b.den))))
              (qmul_comm_assoc ((qadd a b).num) (↑c.den)
                (↑((a.num * ↑b.den + b.num * ↑a.den).natAbs.gcd (a.den * b.den)))))
            (Eq.trans (congrArg (fun x : Int => x * ↑c.den + c.num * (↑(qadd a b).den *
                ↑((a.num * ↑b.den + b.num * ↑a.den).natAbs.gcd (a.den * b.den)))) hNa)
              (congrArg (fun x : Int => (a.num * ↑b.den + b.num * ↑a.den) * ↑c.den + c.num * x) hDa)))))
  have eNR : (a.num * ↑(qadd b c).den + (qadd b c).num * ↑a.den) *
      ↑((b.num * ↑c.den + c.num * ↑b.den).natAbs.gcd (b.den * c.den)) =
      a.num * ↑(b.den * c.den) + (b.num * ↑c.den + c.num * ↑b.den) * ↑a.den :=
    Eq.trans (Int.add_mul (a.num * ↑(qadd b c).den) ((qadd b c).num * ↑a.den)
        (↑((b.num * ↑c.den + c.num * ↑b.den).natAbs.gcd (b.den * c.den))))
      (Eq.trans (congrArg (fun x : Int => x + ((qadd b c).num * ↑a.den) *
          ↑((b.num * ↑c.den + c.num * ↑b.den).natAbs.gcd (b.den * c.den)))
          (Int.mul_assoc a.num (↑(qadd b c).den)
            (↑((b.num * ↑c.den + c.num * ↑b.den).natAbs.gcd (b.den * c.den)))))
        (Eq.trans (congrArg (fun x : Int => a.num * (↑(qadd b c).den *
            ↑((b.num * ↑c.den + c.num * ↑b.den).natAbs.gcd (b.den * c.den))) + x)
            (Int.mul_assoc ((qadd b c).num) (↑a.den)
              (↑((b.num * ↑c.den + c.num * ↑b.den).natAbs.gcd (b.den * c.den)))))
          (Eq.trans (congrArg (fun x : Int => a.num * x + ((qadd b c).num * (↑a.den *
              ↑((b.num * ↑c.den + c.num * ↑b.den).natAbs.gcd (b.den * c.den))))) hDb)
            (Eq.trans (congrArg (fun x : Int => a.num * ↑(b.den * c.den) + x)
                (qmul_comm_assoc ((qadd b c).num) (↑a.den)
                  (↑((b.num * ↑c.den + c.num * ↑b.den).natAbs.gcd (b.den * c.den)))))
              (congrArg (fun x : Int => a.num * ↑(b.den * c.den) + x * ↑a.den) hNb)))))
  have eDR : (↑(a.den * (qadd b c).den) : Int) *
      ↑((b.num * ↑c.den + c.num * ↑b.den).natAbs.gcd (b.den * c.den)) =
      (↑a.den : Int) * ↑(b.den * c.den) :=
    Eq.trans (congrArg (fun y : Nat => (↑(a.den * y) : Int) *
        ↑((b.num * ↑c.den + c.num * ↑b.den).natAbs.gcd (b.den * c.den))) (qadd_den b c))
      (cast_mul_den_gcd a.den (b.den * c.den)
        ((b.num * ↑c.den + c.num * ↑b.den).natAbs.gcd (b.den * c.den)) (qdvd_den _ _))
  have eDL : (↑((qadd a b).den * c.den) : Int) *
      ↑((a.num * ↑b.den + b.num * ↑a.den).natAbs.gcd (a.den * b.den)) =
      (↑(a.den * b.den) : Int) * ↑c.den :=
    Eq.trans (congrArg (fun y : Nat => (↑(y * c.den) : Int) *
        ↑((a.num * ↑b.den + b.num * ↑a.den).natAbs.gcd (a.den * b.den))) (qadd_den a b))
      (cast_den_gcd_mul_comm c.den (a.den * b.den)
        ((a.num * ↑b.den + b.num * ↑a.den).natAbs.gcd (a.den * b.den)) (qdvd_den _ _))
  have lhs1 : ((qadd (qadd a b) c).num * ↑(qadd a (qadd b c)).den) *
      (↑(((qadd a b).num * ↑c.den + c.num * ↑(qadd a b).den).natAbs.gcd ((qadd a b).den * c.den)) *
       ↑((a.num * ↑(qadd b c).den + (qadd b c).num * ↑a.den).natAbs.gcd (a.den * (qadd b c).den))) =
      ((qadd a b).num * ↑c.den + c.num * ↑(qadd a b).den) * ↑(a.den * (qadd b c).den) :=
    Eq.trans (qmul_assoc_swap (qadd (qadd a b) c).num (↑(qadd a (qadd b c)).den)
        (↑(((qadd a b).num * ↑c.den + c.num * ↑(qadd a b).den).natAbs.gcd ((qadd a b).den * c.den)))
        (↑((a.num * ↑(qadd b c).den + (qadd b c).num * ↑a.den).natAbs.gcd (a.den * (qadd b c).den))))
      (Eq.trans (congrArg (fun t : Int => t * (↑(qadd a (qadd b c)).den *
          ↑((a.num * ↑(qadd b c).den + (qadd b c).num * ↑a.den).natAbs.gcd
            (a.den * (qadd b c).den)))) hP)
        (congrArg (fun t : Int => ((qadd a b).num * ↑c.den + c.num * ↑(qadd a b).den) * t) hQd))
  have rhs1 : ((qadd a (qadd b c)).num * ↑(qadd (qadd a b) c).den) *
      (↑(((qadd a b).num * ↑c.den + c.num * ↑(qadd a b).den).natAbs.gcd ((qadd a b).den * c.den)) *
       ↑((a.num * ↑(qadd b c).den + (qadd b c).num * ↑a.den).natAbs.gcd (a.den * (qadd b c).den))) =
      (a.num * ↑(qadd b c).den + (qadd b c).num * ↑a.den) * ↑((qadd a b).den * c.den) :=
    Eq.trans (qmul_assoc_swap' (qadd a (qadd b c)).num (↑(qadd (qadd a b) c).den)
        (↑(((qadd a b).num * ↑c.den + c.num * ↑(qadd a b).den).natAbs.gcd ((qadd a b).den * c.den)))
        (↑((a.num * ↑(qadd b c).den + (qadd b c).num * ↑a.den).natAbs.gcd (a.den * (qadd b c).den))))
      (Eq.trans (congrArg (fun t : Int => t * (↑(qadd (qadd a b) c).den *
          ↑(((qadd a b).num * ↑c.den + c.num * ↑(qadd a b).den).natAbs.gcd
            ((qadd a b).den * c.den)))) hQ)
        (congrArg (fun t : Int => (a.num * ↑(qadd b c).den + (qadd b c).num * ↑a.den) * t) hPd))
  have lhs2 : (((qadd a b).num * ↑c.den + c.num * ↑(qadd a b).den) * ↑(a.den * (qadd b c).den)) *
      (↑((a.num * ↑b.den + b.num * ↑a.den).natAbs.gcd (a.den * b.den)) *
       ↑((b.num * ↑c.den + c.num * ↑b.den).natAbs.gcd (b.den * c.den))) =
      ((a.num * ↑b.den + b.num * ↑a.den) * ↑c.den + c.num * ↑(a.den * b.den)) *
      ((↑a.den : Int) * ↑(b.den * c.den)) :=
    Eq.trans (qmul_assoc_swap ((qadd a b).num * ↑c.den + c.num * ↑(qadd a b).den)
        (↑(a.den * (qadd b c).den))
        (↑((a.num * ↑b.den + b.num * ↑a.den).natAbs.gcd (a.den * b.den)))
        (↑((b.num * ↑c.den + c.num * ↑b.den).natAbs.gcd (b.den * c.den))))
      (Eq.trans (congrArg (fun t : Int => t * (↑(a.den * (qadd b c).den) *
          ↑((b.num * ↑c.den + c.num * ↑b.den).natAbs.gcd (b.den * c.den)))) eNL)
        (congrArg (fun t : Int => ((a.num * ↑b.den + b.num * ↑a.den) * ↑c.den + c.num * ↑(a.den * b.den)) * t)
          eDR))
  have rhs2 : ((a.num * ↑(qadd b c).den + (qadd b c).num * ↑a.den) * ↑((qadd a b).den * c.den)) *
      (↑((a.num * ↑b.den + b.num * ↑a.den).natAbs.gcd (a.den * b.den)) *
       ↑((b.num * ↑c.den + c.num * ↑b.den).natAbs.gcd (b.den * c.den))) =
      (a.num * ↑(b.den * c.den) + (b.num * ↑c.den + c.num * ↑b.den) * ↑a.den) *
      ((↑(a.den * b.den) : Int) * ↑c.den) :=
    Eq.trans (qmul_assoc_swap' (a.num * ↑(qadd b c).den + (qadd b c).num * ↑a.den)
        (↑((qadd a b).den * c.den))
        (↑((a.num * ↑b.den + b.num * ↑a.den).natAbs.gcd (a.den * b.den)))
        (↑((b.num * ↑c.den + c.num * ↑b.den).natAbs.gcd (b.den * c.den))))
      (Eq.trans (congrArg (fun t : Int => t * (↑((qadd a b).den * c.den) *
          ↑((a.num * ↑b.den + b.num * ↑a.den).natAbs.gcd (a.den * b.den)))) eNR)
        (congrArg (fun t : Int => (a.num * ↑(b.den * c.den) + (b.num * ↑c.den + c.num * ↑b.den) * ↑a.den) * t)
          eDL))
  have main : ((qadd a b).num * ↑c.den + c.num * ↑(qadd a b).den) * ↑(a.den * (qadd b c).den) =
      (a.num * ↑(qadd b c).den + (qadd b c).num * ↑a.den) * ↑((qadd a b).den * c.den) := by
    refine qcancel (Int.mul_ne_zero hga hgb) ?_
    exact Eq.trans lhs2 (Eq.trans (qadd_assoc_int a.num b.num c.num a.den b.den c.den) rhs2.symm)
  refine (qeq_iff _ _).mpr ?_
  refine qcancel (Int.mul_ne_zero hGP hGQ) ?_
  exact Eq.trans lhs1 (Eq.trans main rhs1.symm)

-- Reference: [MRR], ch. on fields (associativity of multiplication).
/-- `qmul` is associative. -/
theorem qmul_assoc (a b c : Rat) : qmul (qmul a b) c = qmul a (qmul b c) := by
  have hP := qmul_num_gcd_mul (qmul a b) c
  have hPd := qmul_den_gcd_mul (qmul a b) c
  have hQ := qmul_num_gcd_mul a (qmul b c)
  have hQd := qmul_den_gcd_mul a (qmul b c)
  have hGP : (↑(((qmul a b).num * c.num).natAbs.gcd ((qmul a b).den * c.den)) : Int) ≠ 0 :=
    qgcd_ne_zero (qden_mul (qmul a b) c)
  have hGQ : (↑((a.num * (qmul b c).num).natAbs.gcd (a.den * (qmul b c).den)) : Int) ≠ 0 :=
    qgcd_ne_zero (qden_mul a (qmul b c))
  have hNa := qmul_num_gcd_mul a b
  have hDa := qmul_den_gcd_mul a b
  have hNb := qmul_num_gcd_mul b c
  have hDb := qmul_den_gcd_mul b c
  have hga : (↑((a.num * b.num).natAbs.gcd (a.den * b.den)) : Int) ≠ 0 :=
    qgcd_ne_zero (qden_mul a b)
  have hgb : (↑((b.num * c.num).natAbs.gcd (b.den * c.den)) : Int) ≠ 0 :=
    qgcd_ne_zero (qden_mul b c)
  have eNL : ((qmul a b).num * c.num) *
      ↑((a.num * b.num).natAbs.gcd (a.den * b.den)) = (a.num * b.num) * c.num :=
    Eq.trans (Int.mul_assoc ((qmul a b).num) (c.num) (↑((a.num * b.num).natAbs.gcd (a.den * b.den))))
      (Eq.trans (qmul_comm_assoc ((qmul a b).num) (c.num)
          (↑((a.num * b.num).natAbs.gcd (a.den * b.den))))
        (congrArg (fun t : Int => t * c.num) hNa))
  have eNR : (a.num * (qmul b c).num) *
      ↑((b.num * c.num).natAbs.gcd (b.den * c.den)) = a.num * (b.num * c.num) :=
    Eq.trans (Int.mul_assoc a.num ((qmul b c).num)
        (↑((b.num * c.num).natAbs.gcd (b.den * c.den))))
      (congrArg (fun t : Int => a.num * t) hNb)
  have eDR : (↑(a.den * (qmul b c).den) : Int) *
      ↑((b.num * c.num).natAbs.gcd (b.den * c.den)) = (↑a.den : Int) * ↑(b.den * c.den) :=
    Eq.trans (congrArg (fun y : Nat => (↑(a.den * y) : Int) *
        ↑((b.num * c.num).natAbs.gcd (b.den * c.den))) (qmul_den b c))
      (cast_mul_den_gcd a.den (b.den * c.den)
        ((b.num * c.num).natAbs.gcd (b.den * c.den)) (qdvd_den _ _))
  have eDL : (↑((qmul a b).den * c.den) : Int) *
      ↑((a.num * b.num).natAbs.gcd (a.den * b.den)) = (↑(a.den * b.den) : Int) * ↑c.den :=
    Eq.trans (congrArg (fun y : Nat => (↑(y * c.den) : Int) *
        ↑((a.num * b.num).natAbs.gcd (a.den * b.den))) (qmul_den a b))
      (cast_den_gcd_mul_comm c.den (a.den * b.den)
        ((a.num * b.num).natAbs.gcd (a.den * b.den)) (qdvd_den _ _))
  have lhs1 : ((qmul (qmul a b) c).num * ↑(qmul a (qmul b c)).den) *
      (↑(((qmul a b).num * c.num).natAbs.gcd ((qmul a b).den * c.den)) *
       ↑((a.num * (qmul b c).num).natAbs.gcd (a.den * (qmul b c).den))) =
      ((qmul a b).num * c.num) * ↑(a.den * (qmul b c).den) :=
    Eq.trans (qmul_assoc_swap (qmul (qmul a b) c).num (↑(qmul a (qmul b c)).den)
        (↑(((qmul a b).num * c.num).natAbs.gcd ((qmul a b).den * c.den)))
        (↑((a.num * (qmul b c).num).natAbs.gcd (a.den * (qmul b c).den))))
      (Eq.trans (congrArg (fun t : Int => t * (↑(qmul a (qmul b c)).den *
          ↑((a.num * (qmul b c).num).natAbs.gcd (a.den * (qmul b c).den)))) hP)
        (congrArg (fun t : Int => ((qmul a b).num * c.num) * t) hQd))
  have rhs1 : ((qmul a (qmul b c)).num * ↑(qmul (qmul a b) c).den) *
      (↑(((qmul a b).num * c.num).natAbs.gcd ((qmul a b).den * c.den)) *
       ↑((a.num * (qmul b c).num).natAbs.gcd (a.den * (qmul b c).den))) =
      (a.num * (qmul b c).num) * ↑((qmul a b).den * c.den) :=
    Eq.trans (qmul_assoc_swap' (qmul a (qmul b c)).num (↑(qmul (qmul a b) c).den)
        (↑(((qmul a b).num * c.num).natAbs.gcd ((qmul a b).den * c.den)))
        (↑((a.num * (qmul b c).num).natAbs.gcd (a.den * (qmul b c).den))))
      (Eq.trans (congrArg (fun t : Int => t * (↑(qmul (qmul a b) c).den *
          ↑(((qmul a b).num * c.num).natAbs.gcd ((qmul a b).den * c.den)))) hQ)
        (congrArg (fun t : Int => (a.num * (qmul b c).num) * t) hPd))
  have lhs2 : (((qmul a b).num * c.num) * ↑(a.den * (qmul b c).den)) *
      (↑((a.num * b.num).natAbs.gcd (a.den * b.den)) *
       ↑((b.num * c.num).natAbs.gcd (b.den * c.den))) =
      ((a.num * b.num) * c.num) * ((↑a.den : Int) * ↑(b.den * c.den)) :=
    Eq.trans (qmul_assoc_swap ((qmul a b).num * c.num) (↑(a.den * (qmul b c).den))
        (↑((a.num * b.num).natAbs.gcd (a.den * b.den)))
        (↑((b.num * c.num).natAbs.gcd (b.den * c.den))))
      (Eq.trans (congrArg (fun t : Int => t * (↑(a.den * (qmul b c).den) *
          ↑((b.num * c.num).natAbs.gcd (b.den * c.den)))) eNL)
        (congrArg (fun t : Int => ((a.num * b.num) * c.num) * t) eDR))
  have rhs2 : ((a.num * (qmul b c).num) * ↑((qmul a b).den * c.den)) *
      (↑((a.num * b.num).natAbs.gcd (a.den * b.den)) *
       ↑((b.num * c.num).natAbs.gcd (b.den * c.den))) =
      (a.num * (b.num * c.num)) * ((↑(a.den * b.den) : Int) * ↑c.den) :=
    Eq.trans (qmul_assoc_swap' (a.num * (qmul b c).num) (↑((qmul a b).den * c.den))
        (↑((a.num * b.num).natAbs.gcd (a.den * b.den)))
        (↑((b.num * c.num).natAbs.gcd (b.den * c.den))))
      (Eq.trans (congrArg (fun t : Int => t * (↑((qmul a b).den * c.den) *
          ↑((a.num * b.num).natAbs.gcd (a.den * b.den)))) eNR)
        (congrArg (fun t : Int => (a.num * (b.num * c.num)) * t) eDL))
  have main : ((qmul a b).num * c.num) * ↑(a.den * (qmul b c).den) =
      (a.num * (qmul b c).num) * ↑((qmul a b).den * c.den) := by
    refine qcancel (Int.mul_ne_zero hga hgb) ?_
    exact Eq.trans lhs2 (Eq.trans (qmul_assoc_int a.num b.num c.num a.den b.den c.den) rhs2.symm)
  refine (qeq_iff _ _).mpr ?_
  refine qcancel (Int.mul_ne_zero hGP hGQ) ?_
  exact Eq.trans lhs1 (Eq.trans main rhs1.symm)

-- Reference: [MRR], ch. on fields (distributivity).
/-- `qmul` distributes over `qadd` on the right. -/
theorem mul_add (a b c : Rat) : qmul (qadd a b) c = qadd (qmul a c) (qmul b c) := by
  have hP := qmul_num_gcd_mul (qadd a b) c
  have hPd := qmul_den_gcd_mul (qadd a b) c
  have hQ := qadd_num_gcd_mul (qmul a c) (qmul b c)
  have hQd := qadd_den_gcd_mul (qmul a c) (qmul b c)
  have hGP : (↑(((qadd a b).num * c.num).natAbs.gcd ((qadd a b).den * c.den)) : Int) ≠ 0 :=
    qgcd_ne_zero (qden_mul (qadd a b) c)
  have hGQ : (↑(((qmul a c).num * ↑(qmul b c).den + (qmul b c).num * ↑(qmul a c).den).natAbs.gcd
      ((qmul a c).den * (qmul b c).den)) : Int) ≠ 0 :=
    qgcd_ne_zero (qden_mul (qmul a c) (qmul b c))
  have hNa := qadd_num_gcd_mul a b
  have hDa := qadd_den_gcd_mul a b
  have hNac := qmul_num_gcd_mul a c
  have hDac := qmul_den_gcd_mul a c
  have hNbc := qmul_num_gcd_mul b c
  have hDbc := qmul_den_gcd_mul b c
  have hga : (↑((a.num * ↑b.den + b.num * ↑a.den).natAbs.gcd (a.den * b.den)) : Int) ≠ 0 :=
    qgcd_ne_zero (qden_mul a b)
  have hgac : (↑((a.num * c.num).natAbs.gcd (a.den * c.den)) : Int) ≠ 0 :=
    qgcd_ne_zero (qden_mul a c)
  have hgbc : (↑((b.num * c.num).natAbs.gcd (b.den * c.den)) : Int) ≠ 0 :=
    qgcd_ne_zero (qden_mul b c)
  have eNL : ((qadd a b).num * c.num) *
      ↑((a.num * ↑b.den + b.num * ↑a.den).natAbs.gcd (a.den * b.den)) =
      (a.num * ↑b.den + b.num * ↑a.den) * c.num :=
    Eq.trans (Int.mul_assoc ((qadd a b).num) (c.num)
        (↑((a.num * ↑b.den + b.num * ↑a.den).natAbs.gcd (a.den * b.den))))
      (Eq.trans (qmul_comm_assoc ((qadd a b).num) (c.num)
          (↑((a.num * ↑b.den + b.num * ↑a.den).natAbs.gcd (a.den * b.den))))
        (congrArg (fun t : Int => t * c.num) hNa))
  have eNR : ((qmul a c).num * ↑(qmul b c).den + (qmul b c).num * ↑(qmul a c).den) *
      (↑((a.num * c.num).natAbs.gcd (a.den * c.den)) *
       ↑((b.num * c.num).natAbs.gcd (b.den * c.den))) =
      (a.num * c.num) * ↑(b.den * c.den) + (b.num * c.num) * ↑(a.den * c.den) :=
    Eq.trans (Int.add_mul ((qmul a c).num * ↑(qmul b c).den) ((qmul b c).num * ↑(qmul a c).den)
        (↑((a.num * c.num).natAbs.gcd (a.den * c.den)) *
         ↑((b.num * c.num).natAbs.gcd (b.den * c.den))))
      (Eq.trans (congrArg (fun x : Int => x + ((qmul b c).num * ↑(qmul a c).den) *
          (↑((a.num * c.num).natAbs.gcd (a.den * c.den)) *
           ↑((b.num * c.num).natAbs.gcd (b.den * c.den))))
          (qmul_assoc_swap ((qmul a c).num) (↑(qmul b c).den)
            (↑((a.num * c.num).natAbs.gcd (a.den * c.den)))
            (↑((b.num * c.num).natAbs.gcd (b.den * c.den)))))
        (Eq.trans (congrArg (fun x : Int => (((qmul a c).num * ↑((a.num * c.num).natAbs.gcd (a.den * c.den))) *
            (↑(qmul b c).den * ↑((b.num * c.num).natAbs.gcd (b.den * c.den)))) + x)
            (qmul_assoc_swap' ((qmul b c).num) (↑(qmul a c).den)
              (↑((a.num * c.num).natAbs.gcd (a.den * c.den)))
              (↑((b.num * c.num).natAbs.gcd (b.den * c.den)))))
          (Eq.trans (congrArg (fun x : Int => x * (↑(qmul b c).den *
              ↑((b.num * c.num).natAbs.gcd (b.den * c.den))) +
              ((qmul b c).num * ↑((b.num * c.num).natAbs.gcd (b.den * c.den))) *
              (↑(qmul a c).den * ↑((a.num * c.num).natAbs.gcd (a.den * c.den)))) hNac)
            (Eq.trans (congrArg (fun x : Int => (a.num * c.num) * x +
                ((qmul b c).num * ↑((b.num * c.num).natAbs.gcd (b.den * c.den))) *
                (↑(qmul a c).den * ↑((a.num * c.num).natAbs.gcd (a.den * c.den)))) hDbc)
              (Eq.trans (congrArg (fun x : Int => (a.num * c.num) * ↑(b.den * c.den) + x *
                  (↑(qmul a c).den * ↑((a.num * c.num).natAbs.gcd (a.den * c.den)))) hNbc)
                (congrArg (fun x : Int => (a.num * c.num) * ↑(b.den * c.den) + (b.num * c.num) * x) hDac))))))
  have eDR : (↑((qmul a c).den * (qmul b c).den) : Int) *
      (↑((a.num * c.num).natAbs.gcd (a.den * c.den)) *
       ↑((b.num * c.num).natAbs.gcd (b.den * c.den))) =
      (↑(a.den * c.den) : Int) * ↑(b.den * c.den) :=
    Eq.trans (congrArg (fun x : Int => x * (↑((a.num * c.num).natAbs.gcd (a.den * c.den)) *
        ↑((b.num * c.num).natAbs.gcd (b.den * c.den))))
        (Int.natCast_mul ((qmul a c).den) ((qmul b c).den)))
      (Eq.trans (qmul_assoc_swap (↑(qmul a c).den) (↑(qmul b c).den)
          (↑((a.num * c.num).natAbs.gcd (a.den * c.den)))
          (↑((b.num * c.num).natAbs.gcd (b.den * c.den))))
        (Eq.trans (congrArg (fun t : Int => t * (↑(qmul b c).den *
            ↑((b.num * c.num).natAbs.gcd (b.den * c.den)))) hDac)
          (congrArg (fun t : Int => ↑(a.den * c.den) * t) hDbc)))
  have eDL : (↑((qadd a b).den * c.den) : Int) *
      ↑((a.num * ↑b.den + b.num * ↑a.den).natAbs.gcd (a.den * b.den)) =
      (↑(a.den * b.den) : Int) * ↑c.den :=
    Eq.trans (congrArg (fun x : Int => x * ↑((a.num * ↑b.den + b.num * ↑a.den).natAbs.gcd (a.den * b.den)))
        (Int.natCast_mul ((qadd a b).den) (c.den)))
      (Eq.trans (Int.mul_assoc (↑(qadd a b).den) (↑c.den)
          (↑((a.num * ↑b.den + b.num * ↑a.den).natAbs.gcd (a.den * b.den))))
        (Eq.trans (qmul_comm_assoc (↑(qadd a b).den) (↑c.den)
            (↑((a.num * ↑b.den + b.num * ↑a.den).natAbs.gcd (a.den * b.den))))
          (congrArg (fun t : Int => t * ↑c.den) hDa)))
  have lhs1 : ((qmul (qadd a b) c).num * ↑(qadd (qmul a c) (qmul b c)).den) *
      (↑(((qadd a b).num * c.num).natAbs.gcd ((qadd a b).den * c.den)) *
       ↑(((qmul a c).num * ↑(qmul b c).den + (qmul b c).num * ↑(qmul a c).den).natAbs.gcd
         ((qmul a c).den * (qmul b c).den))) =
      ((qadd a b).num * c.num) * ↑((qmul a c).den * (qmul b c).den) :=
    Eq.trans (qmul_assoc_swap (qmul (qadd a b) c).num (↑(qadd (qmul a c) (qmul b c)).den)
        (↑(((qadd a b).num * c.num).natAbs.gcd ((qadd a b).den * c.den)))
        (↑(((qmul a c).num * ↑(qmul b c).den + (qmul b c).num * ↑(qmul a c).den).natAbs.gcd
          ((qmul a c).den * (qmul b c).den))))
      (Eq.trans (congrArg (fun t : Int => t * (↑(qadd (qmul a c) (qmul b c)).den *
          ↑(((qmul a c).num * ↑(qmul b c).den + (qmul b c).num * ↑(qmul a c).den).natAbs.gcd
            ((qmul a c).den * (qmul b c).den)))) hP)
        (congrArg (fun t : Int => ((qadd a b).num * c.num) * t) hQd))
  have rhs1 : ((qadd (qmul a c) (qmul b c)).num * ↑(qmul (qadd a b) c).den) *
      (↑(((qadd a b).num * c.num).natAbs.gcd ((qadd a b).den * c.den)) *
       ↑(((qmul a c).num * ↑(qmul b c).den + (qmul b c).num * ↑(qmul a c).den).natAbs.gcd
         ((qmul a c).den * (qmul b c).den))) =
      ((qmul a c).num * ↑(qmul b c).den + (qmul b c).num * ↑(qmul a c).den) *
      ↑((qadd a b).den * c.den) :=
    Eq.trans (qmul_assoc_swap' (qadd (qmul a c) (qmul b c)).num (↑(qmul (qadd a b) c).den)
        (↑(((qadd a b).num * c.num).natAbs.gcd ((qadd a b).den * c.den)))
        (↑(((qmul a c).num * ↑(qmul b c).den + (qmul b c).num * ↑(qmul a c).den).natAbs.gcd
          ((qmul a c).den * (qmul b c).den))))
      (Eq.trans (congrArg (fun t : Int => t * (↑(qmul (qadd a b) c).den *
          ↑(((qadd a b).num * c.num).natAbs.gcd ((qadd a b).den * c.den)))) hQ)
        (congrArg (fun t : Int => ((qmul a c).num * ↑(qmul b c).den + (qmul b c).num * ↑(qmul a c).den) * t)
          hPd))
  have lhs2 : (((qadd a b).num * c.num) * ↑((qmul a c).den * (qmul b c).den)) *
      (↑((a.num * ↑b.den + b.num * ↑a.den).natAbs.gcd (a.den * b.den)) *
       (↑((a.num * c.num).natAbs.gcd (a.den * c.den)) *
        ↑((b.num * c.num).natAbs.gcd (b.den * c.den)))) =
      ((a.num * ↑b.den + b.num * ↑a.den) * c.num) *
      ((↑(a.den * c.den) : Int) * ↑(b.den * c.den)) :=
    Eq.trans (qmul_assoc_swap ((qadd a b).num * c.num) (↑((qmul a c).den * (qmul b c).den))
        (↑((a.num * ↑b.den + b.num * ↑a.den).natAbs.gcd (a.den * b.den)))
        (↑((a.num * c.num).natAbs.gcd (a.den * c.den)) *
         ↑((b.num * c.num).natAbs.gcd (b.den * c.den))))
      (Eq.trans (congrArg (fun t : Int => t * (↑((qmul a c).den * (qmul b c).den) *
          (↑((a.num * c.num).natAbs.gcd (a.den * c.den)) *
           ↑((b.num * c.num).natAbs.gcd (b.den * c.den))))) eNL)
        (congrArg (fun t : Int => ((a.num * ↑b.den + b.num * ↑a.den) * c.num) * t) eDR))
  have rhs2 : (((qmul a c).num * ↑(qmul b c).den + (qmul b c).num * ↑(qmul a c).den) *
        ↑((qadd a b).den * c.den)) *
      (↑((a.num * ↑b.den + b.num * ↑a.den).natAbs.gcd (a.den * b.den)) *
       (↑((a.num * c.num).natAbs.gcd (a.den * c.den)) *
        ↑((b.num * c.num).natAbs.gcd (b.den * c.den)))) =
      ((a.num * c.num) * ↑(b.den * c.den) + (b.num * c.num) * ↑(a.den * c.den)) *
      ((↑(a.den * b.den) : Int) * ↑c.den) :=
    Eq.trans (qmul_assoc_swap' ((qmul a c).num * ↑(qmul b c).den + (qmul b c).num * ↑(qmul a c).den)
        (↑((qadd a b).den * c.den))
        (↑((a.num * ↑b.den + b.num * ↑a.den).natAbs.gcd (a.den * b.den)))
        (↑((a.num * c.num).natAbs.gcd (a.den * c.den)) *
         ↑((b.num * c.num).natAbs.gcd (b.den * c.den))))
      (Eq.trans (congrArg (fun t : Int => t * (↑((qadd a b).den * c.den) *
          ↑((a.num * ↑b.den + b.num * ↑a.den).natAbs.gcd (a.den * b.den)))) eNR)
        (congrArg (fun t : Int => ((a.num * c.num) * ↑(b.den * c.den) + (b.num * c.num) * ↑(a.den * c.den)) * t)
          eDL))
  have main : ((qadd a b).num * c.num) * ↑((qmul a c).den * (qmul b c).den) =
      ((qmul a c).num * ↑(qmul b c).den + (qmul b c).num * ↑(qmul a c).den) * ↑((qadd a b).den * c.den) := by
    refine qcancel (Int.mul_ne_zero hga (Int.mul_ne_zero hgac hgbc)) ?_
    exact Eq.trans lhs2
      (Eq.trans (mul_add_int a.num b.num c.num a.den b.den c.den) rhs2.symm)
  refine (qeq_iff _ _).mpr ?_
  refine qcancel (Int.mul_ne_zero hGP hGQ) ?_
  exact Eq.trans lhs1 (Eq.trans main rhs1.symm)

-- Reference: [MRR], ch. on fields (multiplicative inverse); [LeanRat],
-- `Int.natAbs_eq`, `Int.neg_pos`, `Int.natCast_nonneg`.
/-- `qmul a (qinv a) = 1` for `a ≠ 0`. -/
theorem qmul_inv_cancel (a : Rat) (ha : a ≠ 0) : qmul a (qinv a) = 1 := by
  have hn : a.num ≠ 0 := (qnum_ne_zero a).1 ha
  rcases Int.lt_or_gt_of_ne hn with h | h
  · have e2 : a.num = -↑(a.num.natAbs) :=
      (Int.natAbs_eq a.num).resolve_left (fun hc =>
        Int.not_lt.2 (Int.natCast_nonneg _) (Eq.subst (motive := fun x : Int => x < 0) hc h))
    refine Eq.mpr (congrArg (fun x : Rat => qmul a (qinv a) = x) (qmk_one Nat.one_ne_zero).symm) ?_
    unfold qmul
    refine (qmk_eq_iff _ _ (qden_mul a (qinv a)) _ _ Nat.one_ne_zero).2 ?_
    have lhs : (a.num * (qinv a).num) * ↑(1 : Nat) = ↑(a.den * a.num.natAbs) :=
      Eq.trans (congrArg (fun x : Int => (x * (qinv a).num) * ↑(1 : Nat)) e2)
        (Eq.trans (congrArg (fun x : Int => ((-↑(a.num.natAbs)) * x) * ↑(1 : Nat)) (qinv_num_neg a h))
          (Eq.trans (congrArg (fun x : Int => ((-↑(a.num.natAbs)) * (-(a.den : Int))) * x)
              Int.natCast_one)
            (Eq.trans (Int.mul_one _)
              (Eq.trans (Int.neg_mul (↑(a.num.natAbs)) (-(a.den : Int)))
                (Eq.trans (congrArg (fun x : Int => -x) (Int.mul_neg (↑(a.num.natAbs)) (↑a.den)))
                  (Eq.trans (Int.neg_neg _)
                    (Eq.trans ((Int.natCast_mul (a.num.natAbs) a.den).symm)
                      (congrArg (fun y : Nat => (↑y : Int)) (Nat.mul_comm (a.num.natAbs) a.den)))))))))
    have rhs : (1 : Int) * ↑(a.den * (qinv a).den) = ↑(a.den * a.num.natAbs) :=
      Eq.trans (congrArg (fun x : Nat => (1 : Int) * ↑(a.den * x)) (qinv_den_neg a h)) (Int.one_mul _)
    exact Eq.trans lhs rhs.symm
  · have e2 : a.num = ↑(a.num.natAbs) :=
      (Int.natAbs_eq a.num).resolve_right (fun hc =>
        Int.not_lt.2 (Int.natCast_nonneg _)
          (Int.neg_pos.1 (Eq.subst (motive := fun x => 0 < x) hc h)))
    refine Eq.mpr (congrArg (fun x : Rat => qmul a (qinv a) = x) (qmk_one Nat.one_ne_zero).symm) ?_
    unfold qmul
    refine (qmk_eq_iff _ _ (qden_mul a (qinv a)) _ _ Nat.one_ne_zero).2 ?_
    have lhs : (a.num * (qinv a).num) * ↑(1 : Nat) = ↑(a.den * a.num.natAbs) :=
      Eq.trans (congrArg (fun x : Int => (x * (qinv a).num) * ↑(1 : Nat)) e2)
        (Eq.trans (congrArg (fun x : Int => (↑(a.num.natAbs) * x) * ↑(1 : Nat)) (qinv_num_pos a h))
          (Eq.trans (congrArg (fun x : Int => (↑(a.num.natAbs) * (a.den : Int)) * x) Int.natCast_one)
            (Eq.trans (Int.mul_one _)
              (Eq.trans ((Int.natCast_mul (a.num.natAbs) a.den).symm)
                (congrArg (fun y : Nat => (↑y : Int)) (Nat.mul_comm (a.num.natAbs) a.den))))))
    have rhs : (1 : Int) * ↑(a.den * (qinv a).den) = ↑(a.den * a.num.natAbs) :=
      Eq.trans (congrArg (fun x : Nat => (1 : Int) * ↑(a.den * x)) (qinv_den_pos a h)) (Int.one_mul _)
    exact Eq.trans lhs rhs.symm

end BoringMath
