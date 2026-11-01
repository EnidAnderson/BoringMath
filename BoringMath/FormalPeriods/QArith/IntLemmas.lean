/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/

import Mathlib.Init
import BoringMath.FormalPeriods.QArith.Normalize

/-!
# Pure integer lemmas, the residual computations (`QArith`, part 4)

Piece 4 of `BoringMath.FormalPeriods.QArith`: the integer identities behind
associativity of `qadd` (`qadd_assoc_int`), associativity of `qmul`
(`qmul_assoc_int`), and distributivity of `qmul` over `qadd` (`mul_add_int`).
-/

namespace BoringMath

/-! ### Pure integer lemmas (the residual computations) -/

-- Reference: [MRR], ch. on rings (associativity of `+` and `*` over `ℤ`).
/-- The integer identity behind associativity of `qadd`. -/
theorem qadd_assoc_int (a b c : Int) (p q r : Nat) :
    ((a * ↑q + b * ↑p) * ↑r + c * ↑(p * q)) * (↑p * ↑(q * r)) =
    (a * ↑(q * r) + (b * ↑r + c * ↑q) * ↑p) * (↑(p * q) * ↑r) := by
  have hK : (↑p * ↑(q * r) : Int) = ↑(p * q) * ↑r :=
    Eq.trans (congrArg (fun x : Int => ↑p * x) (Int.natCast_mul q r))
      (Eq.trans (Int.mul_assoc (↑p) (↑q) (↑r)).symm
        (congrArg (fun y : Int => y * ↑r) (Int.natCast_mul p q).symm))
  have hXY : ((a * ↑q + b * ↑p) * ↑r + c * ↑(p * q)) =
      (a * ↑(q * r) + (b * ↑r + c * ↑q) * ↑p) := by
    have pl : ((a * ↑q + b * ↑p) * ↑r + c * ↑(p * q)) =
        (a * (↑q * ↑r) + (b * ↑r * ↑p + c * ↑q * ↑p)) :=
      Eq.trans (congrArg (fun x : Int => x + c * ↑(p * q)) (Int.add_mul (a * ↑q) (b * ↑p) (↑r)))
        (Eq.trans (congrArg (fun x : Int => (a * ↑q * ↑r + b * ↑p * ↑r) + c * x) (Int.natCast_mul p q))
          (Eq.trans (congrArg (fun x : Int => (x + b * ↑p * ↑r) + c * (↑p * ↑q))
              (Int.mul_assoc a (↑q) (↑r)))
            (Eq.trans (congrArg (fun x : Int => (a * (↑q * ↑r) + x) + c * (↑p * ↑q))
                (Int.mul_assoc b (↑p) (↑r)))
              (Eq.trans (congrArg (fun x : Int => (a * (↑q * ↑r) + b * x) + c * (↑p * ↑q))
                  (Int.mul_comm (↑p) (↑r)))
                (Eq.trans (congrArg (fun x : Int => (a * (↑q * ↑r) + x) + c * (↑p * ↑q))
                    ((Int.mul_assoc b (↑r) (↑p)).symm))
                  (Eq.trans (congrArg (fun x : Int => (a * (↑q * ↑r) + b * ↑r * ↑p) + c * x)
                      (Int.mul_comm (↑p) (↑q)))
                    (Eq.trans (congrArg (fun x : Int => (a * (↑q * ↑r) + b * ↑r * ↑p) + x)
                        ((Int.mul_assoc c (↑q) (↑p)).symm))
                      (Int.add_assoc (a * (↑q * ↑r)) (b * ↑r * ↑p) (c * ↑q * ↑p)))))))))
    have qr : (a * ↑(q * r) + (b * ↑r + c * ↑q) * ↑p) =
        (a * (↑q * ↑r) + (b * ↑r * ↑p + c * ↑q * ↑p)) :=
      Eq.trans (congrArg (fun x : Int => a * x + (b * ↑r + c * ↑q) * ↑p) (Int.natCast_mul q r))
        (congrArg (fun x : Int => a * (↑q * ↑r) + x) (Int.add_mul (b * ↑r) (c * ↑q) (↑p)))
    exact Eq.trans pl qr.symm
  exact Eq.mpr
    (Eq.trans (congrArg (fun x : Int => ((a * ↑q + b * ↑p) * ↑r + c * ↑(p * q)) * x =
        (a * ↑(q * r) + (b * ↑r + c * ↑q) * ↑p) * (↑(p * q) * ↑r)) hK)
      (congrArg (fun y : Int => y * (↑(p * q) * ↑r) =
        (a * ↑(q * r) + (b * ↑r + c * ↑q) * ↑p) * (↑(p * q) * ↑r)) hXY))
    rfl

-- Reference: [MRR], ch. on rings (associativity of `*` over `ℤ`).
/-- The integer identity behind associativity of `qmul`. -/
theorem qmul_assoc_int (a b c : Int) (p q r : Nat) :
    ((a * b) * c) * (↑p * ↑(q * r)) = (a * (b * c)) * (↑(p * q) * ↑r) := by
  exact Eq.mpr (Eq.trans
    (congrArg (fun x : Int => x * (↑p * ↑(q * r)) = (a * (b * c)) * (↑(p * q) * ↑r))
      (Int.mul_assoc a b c))
    (Eq.trans
      (congrArg (fun x : Int => (a * (b * c)) * x = (a * (b * c)) * (↑(p * q) * ↑r))
        (congrArg (fun y : Int => ↑p * y) (Int.natCast_mul q r)))
      (Eq.trans
        (congrArg (fun z : Int => (a * (b * c)) * (↑p * (↑q * ↑r)) = z)
          (congrArg (fun w : Int => (a * (b * c)) * (w * ↑r)) (Int.natCast_mul p q)))
        (congrArg (fun v : Int => (a * (b * c)) * (↑p * (↑q * ↑r)) = (a * (b * c)) * v)
          (Int.mul_assoc (↑p) (↑q) (↑r)))))) rfl

-- Reference: [MRR], ch. on rings (distributivity over `ℤ`).
/-- The integer identity behind distributivity of `qmul` over `qadd`. -/
theorem mul_add_int (a b c : Int) (p q r : Nat) :
    ((a * ↑q + b * ↑p) * c) * (↑(p * r) * ↑(q * r)) =
    ((a * c) * ↑(q * r) + (b * c) * ↑(p * r)) * (↑(p * q) * ↑r) := by
  have hK : (↑(p * r) * ↑(q * r) : Int) = (↑(p * q) * ↑r) * ↑r := by
    exact Eq.mpr (Eq.trans
      (congrArg (fun x : Int => x * ↑(q * r) = ((↑(p * q) * ↑r) * ↑r)) (Int.natCast_mul p r))
      (Eq.trans
        (congrArg (fun x : Int => (↑p * ↑r) * x = ((↑(p * q) * ↑r) * ↑r)) (Int.natCast_mul q r))
        (Eq.trans
          (congrArg (fun x : Int => x = ((↑(p * q) * ↑r) * ↑r))
            (qmul_assoc_swap (↑p) (↑r) (↑q) (↑r)))
          (Eq.trans
            (congrArg (fun x : Int => (↑p * ↑q) * (↑r * ↑r) = x)
              (congrArg (fun y : Int => (y * ↑r) * ↑r) (Int.natCast_mul p q)))
            (congrArg (fun z : Int => (↑p * ↑q) * (↑r * ↑r) = z)
              (Int.mul_assoc (↑p * ↑q) (↑r) (↑r))))))) rfl
  have hXY : ((a * ↑q + b * ↑p) * c) * ↑r =
      ((a * c) * ↑(q * r) + (b * c) * ↑(p * r)) := by
    have pl : ((a * ↑q + b * ↑p) * c) * ↑r =
        ((a * c) * (↑q * ↑r) + (b * c) * (↑p * ↑r)) :=
      Eq.trans (congrArg (fun x : Int => x * ↑r) (Int.add_mul (a * ↑q) (b * ↑p) c))
        (Eq.trans (Int.add_mul (a * ↑q * c) (b * ↑p * c) (↑r))
          (Eq.trans (congrArg (fun x : Int => x * ↑r + b * ↑p * c * ↑r) (Int.mul_assoc a (↑q) c))
            (Eq.trans (congrArg (fun x : Int => a * (↑q * c) * ↑r + x * ↑r) (Int.mul_assoc b (↑p) c))
              (Eq.trans (congrArg (fun x : Int => a * x * ↑r + b * (↑p * c) * ↑r)
                  (Int.mul_comm (↑q) c))
                (Eq.trans (congrArg (fun x : Int => x * ↑r + b * (↑p * c) * ↑r)
                    ((Int.mul_assoc a c (↑q)).symm))
                  (Eq.trans (congrArg (fun x : Int => a * c * ↑q * ↑r + b * x * ↑r)
                      (Int.mul_comm (↑p) c))
                    (Eq.trans (congrArg (fun x : Int => a * c * ↑q * ↑r + x * ↑r)
                        ((Int.mul_assoc b c (↑p)).symm))
                      (Eq.trans (congrArg (fun x : Int => x + b * c * ↑p * ↑r)
                          (Int.mul_assoc (a * c) (↑q) (↑r)))
                        (congrArg (fun x : Int => (a * c) * (↑q * ↑r) + x)
                          (Int.mul_assoc (b * c) (↑p) (↑r)))))))))))
    have qr : ((a * c) * ↑(q * r) + (b * c) * ↑(p * r)) =
        ((a * c) * (↑q * ↑r) + (b * c) * (↑p * ↑r)) :=
      Eq.trans (congrArg (fun x : Int => (a * c) * x + (b * c) * ↑(p * r)) (Int.natCast_mul q r))
        (congrArg (fun x : Int => (a * c) * (↑q * ↑r) + (b * c) * x) (Int.natCast_mul p r))
    exact Eq.trans pl qr.symm
  exact Eq.mpr
    (Eq.trans (congrArg (fun x : Int => ((a * ↑q + b * ↑p) * c) * x =
        ((a * c) * ↑(q * r) + (b * c) * ↑(p * r)) * (↑(p * q) * ↑r)) hK)
      (congrArg (fun y : Int => y =
        ((a * c) * ↑(q * r) + (b * c) * ↑(p * r)) * (↑(p * q) * ↑r))
        (Eq.trans (qmul_comm_assoc ((a * ↑q + b * ↑p) * c) (↑(p * q) * ↑r) (↑r)) (congrArg (fun t : Int => t * (↑(p * q) * ↑r)) hXY))))
    rfl

end BoringMath
