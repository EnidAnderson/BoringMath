/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/

import Mathlib.Init
import BoringMath.FormalPeriods.QArith.Normalize

/-!
# The computable operations (`QArith`, part 2)

Piece 2 of `BoringMath.FormalPeriods.QArith`: the computable operations
`qneg`, `qadd`, `qmul`, `qsub`, `qinv`, `qdiv` over `Rat`, built directly on
`qmk`/`Rat.mk'`, together with their definitional projection peels
(`qneg_num`, `qadd_num`, `qinv_num_neg`, ...) and the `reduced` field proofs
for `qneg`/`qinv`.
-/

namespace BoringMath

/-! ### The computable operations -/

-- Reference: [LeanRat], `Int.natAbs_neg`, `Rat.reduced`.
/-- The `reduced` field for `qneg` (computable proof). -/
theorem qneg_reduced (a : Rat) : (-a.num).natAbs.Coprime a.den :=
  Eq.mpr (congrArg (fun x : Nat => x.Coprime a.den) (Int.natAbs_neg a.num)) a.reduced

-- Reference: [MRR], ch. on fields (negation); [LeanRat], `Rat.mk'`, `Rat.neg`.
/-- Computable negation of a rational, via the structure constructor. -/
def qneg (a : Rat) : Rat := Rat.mk' (-a.num) a.den a.den_nz (qneg_reduced a)

-- Reference: [LeanRat], `Rat.num`; primitive definitional lemma (`rfl`).
/-- Numerator projection of `qneg` (definitional peel). -/
theorem qneg_num (a : Rat) : (qneg a).num = -a.num := rfl

-- Reference: [LeanRat], `Rat.den`; primitive definitional lemma (`rfl`).
/-- Denominator projection of `qneg` (definitional peel). -/
theorem qneg_den (a : Rat) : (qneg a).den = a.den := rfl

-- Reference: [LeanRat], `Rat.den_pos`, `Nat.mul_pos`.
/-- Product of denominators is nonzero (computable proof). -/
theorem qden_mul (a b : Rat) : a.den * b.den ≠ 0 :=
  Nat.ne_of_gt (Nat.mul_pos a.den_pos b.den_pos)

-- Reference: [MRR], ch. on fields (addition of fractions);
-- [LeanRat], `Rat.add` (choice-tainted) replaced by `qmk`.
/-- Computable addition of rationals: `(a.num * b.den + b.num * a.den) /
(a.den * b.den)`, normalized by `qmk`. -/
def qadd (a b : Rat) : Rat :=
  qmk (a.num * ↑b.den + b.num * ↑a.den) (a.den * b.den) (qden_mul a b)

-- Reference: [LeanRat], `Rat.num`; primitive definitional lemma (`rfl`).
/-- Numerator projection of `qadd` (definitional peel). -/
theorem qadd_num (a b : Rat) : (qadd a b).num =
    (a.num * ↑b.den + b.num * ↑a.den).divExact
      ((a.num * ↑b.den + b.num * ↑a.den).natAbs.gcd (a.den * b.den)) (qdvd_num _ _) := rfl

-- Reference: [LeanRat], `Rat.den`; primitive definitional lemma (`rfl`).
/-- Denominator projection of `qadd` (definitional peel). -/
theorem qadd_den (a b : Rat) : (qadd a b).den =
    (a.den * b.den).divExact
      ((a.num * ↑b.den + b.num * ↑a.den).natAbs.gcd (a.den * b.den)) (qdvd_den _ _) := rfl

-- Reference: [MRR], ch. on fields (multiplication of fractions);
-- [LeanRat], `Rat.mul` (choice-tainted) replaced by `qmk`.
/-- Computable multiplication of rationals. -/
def qmul (a b : Rat) : Rat := qmk (a.num * b.num) (a.den * b.den) (qden_mul a b)

-- Reference: [LeanRat], `Rat.num`; primitive definitional lemma (`rfl`).
/-- Numerator projection of `qmul` (definitional peel). -/
theorem qmul_num (a b : Rat) : (qmul a b).num =
    (a.num * b.num).divExact ((a.num * b.num).natAbs.gcd (a.den * b.den)) (qdvd_num _ _) := rfl

-- Reference: [LeanRat], `Rat.den`; primitive definitional lemma (`rfl`).
/-- Denominator projection of `qmul` (definitional peel). -/
theorem qmul_den (a b : Rat) : (qmul a b).den =
    (a.den * b.den).divExact ((a.num * b.num).natAbs.gcd (a.den * b.den)) (qdvd_den _ _) := rfl

-- Reference: [MRR], ch. on fields (subtraction).
/-- Computable subtraction of rationals. -/
def qsub (a b : Rat) : Rat := qadd a (qneg b)

-- Reference: [LeanRat], definitional unfolding; primitive lemma (`rfl`).
/-- Definition law of `qsub` (definitional peel). -/
theorem qsub_def (a b : Rat) : qsub a b = qadd a (qneg b) := rfl

-- Reference: [LeanRat], `Int.natAbs_pos`.
/-- A nonzero integer has nonzero `natAbs` (computable proof). -/
theorem qinv_den_nz {a : Rat} (h : a.num ≠ 0) : a.num.natAbs ≠ 0 :=
  Nat.ne_of_gt (Int.natAbs_pos.2 h)

-- Reference: [LeanRat], `Int.natAbs_neg`, `Int.natAbs_natCast`, `Nat.Coprime.symm`.
/-- The `reduced` field for `qinv` in the negative case (computable proof). -/
theorem qinv_reduced_neg (a : Rat) : (-(a.den : Int)).natAbs.Coprime a.num.natAbs :=
  Eq.mpr (congrArg (fun x : Nat => x.Coprime a.num.natAbs)
    (Eq.trans (Int.natAbs_neg (a.den : Int)) (Int.natAbs_natCast a.den))) a.reduced.symm

-- Reference: [LeanRat], `Int.natAbs_natCast`, `Nat.Coprime.symm`.
/-- The `reduced` field for `qinv` in the positive case (computable proof). -/
theorem qinv_reduced_pos (a : Rat) : ((a.den : Int)).natAbs.Coprime a.num.natAbs :=
  Eq.mpr (congrArg (fun x : Nat => x.Coprime a.num.natAbs) (Int.natAbs_natCast a.den)) a.reduced.symm

-- Reference: [MRR], ch. on fields (multiplicative inverse);
-- [LeanRat], `Rat.inv` (clean, but irreducible) mirrored via `Rat.mk'`.
/-- Computable inverse of a rational (`qinv 0 = 0`), via the structure
constructor with an explicit case split on the sign of the numerator. -/
def qinv (a : Rat) : Rat :=
  if h : a.num < 0 then
    Rat.mk' (-(a.den : Int)) a.num.natAbs (qinv_den_nz (Int.ne_of_lt h)) (qinv_reduced_neg a)
  else if h : 0 < a.num then
    Rat.mk' (a.den : Int) a.num.natAbs (qinv_den_nz (Int.ne_of_gt h)) (qinv_reduced_pos a)
  else a

-- Reference: [LeanRat], `Rat.mk'`, `Rat.num`; primitive definitional lemma (`rfl`).
/-- Numerator projection of `Rat.mk'` (definitional peel). -/
theorem qmk'_num (n : Int) (d : Nat) (h1 : d ≠ 0) (h2 : n.natAbs.Coprime d) :
    (Rat.mk' n d h1 h2).num = n := rfl

-- Reference: [LeanRat], `Rat.mk'`, `Rat.den`; primitive definitional lemma (`rfl`).
/-- Denominator projection of `Rat.mk'` (definitional peel). -/
theorem qmk'_den (n : Int) (d : Nat) (h1 : d ≠ 0) (h2 : n.natAbs.Coprime d) :
    (Rat.mk' n d h1 h2).den = d := rfl

-- Reference: [LeanRat], `dite_eq_left`; unfold of `qinv` in the negative case.
/-- Numerator of `qinv` in the negative case (peel). -/
theorem qinv_num_neg (a : Rat) (h : a.num < 0) : (qinv a).num = -(a.den : Int) := by
  unfold qinv
  exact Eq.trans (congrArg Rat.num (dite_eq_left h))
    (qmk'_num (-(a.den : Int)) a.num.natAbs (qinv_den_nz (Int.ne_of_lt h)) (qinv_reduced_neg a))

-- Reference: [LeanRat], `dite_eq_left`; denominator of `qinv` in the negative case.
/-- Denominator of `qinv` in the negative case (peel). -/
theorem qinv_den_neg (a : Rat) (h : a.num < 0) : (qinv a).den = a.num.natAbs := by
  unfold qinv
  exact Eq.trans (congrArg Rat.den (dite_eq_left h))
    (qmk'_den (-(a.den : Int)) a.num.natAbs (qinv_den_nz (Int.ne_of_lt h)) (qinv_reduced_neg a))

-- Reference: [LeanRat], `dite_eq_right`, `dite_eq_left`; positive case of `qinv`.
/-- Numerator of `qinv` in the positive case (peel). -/
theorem qinv_num_pos (a : Rat) (h : 0 < a.num) : (qinv a).num = (a.den : Int) := by
  unfold qinv
  exact Eq.trans (congrArg Rat.num (dite_eq_right (Int.not_lt.2 (Int.le_of_lt h))))
    (Eq.trans (congrArg Rat.num (dite_eq_left h))
      (qmk'_num (a.den : Int) a.num.natAbs (qinv_den_nz (Int.ne_of_gt h)) (qinv_reduced_pos a)))

-- Reference: [LeanRat], `dite_eq_right`, `dite_eq_left`; positive case of `qinv`.
/-- Denominator of `qinv` in the positive case (peel). -/
theorem qinv_den_pos (a : Rat) (h : 0 < a.num) : (qinv a).den = a.num.natAbs := by
  unfold qinv
  exact Eq.trans (congrArg Rat.den (dite_eq_right (Int.not_lt.2 (Int.le_of_lt h))))
    (Eq.trans (congrArg Rat.den (dite_eq_left h))
      (qmk'_den (a.den : Int) a.num.natAbs (qinv_den_nz (Int.ne_of_gt h)) (qinv_reduced_pos a)))

-- Reference: [MRR], ch. on fields (division).
/-- Computable division of rationals: `qmul a (qinv b)`. -/
def qdiv (a b : Rat) : Rat := qmul a (qinv b)

-- Reference: [LeanRat], definitional unfolding; primitive lemma (`rfl`).
/-- Definition law of `qdiv` (definitional peel). -/
theorem qdiv_def (a b : Rat) : qdiv a b = qmul a (qinv b) := rfl

end BoringMath
