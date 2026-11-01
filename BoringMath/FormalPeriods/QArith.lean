/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Init
import BoringMath.FormalPeriods.AxiomLint

/-!
# Constructive rational arithmetic (`QArith`)

A narrow, fully computable replacement for the choice-tainted rational
arithmetic of Lean core / Mathlib at the pin `lean4 v4.35.0-rc3` /
`mathlib v4.35.0-rc3` (ticket RETRO.7). At this pin, `Rat.add`, `Rat.mul`,
`Rat.sub`, `Rat.div`, `Rat.normalize` and `Rat.instField` all depend on
`Classical.choice`: the taint enters through the `reduced` field proofs —
`Rat.normalize.reduced` (via `Int.natAbs_ediv_of_dvd`/`Int.natAbs_ediv`)
for `Rat.add`/`Rat.sub`/`Rat.normalize`, and through `Int.divExact_eq_tdiv`
in the `reduced` field of `Rat.mul`. Everything else used here
(`Rat.mk'`, `Rat.normalize.dvd_num`/`dvd_den`/`den_nz`, `Nat.gcd` lemmas,
`Int.divExact_eq_ediv`, `Int.natCast_ediv`, ...) is axiom-clean.

This module defines computable operations `qadd`, `qneg`, `qsub`, `qmul`,
`qinv`, `qdiv` over `ℚ` built directly on `Rat.mk'` with explicit
computable normalization (`Nat.gcd` + `Int.divExact`/`Nat.divExact` +
a computable `Nat.Coprime` proof via `qNatAbs_ediv` and
`Nat.coprime_div_gcd_div_gcd`), and proves the field laws the P-line
needs. Every declaration is linted at the bottom with `#print axioms`;
all are clean (only `propext`/`Quot.sound`).

## References
* [MRR] A. Mines, F. Richman, W. Ruitenburg, *A Course in Constructive
  Algebra*, Springer Universitext, 1988, DOI 10.1007/978-1-4419-8640-5
  (the rationals as a constructive field; field laws).
* [LeanRat] Lean 4 core `v4.35.0-rc3`, `Init/Data/Rat/Basic.lean` and
  `Init/Data/Rat/Lemmas.lean` (the `Rat` structure, `Rat.mk'`,
  `Rat.normalize`, `Rat.ext`).
-/

namespace BoringMath

/-! ### Computable normalization machinery -/

-- Reference: [LeanRat], `Rat.normalize.dvd_num` in `Init/Data/Rat/Basic.lean`
-- (gcd divides the numerator); [MRR], ch. on fields (reduction of fractions).
/-- The gcd of `|n|` and `d` divides `n` (computable proof). -/
theorem qdvd_num (n : Int) (d : Nat) : (↑(n.natAbs.gcd d) : Int) ∣ n :=
  Rat.normalize.dvd_num rfl

-- Reference: [LeanRat], `Rat.normalize.dvd_den` in `Init/Data/Rat/Basic.lean`.
/-- The gcd of `|n|` and `d` divides `d` (computable proof). -/
theorem qdvd_den (n : Int) (d : Nat) : n.natAbs.gcd d ∣ d := Rat.normalize.dvd_den rfl

-- Reference: [LeanRat], `Int.natAbs_eq`, `Int.natCast_ediv`,
-- `Int.neg_ediv_of_dvd` in `Init/Data/Int/*`; avoids the choice-tainted
-- `Int.natAbs_ediv_of_dvd`.
/-- Constructive replacement for `Int.natAbs_ediv_of_dvd`: if `↑g ∣ a` then
`(a / ↑g).natAbs = a.natAbs / g`. -/
theorem qNatAbs_ediv (a : Int) (g : Nat) (h : (↑g : Int) ∣ a) :
    (a / ↑g).natAbs = a.natAbs / g := by
  rcases Int.natAbs_eq a with e | e
  · exact Eq.trans (congrArg (fun x : Int => (x / ↑g).natAbs) e)
      (Eq.trans (congrArg Int.natAbs (Int.natCast_ediv a.natAbs g).symm) (Int.natAbs_natCast (a.natAbs / g)))
  · exact Eq.trans (congrArg (fun x : Int => (x / ↑g).natAbs) e)
      (Eq.trans (congrArg Int.natAbs (Int.neg_ediv_of_dvd (Int.dvd_neg.1 (Eq.subst e h))))
        (Eq.trans (Int.natAbs_neg (↑(a.natAbs) / ↑g))
          (Eq.trans (congrArg Int.natAbs (Int.natCast_ediv a.natAbs g).symm)
            (Int.natAbs_natCast (a.natAbs / g)))))

-- Reference: [MRR], ch. on fields (a fraction divided by its gcd is reduced);
-- [LeanRat], `Nat.coprime_div_gcd_div_gcd` in `Init/Data/Nat/Coprime.lean`.
/-- The `reduced` field of `qmk`, proved constructively (this is where
`Rat.normalize.reduced` picks up `Classical.choice`). -/
theorem qreduced (n : Int) (d : Nat) (hd : d ≠ 0) :
    ((n.divExact (n.natAbs.gcd d) (qdvd_num n d)).natAbs).Coprime
      (d.divExact (n.natAbs.gcd d) (qdvd_den n d)) := by
  have h1 : n.divExact (n.natAbs.gcd d) (qdvd_num n d) = n / ↑(n.natAbs.gcd d) :=
    Int.divExact_eq_ediv (qdvd_num n d)
  have h2 : d.divExact (n.natAbs.gcd d) (qdvd_den n d) = d / n.natAbs.gcd d :=
    Nat.divExact_eq_div (qdvd_den n d)
  have h3 : (n / ↑(n.natAbs.gcd d)).natAbs = n.natAbs / n.natAbs.gcd d :=
    qNatAbs_ediv n _ (qdvd_num n d)
  have hfin : (n.natAbs / n.natAbs.gcd d).Coprime (d / n.natAbs.gcd d) :=
    Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_right n.natAbs (Nat.pos_of_ne_zero hd))
  exact Eq.mpr
    (Eq.trans (congrArg (fun x : Int => x.natAbs.Coprime (d.divExact (n.natAbs.gcd d) (qdvd_den n d))) h1)
      (Eq.trans (congrArg (fun y : Nat => (n / ↑(n.natAbs.gcd d)).natAbs.Coprime y) h2)
        (congrArg (fun z : Nat => z.Coprime (d / n.natAbs.gcd d)) h3)))
    hfin

-- Reference: [LeanRat], `Rat.normalize.den_nz` in `Init/Data/Rat/Basic.lean`.
/-- The normalized denominator is nonzero (computable proof). -/
theorem qden_nz (n : Int) (d : Nat) (hd : d ≠ 0) :
    d.divExact (n.natAbs.gcd d) (qdvd_den n d) ≠ 0 :=
  Eq.mpr (congrArg (fun x : Nat => x ≠ 0) (Nat.divExact_eq_div (qdvd_den n d)))
    (Rat.normalize.den_nz hd rfl)

-- Reference: [MRR], ch. on fields (construction of a fraction from numerator
-- and positive denominator); [LeanRat], `Rat.mk'`.
/-- Computable smart constructor: `qmk n d` is the reduced fraction `n / d`
for `d ≠ 0`, built from `Rat.mk'`, `Nat.gcd` and `divExact` only. -/
def qmk (n : Int) (d : Nat) (hd : d ≠ 0) : Rat :=
  Rat.mk' (n.divExact (n.natAbs.gcd d) (qdvd_num n d))
          (d.divExact (n.natAbs.gcd d) (qdvd_den n d))
          (qden_nz n d hd) (qreduced n d hd)

-- Reference: [LeanRat], `Rat.num` (structure projection); primitive
-- definitional lemma (`rfl`).
/-- Numerator projection of `qmk` (definitional peel). -/
theorem qmk_num (n : Int) (d : Nat) (hd : d ≠ 0) :
    (qmk n d hd).num = n.divExact (n.natAbs.gcd d) (qdvd_num n d) := rfl

-- Reference: [LeanRat], `Rat.den` (structure projection); primitive
-- definitional lemma (`rfl`).
/-- Denominator projection of `qmk` (definitional peel). -/
theorem qmk_den (n : Int) (d : Nat) (hd : d ≠ 0) :
    (qmk n d hd).den = d.divExact (n.natAbs.gcd d) (qdvd_den n d) := rfl

-- Reference: [LeanRat], `Int.divExact_eq_ediv`, `Int.ediv_mul_cancel`.
/-- Multiplying the exact quotient back by the divisor (numerator). -/
theorem qdivExact_num_mul (n : Int) (g : Nat) (h : (↑g : Int) ∣ n) :
    n.divExact g h * ↑g = n :=
  Eq.trans (congrArg (fun x : Int => x * ↑g) (Int.divExact_eq_ediv h)) (Int.ediv_mul_cancel h)

-- Reference: [LeanRat], `Int.natCast_ediv`, `Nat.div_mul_cancel`.
/-- Multiplying the exact quotient back by the divisor (denominator, cast). -/
theorem qdivExact_den_mul (d g : Nat) (h : g ∣ d) : (d.divExact g h : Int) * ↑g = ↑d :=
  Eq.trans (congrArg (fun x : Nat => (x : Int) * ↑g) (Nat.divExact_eq_div h))
    (Eq.trans (Int.natCast_mul (d / g) g).symm
      (congrArg (fun x : Nat => (x : Int)) (Nat.div_mul_cancel h)))

-- Reference: [LeanRat], `Nat.div_mul_cancel`.
/-- Nat-level version of `qdivExact_den_mul`. -/
theorem qdivExact_den_mul_nat (d g : Nat) (h : g ∣ d) : d.divExact g h * g = d :=
  Eq.trans (congrArg (fun x : Nat => x * g) (Nat.divExact_eq_div h)) (Nat.div_mul_cancel h)

-- Reference: [LeanRat], `Nat.divExact_eq_div`, `Int.natCast_mul`,
-- `Nat.div_mul_cancel` (peel: a cast product with a `divExact` factor
-- collapses to the cast product of the divisors).
/-- `↑(x * (d.divExact g h)) * ↑g = ↑x * ↑d` (peel used by the field laws). -/
theorem cast_mul_den_gcd (x d g : Nat) (h : g ∣ d) :
    (↑(x * d.divExact g h) : Int) * ↑g = (↑x : Int) * ↑d :=
  Eq.trans (congrArg (fun y : Nat => (↑(x * y) : Int) * ↑g) (Nat.divExact_eq_div h))
    (Eq.trans (Int.natCast_mul (x * (d / g)) g).symm
      (Eq.trans (congrArg (fun z : Nat => (↑z : Int)) (Nat.mul_assoc x (d / g) g))
        (Eq.trans (congrArg (fun w : Nat => (↑(x * w) : Int)) (Nat.div_mul_cancel h))
          (Int.natCast_mul x d))))

-- Reference: [LeanRat], `Nat.divExact_eq_div`, `Int.natCast_mul`,
-- `Nat.mul_comm`, `Nat.div_mul_cancel` (peel: `divExact` on the left of a
-- cast product, with the gcd on the right).
/-- `↑(d.divExact g h * c) * ↑g = ↑d * ↑c` (peel used by the field laws). -/
theorem cast_den_gcd_mul_comm (c d g : Nat) (h : g ∣ d) :
    (↑(d.divExact g h * c) : Int) * ↑g = (↑d : Int) * ↑c :=
  Eq.trans (congrArg (fun y : Nat => (↑(y * c) : Int) * ↑g) (Nat.divExact_eq_div h))
    (Eq.trans (Int.natCast_mul (d / g * c) g).symm
      (Eq.trans (congrArg (fun z : Nat => (↑z : Int)) (Nat.mul_assoc (d / g) c g))
        (Eq.trans (congrArg (fun w : Nat => (↑((d / g) * w) : Int)) (Nat.mul_comm c g))
          (Eq.trans (congrArg (fun v : Nat => (↑v : Int)) ((Nat.mul_assoc (d / g) g c).symm))
            (Eq.trans (congrArg (fun u : Nat => (↑(u * c) : Int)) (Nat.div_mul_cancel h))
              (Int.natCast_mul d c))))))

-- Reference: [LeanRat], `Nat.gcd_pos_of_pos_right`, `Int.ofNat_ne_zero`.
/-- The gcd of `|n|` and a nonzero `d` is positive (computable). -/
theorem qgcd_pos {n : Int} {d : Nat} (hd : d ≠ 0) : 0 < n.natAbs.gcd d :=
  Nat.gcd_pos_of_pos_right n.natAbs (Nat.pos_of_ne_zero hd)

-- Reference: [LeanRat], `Int.ofNat_ne_zero`.
/-- The cast of the gcd of `|n|` and a nonzero `d` is a nonzero integer. -/
theorem qgcd_ne_zero {n : Int} {d : Nat} (hd : d ≠ 0) : (↑(n.natAbs.gcd d) : Int) ≠ 0 :=
  Int.ofNat_ne_zero.2 (Nat.ne_of_gt (qgcd_pos hd))

-- Reference: [MRR], ch. on rings (commutativity/associativity of `*`);
-- [LeanRat], `Int.mul_comm`, `Int.mul_assoc`.
/-- Middle-factor commutation for integer multiplication. -/
theorem qmul_comm_assoc (a b c : Int) : a * (b * c) = (a * c) * b :=
  Eq.trans (congrArg (fun x : Int => a * x) (Int.mul_comm b c)) (Int.mul_assoc a c b).symm

-- Reference: [MRR], ch. on rings; [LeanRat], `Int.mul_assoc`, `Int.mul_comm`.
/-- Pairwise regrouping of a four-factor integer product. -/
theorem qmul_assoc_swap (a b c d : Int) : a * b * (c * d) = (a * c) * (b * d) := by
  calc a * b * (c * d) = a * (b * (c * d)) := Int.mul_assoc a b (c * d)
    _ = (a * (c * d)) * b := qmul_comm_assoc a b (c * d)
    _ = ((a * c) * d) * b := congrArg (fun x : Int => x * b) (Int.mul_assoc a c d).symm
    _ = (a * c) * (d * b) := Int.mul_assoc (a * c) d b
    _ = (a * c) * (b * d) := congrArg (fun x : Int => (a * c) * x) (Int.mul_comm d b)

-- Reference: [MRR], ch. on rings; corollary of `qmul_assoc_swap`.
/-- Pairwise regrouping of a four-factor integer product, other diagonal. -/
theorem qmul_assoc_swap' (a b c d : Int) : a * b * (c * d) = (a * d) * (b * c) :=
  Eq.trans (congrArg (fun x : Int => a * b * x) (Int.mul_comm c d)) (qmul_assoc_swap a b d c)

-- Reference: [MRR], ch. on rings; [LeanRat], `Int.eq_of_mul_eq_mul_right`.
/-- Cancel a nonzero right factor in an integer equation (term-level wrapper
so that `refine qcancel hK ?_` multiplies the goal by `K`). -/
theorem qcancel {A B K : Int} (hK : K ≠ 0) (h : A * K = B * K) : A = B :=
  Int.eq_of_mul_eq_mul_right hK h

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

/-! ### Equality of rationals via cross-multiplication -/

-- Reference: [LeanRat], `qadd_num` composed with `qdivExact_num_mul`
-- (peel of the numerator-times-gcd step used throughout the field laws).
/-- `(qadd a b).num` times the gcd cast equals the un-normalized numerator. -/
theorem qadd_num_gcd_mul (a b : Rat) :
    (qadd a b).num * ↑((a.num * ↑b.den + b.num * ↑a.den).natAbs.gcd (a.den * b.den)) =
      a.num * ↑b.den + b.num * ↑a.den :=
  Eq.trans (congrArg (fun x : Int => x * ↑((a.num * ↑b.den + b.num * ↑a.den).natAbs.gcd (a.den * b.den)))
      (qadd_num a b))
    (qdivExact_num_mul _ _ (qdvd_num _ _))

-- Reference: [LeanRat], `qadd_den` composed with `qdivExact_den_mul`
-- (peel of the denominator-times-gcd step used throughout the field laws).
/-- `(qadd a b).den` cast times the gcd cast equals the denominator product. -/
theorem qadd_den_gcd_mul (a b : Rat) :
    ((qadd a b).den : Int) * ↑((a.num * ↑b.den + b.num * ↑a.den).natAbs.gcd (a.den * b.den)) =
      (↑(a.den * b.den) : Int) :=
  Eq.trans (congrArg (fun x : Nat => (x : Int) * ↑((a.num * ↑b.den + b.num * ↑a.den).natAbs.gcd
      (a.den * b.den))) (qadd_den a b))
    (qdivExact_den_mul _ _ (qdvd_den _ _))

-- Reference: [LeanRat], `qmul_num` composed with `qdivExact_num_mul`
-- (peel of the numerator-times-gcd step used throughout the field laws).
/-- `(qmul a b).num` times the gcd cast equals the un-normalized numerator. -/
theorem qmul_num_gcd_mul (a b : Rat) :
    (qmul a b).num * ↑((a.num * b.num).natAbs.gcd (a.den * b.den)) = a.num * b.num :=
  Eq.trans (congrArg (fun x : Int => x * ↑((a.num * b.num).natAbs.gcd (a.den * b.den))) (qmul_num a b))
    (qdivExact_num_mul _ _ (qdvd_num _ _))

-- Reference: [LeanRat], `qmul_den` composed with `qdivExact_den_mul`
-- (peel of the denominator-times-gcd step used throughout the field laws).
/-- `(qmul a b).den` cast times the gcd cast equals the denominator product. -/
theorem qmul_den_gcd_mul (a b : Rat) :
    ((qmul a b).den : Int) * ↑((a.num * b.num).natAbs.gcd (a.den * b.den)) =
      (↑(a.den * b.den) : Int) :=
  Eq.trans (congrArg (fun x : Nat => (x : Int) * ↑((a.num * b.num).natAbs.gcd (a.den * b.den)))
      (qmul_den a b))
    (qdivExact_den_mul _ _ (qdvd_den _ _))

-- Reference: [LeanRat], `Int.natAbs_zero`, `Nat.gcd_zero_left`,
-- `Nat.Coprime.gcd_eq_one`; [MRR], ch. on fields (a fraction with zero
-- numerator has denominator 1 in reduced form).
/-- A rational with zero numerator has denominator 1 (peel). -/
theorem qden_eq_one_of_num_zero (a : Rat) (h : a.num = 0) : a.den = 1 :=
  Eq.trans (Nat.gcd_zero_left a.den).symm
    (Eq.mp (Eq.trans (congrArg (fun x : Int => x.natAbs.Coprime a.den) h)
        (congrArg (fun x : Nat => x.Coprime a.den) Int.natAbs_zero)) a.reduced).gcd_eq_one

-- Reference: [MRR], ch. on fields (a fraction with zero numerator is zero);
-- [LeanRat], `Rat.ext`, `Nat.gcd_zero_left`.
/-- A rational with zero numerator is zero. -/
theorem qnum_eq_zero (a : Rat) (h : a.num = 0) : a = 0 :=
  Rat.ext (Eq.trans h Rat.zero_num.symm)
    (Eq.trans (qden_eq_one_of_num_zero a h) Rat.zero_den.symm)

-- Reference: [MRR], ch. on fields; [LeanRat], `Rat.zero_num`.
/-- A rational is zero iff its numerator is zero. -/
theorem qnum_ne_zero (a : Rat) : a ≠ 0 ↔ a.num ≠ 0 :=
  ⟨fun h hn => h (qnum_eq_zero a hn),
    fun hn h => hn (Eq.trans (congrArg Rat.num h) Rat.zero_num)⟩

-- Reference: [MRR], ch. on fields (uniqueness of the reduced form);
-- [LeanRat], `Int.eq_of_mul_eq_mul_left`, `Int.ofNat_inj`, `Nat.gcd_zero_left`.
/-- If two rationals have equal numerators and cross-multiplied denominators,
their denominators agree. -/
theorem qden_eq_of_cross (a b : Rat) (hn : a.num = b.num)
    (h : a.num * ↑b.den = b.num * ↑a.den) : a.den = b.den := by
  rcases Int.lt_trichotomy a.num 0 with hlt | h0 | hgt
  · exact (Int.ofNat_inj.1 (Int.eq_of_mul_eq_mul_left (Int.ne_of_lt hlt)
      (Eq.subst (motive := fun x : Int => a.num * ↑b.den = x * ↑a.den) hn.symm h))).symm
  · exact Eq.trans (qden_eq_one_of_num_zero a h0)
      (qden_eq_one_of_num_zero b (Eq.trans hn.symm h0)).symm
  · exact (Int.ofNat_inj.1 (Int.eq_of_mul_eq_mul_left (Int.ne_of_gt hgt)
      (Eq.subst (motive := fun x : Int => a.num * ↑b.den = x * ↑a.den) hn.symm h))).symm

-- Reference: [MRR], ch. on fields (uniqueness of the reduced form: equal
-- cross-products give equal fractions); [LeanRat], `Int.natAbs_dvd_natAbs`,
-- `Nat.Coprime.dvd_of_dvd_mul_right`, `Nat.dvd_antisymm`,
-- `Int.natAbs_eq_natAbs_iff`.
/-- Cross-multiplication characterizes equality of rationals (constructive
uniqueness of the reduced form). -/
theorem qeq_of_cross (a b : Rat) (h : a.num * ↑b.den = b.num * ↑a.den) : a = b := by
  have e1 : a.num.natAbs ∣ (b.num * ↑a.den).natAbs :=
    Int.natAbs_dvd_natAbs.2 ⟨↑b.den, h.symm⟩
  have e1' : a.num.natAbs ∣ b.num.natAbs * a.den :=
    Eq.mp (congrArg (fun x : Nat => a.num.natAbs ∣ x)
      (Eq.trans (Int.natAbs_mul b.num (↑a.den))
        (congrArg (fun y : Nat => b.num.natAbs * y) (Int.natAbs_natCast a.den)))) e1
  have d1 : a.num.natAbs ∣ b.num.natAbs := a.reduced.dvd_of_dvd_mul_right e1'
  have e2 : b.num.natAbs ∣ (a.num * ↑b.den).natAbs :=
    Int.natAbs_dvd_natAbs.2 ⟨↑a.den, h⟩
  have e2' : b.num.natAbs ∣ a.num.natAbs * b.den :=
    Eq.mp (congrArg (fun x : Nat => b.num.natAbs ∣ x)
      (Eq.trans (Int.natAbs_mul a.num (↑b.den))
        (congrArg (fun y : Nat => a.num.natAbs * y) (Int.natAbs_natCast b.den)))) e2
  have d2 : b.num.natAbs ∣ a.num.natAbs := b.reduced.dvd_of_dvd_mul_right e2'
  have hab : a.num.natAbs = b.num.natAbs := Nat.dvd_antisymm d1 d2
  rcases Int.natAbs_eq_natAbs_iff.1 hab with e | e
  · exact Rat.ext e (qden_eq_of_cross a b e h)
  · have hneg : b.num * ↑a.den = -(b.num * ↑b.den) :=
      Eq.trans h.symm (Eq.trans (congrArg (fun x : Int => x * ↑b.den) e) (Int.neg_mul b.num (↑b.den)))
    have h0 : b.num * (↑a.den + ↑b.den) = 0 :=
      Eq.trans (Int.mul_add b.num (↑a.den) (↑b.den))
        (Eq.trans (congrArg (fun x : Int => x + b.num * ↑b.den) hneg)
          (Eq.trans (Int.add_comm (-(b.num * ↑b.den)) (b.num * ↑b.den))
            (Eq.trans (Int.sub_eq_add_neg (a := b.num * ↑b.den) (b := b.num * ↑b.den)).symm
              (Int.sub_self (b.num * ↑b.den)))))
    have hsum : (↑a.den + ↑b.den : Int) ≠ 0 := by
      intro hs
      have hs' : (↑(a.den + b.den) : Int) = 0 :=
        Eq.subst (motive := fun x : Int => x = 0) (Int.natCast_add a.den b.den).symm hs
      have hz : a.den = 0 := (Nat.add_eq_zero_iff.1 (Int.ofNat_eq_zero.1 hs')).1
      exact Nat.lt_irrefl 0 (Eq.subst (motive := fun x : Nat => 0 < x) hz a.den_pos)
    rcases Int.mul_eq_zero.1 h0 with e0 | e0
    · have e' : a.num = b.num :=
        Eq.trans e (Eq.trans (congrArg (fun x : Int => -x) e0) (Eq.trans Int.neg_zero e0.symm))
      exact Rat.ext e' (qden_eq_of_cross a b e' h)
    · exfalso; exact hsum e0

-- Reference: [MRR], ch. on fields (fractions `a/b = c/d` iff `a*d = c*b`).
/-- Equality of rationals is cross-multiplication. -/
theorem qeq_iff (a b : Rat) : a = b ↔ a.num * ↑b.den = b.num * ↑a.den :=
  ⟨fun h => Eq.mpr (congrArg (fun x : Rat => x.num * ↑b.den = b.num * ↑x.den) h) rfl, qeq_of_cross a b⟩

-- Reference: [MRR], ch. on fields; [LeanRat], `Int.eq_of_mul_eq_mul_right`.
/-- Cross-multiplication form for `qmk`, from `n * d' = n' * d` to the
cross-equation of the reduced fractions. -/
theorem qmk_cross (n : Int) (d : Nat) (hd : d ≠ 0) (n' : Int) (d' : Nat) (hd' : d' ≠ 0)
    (h : n * ↑d' = n' * ↑d) :
    (qmk n d hd).num * ↑(qmk n' d' hd').den = (qmk n' d' hd').num * ↑(qmk n d hd).den := by
  have hA := qdivExact_num_mul n (n.natAbs.gcd d) (qdvd_num n d)
  have hB := qdivExact_den_mul d (n.natAbs.gcd d) (qdvd_den n d)
  have hA' := qdivExact_num_mul n' (n'.natAbs.gcd d') (qdvd_num n' d')
  have hB' := qdivExact_den_mul d' (n'.natAbs.gcd d') (qdvd_den n' d')
  have hg : (↑(n.natAbs.gcd d) : Int) * ↑(n'.natAbs.gcd d') ≠ 0 :=
    Int.mul_ne_zero (qgcd_ne_zero hd) (qgcd_ne_zero hd')
  have key : (n.divExact (n.natAbs.gcd d) (qdvd_num n d)) *
        ↑(d'.divExact (n'.natAbs.gcd d') (qdvd_den n' d')) *
        (↑(n.natAbs.gcd d) * ↑(n'.natAbs.gcd d')) =
      (n'.divExact (n'.natAbs.gcd d') (qdvd_num n' d')) *
        ↑(d.divExact (n.natAbs.gcd d) (qdvd_den n d)) *
        (↑(n.natAbs.gcd d) * ↑(n'.natAbs.gcd d')) :=
    Eq.trans
      (Eq.trans (qmul_assoc_swap (n.divExact (n.natAbs.gcd d) (qdvd_num n d))
            (↑(d'.divExact (n'.natAbs.gcd d') (qdvd_den n' d')))
            (↑(n.natAbs.gcd d)) (↑(n'.natAbs.gcd d')))
        (Eq.trans (congrArg (fun t : Int => t * (↑(d'.divExact (n'.natAbs.gcd d') (qdvd_den n' d')) *
            ↑(n'.natAbs.gcd d'))) hA)
          (Eq.trans (congrArg (fun t : Int => n * t) hB') h)))
      (Eq.trans (qmul_assoc_swap' (n'.divExact (n'.natAbs.gcd d') (qdvd_num n' d'))
            (↑(d.divExact (n.natAbs.gcd d) (qdvd_den n d)))
            (↑(n.natAbs.gcd d)) (↑(n'.natAbs.gcd d')))
        (Eq.trans (congrArg (fun t : Int => t * (↑(d.divExact (n.natAbs.gcd d) (qdvd_den n d)) *
            ↑(n.natAbs.gcd d))) hA')
          (congrArg (fun t : Int => n' * t) hB))).symm
  refine Eq.mpr ?_ (Int.eq_of_mul_eq_mul_right hg key)
  exact Eq.trans
    (congrArg (fun x : Int => x * ↑(qmk n' d' hd').den = (qmk n' d' hd').num * ↑(qmk n d hd).den)
      (qmk_num n d hd))
    (Eq.trans
      (congrArg (fun y : Nat => (n.divExact (n.natAbs.gcd d) (qdvd_num n d)) * ↑y =
        (qmk n' d' hd').num * ↑(qmk n d hd).den) (qmk_den n' d' hd'))
      (Eq.trans
        (congrArg (fun z : Int => (n.divExact (n.natAbs.gcd d) (qdvd_num n d)) *
            ↑(d'.divExact (n'.natAbs.gcd d') (qdvd_den n' d')) = z * ↑(qmk n d hd).den)
          (qmk_num n' d' hd'))
        (congrArg (fun w : Nat => (n.divExact (n.natAbs.gcd d) (qdvd_num n d)) *
            ↑(d'.divExact (n'.natAbs.gcd d') (qdvd_den n' d')) =
          (n'.divExact (n'.natAbs.gcd d') (qdvd_num n' d')) * ↑w) (qmk_den n d hd))))

-- Reference: [MRR], ch. on fields; [LeanRat], `Int.eq_of_mul_eq_mul_right`.
/-- Cross-multiplication form for `qmk`, backward direction: from
`qmk n d = qmk n' d'` to `n * d' = n' * d`. -/
theorem qmk_int_of_eq (n : Int) (d : Nat) (hd : d ≠ 0) (n' : Int) (d' : Nat) (hd' : d' ≠ 0)
    (h : qmk n d hd = qmk n' d' hd') : n * ↑d' = n' * ↑d := by
  have hc : (qmk n d hd).num * ↑(qmk n' d' hd').den = (qmk n' d' hd').num * ↑(qmk n d hd).den :=
    Eq.mpr (congrArg (fun x : Rat => x.num * ↑(qmk n' d' hd').den = (qmk n' d' hd').num * ↑x.den) h) rfl
  have hA := qdivExact_num_mul n (n.natAbs.gcd d) (qdvd_num n d)
  have hB := qdivExact_den_mul d (n.natAbs.gcd d) (qdvd_den n d)
  have hA' := qdivExact_num_mul n' (n'.natAbs.gcd d') (qdvd_num n' d')
  have hB' := qdivExact_den_mul d' (n'.natAbs.gcd d') (qdvd_den n' d')
  have hc' : (n.divExact (n.natAbs.gcd d) (qdvd_num n d)) *
      ↑(d'.divExact (n'.natAbs.gcd d') (qdvd_den n' d')) =
      (n'.divExact (n'.natAbs.gcd d') (qdvd_num n' d')) *
      ↑(d.divExact (n.natAbs.gcd d) (qdvd_den n d)) :=
    Eq.mpr
      (Eq.trans
        (congrArg (fun x : Int => x * ↑(qmk n' d' hd').den = (qmk n' d' hd').num * ↑(qmk n d hd).den)
          (qmk_num n d hd))
        (Eq.trans
          (congrArg (fun y : Nat => (n.divExact (n.natAbs.gcd d) (qdvd_num n d)) * ↑y =
            (qmk n' d' hd').num * ↑(qmk n d hd).den) (qmk_den n' d' hd'))
          (Eq.trans
            (congrArg (fun z : Int => (n.divExact (n.natAbs.gcd d) (qdvd_num n d)) *
                ↑(d'.divExact (n'.natAbs.gcd d') (qdvd_den n' d')) = z * ↑(qmk n d hd).den)
              (qmk_num n' d' hd'))
            (congrArg (fun w : Nat => (n.divExact (n.natAbs.gcd d) (qdvd_num n d)) *
                ↑(d'.divExact (n'.natAbs.gcd d') (qdvd_den n' d')) =
              (n'.divExact (n'.natAbs.gcd d') (qdvd_num n' d')) * ↑w) (qmk_den n d hd)))))
      hc
  calc n * ↑d'
      = (n.divExact (n.natAbs.gcd d) (qdvd_num n d) * ↑(n.natAbs.gcd d)) *
        (↑(d'.divExact (n'.natAbs.gcd d') (qdvd_den n' d')) * ↑(n'.natAbs.gcd d')) :=
        (Eq.trans (congrArg (fun t : Int => t * (↑(d'.divExact (n'.natAbs.gcd d') (qdvd_den n' d')) *
          ↑(n'.natAbs.gcd d'))) hA) (congrArg (fun t : Int => n * t) hB')).symm
    _ = n.divExact (n.natAbs.gcd d) (qdvd_num n d) *
          ↑(d'.divExact (n'.natAbs.gcd d') (qdvd_den n' d')) *
          (↑(n.natAbs.gcd d) * ↑(n'.natAbs.gcd d')) := qmul_assoc_swap _ _ _ _
    _ = n'.divExact (n'.natAbs.gcd d') (qdvd_num n' d') *
          ↑(d.divExact (n.natAbs.gcd d) (qdvd_den n d)) *
          (↑(n.natAbs.gcd d) * ↑(n'.natAbs.gcd d')) :=
        congrArg (fun t : Int => t * (↑(n.natAbs.gcd d) * ↑(n'.natAbs.gcd d'))) hc'
    _ = (n'.divExact (n'.natAbs.gcd d') (qdvd_num n' d') * ↑(n'.natAbs.gcd d')) *
        (↑(d.divExact (n.natAbs.gcd d) (qdvd_den n d)) * ↑(n.natAbs.gcd d)) :=
        qmul_assoc_swap' _ _ _ _
    _ = n' * ↑d :=
        Eq.trans (congrArg (fun t : Int => t * (↑(d.divExact (n.natAbs.gcd d) (qdvd_den n d)) *
          ↑(n.natAbs.gcd d))) hA') (congrArg (fun t : Int => n' * t) hB)

-- Reference: [MRR], ch. on fields (fractions `n/d = n'/d'` iff `n*d' = n'*d`).
/-- Cross-multiplication characterizes equality of `qmk` fractions. -/
theorem qmk_eq_iff (n : Int) (d : Nat) (hd : d ≠ 0) (n' : Int) (d' : Nat) (hd' : d' ≠ 0) :
    qmk n d hd = qmk n' d' hd' ↔ n * ↑d' = n' * ↑d :=
  ⟨qmk_int_of_eq n d hd n' d' hd', fun h => qeq_of_cross _ _ (qmk_cross n d hd n' d' hd' h)⟩

-- Reference: [MRR], ch. on fields; corollary of `qmk_eq_iff`.
/-- `qmk` respects equality of numerator and denominator. -/
theorem qmk_congr (n : Int) (d : Nat) (hd : d ≠ 0) (n' : Int) (d' : Nat) (hd' : d' ≠ 0)
    (h : n = n') (e : d = d') : qmk n d hd = qmk n' d' hd' :=
  (qmk_eq_iff n d hd n' d' hd').2
    (Eq.trans (congrArg (fun x : Int => x * ↑d') h) (congrArg (fun y : Nat => n' * ↑y) e.symm))

-- Reference: [MRR], ch. on fields (a reduced fraction equals itself);
-- [LeanRat], `qeq_iff` machinery above.
/-- `qmk` of the components of `a` is `a`. -/
theorem qmk_self (a : Rat) : qmk a.num a.den a.den_nz = a := by
  refine (qeq_iff _ _).mpr ?_
  exact Eq.mpr (Eq.trans
    (congrArg (fun x : Int => x * ↑a.den = a.num * ↑(qmk a.num a.den a.den_nz).den)
      (qmk_num a.num a.den a.den_nz))
    (Eq.trans
      (congrArg (fun y : Nat => (a.num.divExact (a.num.natAbs.gcd a.den) (qdvd_num a.num a.den)) * ↑a.den =
        a.num * ↑y) (qmk_den a.num a.den a.den_nz))
      (Eq.trans
        (congrArg (fun z : Int => (a.num.divExact (a.num.natAbs.gcd a.den) (qdvd_num a.num a.den)) * z =
          a.num * ↑(a.den.divExact (a.num.natAbs.gcd a.den) (qdvd_den a.num a.den)))
          ((qdivExact_den_mul a.den (a.num.natAbs.gcd a.den) (qdvd_den a.num a.den)).symm))
        (Eq.trans
          (congrArg (fun w : Int => w = a.num * ↑(a.den.divExact (a.num.natAbs.gcd a.den)
              (qdvd_den a.num a.den)))
            (qmul_comm_assoc (a.num.divExact (a.num.natAbs.gcd a.den) (qdvd_num a.num a.den))
              (↑(a.den.divExact (a.num.natAbs.gcd a.den) (qdvd_den a.num a.den)))
              (↑(a.num.natAbs.gcd a.den))))
          (congrArg (fun v : Int => v * ↑(a.den.divExact (a.num.natAbs.gcd a.den)
              (qdvd_den a.num a.den)) = a.num * ↑(a.den.divExact (a.num.natAbs.gcd a.den)
              (qdvd_den a.num a.den)))
            (qdivExact_num_mul a.num (a.num.natAbs.gcd a.den) (qdvd_num a.num a.den))))))) rfl

-- Reference: [MRR], ch. on fields (zero fraction); [LeanRat], `Int.zero_ediv`.
/-- `qmk 0 d` is zero. -/
theorem qmk_zero (d : Nat) (hd : d ≠ 0) : qmk 0 d hd = 0 :=
  Eq.trans ((qmk_eq_iff 0 d hd 0 1 Nat.one_ne_zero).2
    (Eq.trans (Int.zero_mul (↑(1 : Nat) : Int)) (Int.zero_mul (↑d : Int)).symm))
    (Eq.trans
      (qmk_congr (0 : Rat).num (0 : Rat).den (0 : Rat).den_nz 0 1 Nat.one_ne_zero
        Rat.zero_num Rat.zero_den).symm (qmk_self 0))

-- Reference: [MRR], ch. on fields (one as a fraction); [LeanRat], `Rat.one_num`.
/-- `qmk 1 1` is one. -/
theorem qmk_one (hd : (1 : Nat) ≠ 0) : qmk 1 1 hd = 1 :=
  Eq.trans
    (qmk_congr (1 : Rat).num (1 : Rat).den (1 : Rat).den_nz 1 1 Nat.one_ne_zero
      Rat.one_num Rat.one_den).symm (qmk_self 1)

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

/-! ### Axiom lint trailer: every declaration must be CLEAN
(only `propext` / `Quot.sound`; no classical choice, no conjecture axioms). -/

#lint_axioms BoringMath.qdvd_num
#lint_axioms BoringMath.qdvd_den
#lint_axioms BoringMath.qNatAbs_ediv
#lint_axioms BoringMath.qreduced
#lint_axioms BoringMath.qden_nz
#lint_axioms BoringMath.qmk
#lint_axioms BoringMath.qmk_num
#lint_axioms BoringMath.qmk_den
#lint_axioms BoringMath.qdivExact_num_mul
#lint_axioms BoringMath.qdivExact_den_mul
#lint_axioms BoringMath.qdivExact_den_mul_nat
#lint_axioms BoringMath.qgcd_pos
#lint_axioms BoringMath.qgcd_ne_zero
#lint_axioms BoringMath.qmul_comm_assoc
#lint_axioms BoringMath.qmul_assoc_swap
#lint_axioms BoringMath.qmul_assoc_swap'
#lint_axioms BoringMath.qcancel
#lint_axioms BoringMath.qneg_reduced
#lint_axioms BoringMath.qneg
#lint_axioms BoringMath.qneg_num
#lint_axioms BoringMath.qneg_den
#lint_axioms BoringMath.qden_mul
#lint_axioms BoringMath.qadd
#lint_axioms BoringMath.qadd_num
#lint_axioms BoringMath.qadd_den
#lint_axioms BoringMath.qmul
#lint_axioms BoringMath.qmul_num
#lint_axioms BoringMath.qmul_den
#lint_axioms BoringMath.qsub
#lint_axioms BoringMath.qsub_def
#lint_axioms BoringMath.qinv_den_nz
#lint_axioms BoringMath.qinv_reduced_neg
#lint_axioms BoringMath.qinv_reduced_pos
#lint_axioms BoringMath.qinv
#lint_axioms BoringMath.qmk'_num
#lint_axioms BoringMath.qmk'_den
#lint_axioms BoringMath.qinv_num_neg
#lint_axioms BoringMath.qinv_den_neg
#lint_axioms BoringMath.qinv_num_pos
#lint_axioms BoringMath.qinv_den_pos
#lint_axioms BoringMath.qdiv
#lint_axioms BoringMath.qdiv_def
#lint_axioms BoringMath.qnum_eq_zero
#lint_axioms BoringMath.qnum_ne_zero
#lint_axioms BoringMath.qden_eq_of_cross
#lint_axioms BoringMath.qeq_of_cross
#lint_axioms BoringMath.qeq_iff
#lint_axioms BoringMath.qmk_cross
#lint_axioms BoringMath.qmk_int_of_eq
#lint_axioms BoringMath.qmk_eq_iff
#lint_axioms BoringMath.qmk_congr
#lint_axioms BoringMath.qmk_self
#lint_axioms BoringMath.qmk_zero
#lint_axioms BoringMath.qmk_one
#lint_axioms BoringMath.qadd_assoc_int
#lint_axioms BoringMath.qmul_assoc_int
#lint_axioms BoringMath.mul_add_int
#lint_axioms BoringMath.qadd_comm
#lint_axioms BoringMath.qmul_comm
#lint_axioms BoringMath.qadd_zero
#lint_axioms BoringMath.qmul_one
#lint_axioms BoringMath.qadd_left_neg
#lint_axioms BoringMath.qadd_assoc
#lint_axioms BoringMath.qmul_assoc
#lint_axioms BoringMath.mul_add
#lint_axioms BoringMath.qmul_inv_cancel
