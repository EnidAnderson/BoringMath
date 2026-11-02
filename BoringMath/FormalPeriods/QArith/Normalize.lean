/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/

import Mathlib.Init

/-!
# Computable normalization machinery (`QArith`, part 1)

Piece 1 of `BoringMath.FormalPeriods.QArith`: the computable gcd/`divExact`
normalization machinery behind `qmk` (the constructive `reduced` and `den_nz`
proofs, replacing the choice-tainted fields of `Rat.normalize`), plus the
integer peels (`divExact` recombination, gcd positivity, cancellation,
four-factor regrouping) used throughout the field laws.
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

end BoringMath
