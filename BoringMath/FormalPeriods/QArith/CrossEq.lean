/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/

import Mathlib.Init
import BoringMath.FormalPeriods.QArith.Normalize
import BoringMath.FormalPeriods.QArith.Ops

/-!
# Equality of rationals via cross-multiplication (`QArith`, part 3)

Piece 3 of `BoringMath.FormalPeriods.QArith`: the gcd-times-component peels
(`qadd_num_gcd_mul`, ...), the zero-numerator lemmas, cross-multiplication
characterization of equality (`qeq_of_cross`, `qeq_iff`), and the `qmk`
cross-multiplication API (`qmk_cross`, `qmk_eq_iff`, `qmk_congr`, `qmk_self`,
`qmk_zero`, `qmk_one`).
-/

namespace BoringMath

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

end BoringMath
