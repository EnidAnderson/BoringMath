/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Data.ZMod.Basic
import BoringMath.GroupTheory.Simple.Classification

/-!
# The order of `PSL(n, ZMod p)` — the roots-of-unity gcd formula

Ticket **#283** (= **#235** detailed): over the prime field `F_p`, the group of
`n`-th roots of unity has order `gcd n (p - 1)` (because `F_pˣ` is cyclic of
order `p - 1`), which turns the cardinality split
`card_PSL_finiteField_mul_card_rootsOfUnity` (in
`BoringMath.GroupTheory.Simple.Classification`) into the full order formula

  `|PSL(n, F_p)| * gcd n (p - 1) = (∏_{i < n} (p^n - p^i)) / (p - 1)`.

The gcd formula itself is proved below (via the `n`-torsion count in the
cyclic group `(ZMod p)ˣ`, `IsCyclic.card_pow_eq_one_eq_gcd`); the order formula
below it is proved from it.

## References
* [Wilson] R. A. Wilson, *The Finite Simple Groups*, Springer GTM 251, 2009,
  ch. 5 (the order of `PSL(n, q)`: `(1 / ((q-1) gcd(n, q-1))) ∏ (q^n - q^i)`).
* [ATLAS] J. H. Conway et al., *ATLAS of Finite Groups*, OUP 1985, p. xvi.
* mathlib pin v4.35.0-rc3: `rootsOfUnityEquivNthRoots`, `Polynomial.card_nthRoots`,
  `ZMod.pow_card_sub_one_eq_one`, `FiniteField.splits_X_pow_card_sub_X` /
  `roots_X_pow_card_sub_X`, `IsCyclic (ZMod p)ˣ` (`Mathlib/RingTheory/ZMod/UnitsCyclic.lean`),
  `Matrix.card_SL_field` (via `Classification.lean`).
-/

namespace BoringMath

open Matrix
open scoped MatrixGroups

-- Reference: [Dummit–Foote], Ch. 2, §5 (in a cyclic group of order `m` with
-- generator `g`, the solutions of `x ^ n = 1` are exactly the powers of
-- `g ^ (m / gcd m n)`, hence number `gcd m n`); mathlib pin v4.35.0-rc3:
-- `IsCyclic.exists_generator`, `orderOf_eq_card_of_forall_mem_zpowers`,
-- `Nat.card_zpowers`, `orderOf_pow`, `Nat.coprime_div_gcd_div_gcd`.
/-- In a finite cyclic group of order `m`, exactly `gcd m n` elements satisfy
`x ^ n = 1`. -/
theorem IsCyclic.card_pow_eq_one_eq_gcd {G : Type*} [Group G] [Fintype G] [IsCyclic G]
    (n : ℕ) : Nat.card {x : G // x ^ n = 1} = Nat.gcd (Fintype.card G) n := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  have hm : orderOf g = Fintype.card G :=
    (orderOf_eq_card_of_forall_mem_zpowers hg).trans Nat.card_eq_fintype_card
  have hmpos : 0 < Fintype.card G := Fintype.card_pos
  have hdpos : 0 < Nat.gcd (Fintype.card G) n := Nat.gcd_pos_of_pos_left n hmpos
  have hdm : Nat.gcd (Fintype.card G) n ∣ Fintype.card G := Nat.gcd_dvd_left _ _
  have hdn : Nat.gcd (Fintype.card G) n ∣ n := Nat.gcd_dvd_right _ _
  -- `(m / d) * n = m * (n / d)` with `d = gcd m n`.
  have hmn : (Fintype.card G / Nat.gcd (Fintype.card G) n) * n =
      Fintype.card G * (n / Nat.gcd (Fintype.card G) n) :=
    (congrArg ((Fintype.card G / Nat.gcd (Fintype.card G) n) * ·)
        ((Nat.div_mul_cancel hdn).symm.trans
          (Nat.mul_comm (n / Nat.gcd (Fintype.card G) n) (Nat.gcd (Fintype.card G) n)))).trans
      ((Nat.mul_assoc (Fintype.card G / Nat.gcd (Fintype.card G) n)
          (Nat.gcd (Fintype.card G) n) (n / Nat.gcd (Fintype.card G) n)).symm.trans
        (congrArg (· * (n / Nat.gcd (Fintype.card G) n)) (Nat.div_mul_cancel hdm)))
  -- The `n`-torsion is exactly `zpowers (g ^ (m / d))`.
  have hiff : ∀ x : G, x ^ n = 1 ↔
      x ∈ Subgroup.zpowers (g ^ (Fintype.card G / Nat.gcd (Fintype.card G) n)) := by
    intro x
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff x g).mp
      (mem_powers_iff_mem_zpowers.mpr (hg x))
    refine ⟨?_, ?_⟩
    · intro hxn
      have e1 : g ^ (k * n) = 1 :=
        ((pow_mul g k n).trans (congrArg (· ^ n) hk)).trans hxn
      have e2 : Fintype.card G ∣ k * n :=
        Eq.subst (motive := fun o => o ∣ k * n) hm (orderOf_dvd_iff_pow_eq_one.mpr e1)
      have hkn : k * n =
          Nat.gcd (Fintype.card G) n * (k * (n / Nat.gcd (Fintype.card G) n)) :=
        (congrArg (k * ·) ((Nat.div_mul_cancel hdn).symm.trans
            (Nat.mul_comm (n / Nat.gcd (Fintype.card G) n)
              (Nat.gcd (Fintype.card G) n)))).trans
          (Nat.mul_left_comm k (Nat.gcd (Fintype.card G) n)
            (n / Nat.gcd (Fintype.card G) n))
      have e3 : Fintype.card G ∣
          Nat.gcd (Fintype.card G) n * (k * (n / Nat.gcd (Fintype.card G) n)) :=
        Eq.subst (motive := fun t => Fintype.card G ∣ t) hkn e2
      have e4 : Fintype.card G / Nat.gcd (Fintype.card G) n ∣
          k * (n / Nat.gcd (Fintype.card G) n) :=
        (Nat.div_dvd_iff_dvd_mul hdm hdpos).mpr e3
      have e5 : Fintype.card G / Nat.gcd (Fintype.card G) n ∣ k :=
        Nat.Coprime.dvd_of_dvd_mul_right (Nat.coprime_div_gcd_div_gcd hdpos) e4
      have e6 : g ^ k =
          (g ^ (Fintype.card G / Nat.gcd (Fintype.card G) n)) ^
            (k / (Fintype.card G / Nat.gcd (Fintype.card G) n)) :=
        (congrArg (g ^ ·) ((Nat.mul_comm (Fintype.card G / Nat.gcd (Fintype.card G) n)
              (k / (Fintype.card G / Nat.gcd (Fintype.card G) n))).trans
            (Nat.div_mul_cancel e5)).symm).trans
          (pow_mul g (Fintype.card G / Nat.gcd (Fintype.card G) n)
            (k / (Fintype.card G / Nat.gcd (Fintype.card G) n)))
      exact Subgroup.mem_zpowers_iff.mpr
        ⟨↑(k / (Fintype.card G / Nat.gcd (Fintype.card G) n)),
          (zpow_natCast _ _).trans (e6.symm.trans hk)⟩
    · intro hxmem
      obtain ⟨l, hl⟩ := (Submonoid.mem_powers_iff x (g ^ (Fintype.card G /
          Nat.gcd (Fintype.card G) n))).mp (mem_powers_iff_mem_zpowers.mpr hxmem)
      have e1 : x ^ n =
          g ^ ((Fintype.card G / Nat.gcd (Fintype.card G) n) * (l * n)) :=
        ((congrArg (· ^ n) hl.symm).trans
          ((pow_mul (g ^ (Fintype.card G / Nat.gcd (Fintype.card G) n)) l n).symm)).trans
          (pow_mul g (Fintype.card G / Nat.gcd (Fintype.card G) n) (l * n)).symm
      have hexp : (Fintype.card G / Nat.gcd (Fintype.card G) n) * (l * n) =
          (l * (n / Nat.gcd (Fintype.card G) n)) * Fintype.card G :=
        ((Nat.mul_assoc (Fintype.card G / Nat.gcd (Fintype.card G) n) l n).symm.trans
          ((congrArg (· * n) (Nat.mul_comm (Fintype.card G / Nat.gcd (Fintype.card G) n) l)).trans
            ((Nat.mul_assoc l (Fintype.card G / Nat.gcd (Fintype.card G) n) n).trans
              ((congrArg (l * ·) hmn).trans
                ((congrArg (l * ·) (Nat.mul_comm (Fintype.card G)
                    (n / Nat.gcd (Fintype.card G) n))).trans
                  (Nat.mul_assoc l (n / Nat.gcd (Fintype.card G) n)
                    (Fintype.card G)).symm)))))
      have e2 : x ^ n = (g ^ Fintype.card G) ^ (l * (n / Nat.gcd (Fintype.card G) n)) :=
        (e1.trans (congrArg (g ^ ·) hexp)).trans
          ((congrArg (g ^ ·) (Nat.mul_comm (l * (n / Nat.gcd (Fintype.card G) n))
              (Fintype.card G))).trans
            (pow_mul g (Fintype.card G) (l * (n / Nat.gcd (Fintype.card G) n))))
      exact e2.trans ((congrArg (· ^ (l * (n / Nat.gcd (Fintype.card G) n)))
          (Eq.subst (motive := fun o => g ^ o = 1) hm (pow_orderOf_eq_one g))).trans
        (one_pow _))
  exact (Nat.card_congr (Equiv.subtypeEquivRight hiff)).trans
    ((Nat.card_zpowers (g ^ (Fintype.card G / Nat.gcd (Fintype.card G) n))).trans
      ((@orderOf_pow G _ _ (Fintype.card G / Nat.gcd (Fintype.card G) n) g).trans
        ((congrArg (fun o => o / Nat.gcd o (Fintype.card G / Nat.gcd (Fintype.card G) n)) hm).trans
          ((congrArg (fun t => Fintype.card G / t)
              (Nat.gcd_eq_right ⟨Nat.gcd (Fintype.card G) n, (Nat.div_mul_cancel hdm).symm⟩)).trans
            (Nat.div_div_self hdm hmpos.ne')))))

-- Reference: [Wilson] GTM 251, ch. 5 (the center of `SL(n, q)` is `μ_n(F_q)`,
-- of order `gcd n (q - 1)`); proof: `IsCyclic.card_pow_eq_one_eq_gcd` applied to
-- the cyclic group `(ZMod p)ˣ` of order `p - 1` (`IsCyclic (ZMod p)ˣ`,
-- `ZMod.card_units_eq_totient`, `Nat.totient_prime`), with
-- `mem_rootsOfUnity` identifying `rootsOfUnity n (ZMod p)` with the `n`-torsion.
/-- **The `n`-th roots of unity in `ZMod p` number `gcd n (p - 1)`** (over the
prime field `F_pˣ` is cyclic of order `p - 1`, and the `n`-torsion of a cyclic
group of order `m` has order `gcd n m`) (proved). -/
theorem card_rootsOfUnity_zmod_prime {n p : ℕ} [Fact p.Prime] :
    Nat.card (rootsOfUnity n (ZMod p)) = Nat.gcd n (p - 1) := by
  have hp : p.Prime := Fact.out
  have hcard : Fintype.card (ZMod p)ˣ = p - 1 :=
    (ZMod.card_units_eq_totient p).trans (Nat.totient_prime hp)
  have hequiv : ↥(rootsOfUnity n (ZMod p)) ≃ {x : (ZMod p)ˣ // x ^ n = 1} :=
    Equiv.subtypeEquivRight (fun ζ => mem_rootsOfUnity n ζ)
  exact (Nat.card_congr hequiv).trans
    ((IsCyclic.card_pow_eq_one_eq_gcd n).trans
      ((congrArg (fun m => Nat.gcd m n) hcard).trans (Nat.gcd_comm (p - 1) n)))

-- Reference: `card_PSL_finiteField_mul_card_rootsOfUnity` (Classification.lean)
-- + `card_rootsOfUnity_zmod_prime` + `ZMod.card`; [Wilson] GTM 251, ch. 5.
/-- **The full order formula for `PSL(n, F_p)` over a prime field** (proved from
#283): `|PSL(n, F_p)| * gcd n (p - 1) = (∏_{i<n} (p^n - p^i)) / (p - 1)`. -/
theorem card_PSL_zmod_prime_mul_gcd {n p : ℕ} [NeZero n] [Fact p.Prime] :
    Nat.card (PSL(n, ZMod p)) * Nat.gcd n (p - 1) =
      (∏ i : Fin n, (p ^ n - p ^ (i : ℕ))) / (p - 1) :=
  (congrArg (fun c => Nat.card (PSL(n, ZMod p)) * c)
      (card_rootsOfUnity_zmod_prime (p := p) (n := n))).symm.trans
    ((card_PSL_finiteField_mul_card_rootsOfUnity (n := n) (𝔽 := ZMod p)).trans
      (congrArg (fun c => (∏ i : Fin n, (c ^ n - c ^ (i : ℕ))) / (c - 1)) (ZMod.card p)))

end BoringMath
