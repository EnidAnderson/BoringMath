/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.OrderOfElement

/-!
# The exact `n`-torsion count in a finite cyclic group

Ticket **#283** (step 1): in a finite cyclic group `α` of order `m`, the number
of solutions of `x ^ n = 1` is exactly `gcd n m`. mathlib at the pin has only the
upper bound `IsCyclic.card_pow_eq_one_le` (≤ n); here the equality is proved by
identifying the `n`-torsion with `zpowers (g ^ (m / gcd n m))` for a generator
`g` and computing its order via `orderOf_pow`.

This feeds `card_rootsOfUnity_zmod_prime` (PSLCard.lean, #283/#235):
`μ_n(ZMod p)` is the `n`-torsion of the cyclic group `(ZMod p)ˣ` of order `p - 1`.

## References
* [Dummit–Foote] D. S. Dummit, R. M. Foote, *Abstract Algebra*, 3rd ed., Wiley
  2004, Ch. 2, Sec. 3 (cyclic groups: unique subgroup of each order).
  REVIEW(citation): pin section against a held copy in review.
* mathlib pin v4.35.0-rc3: `IsCyclic.exists_generator`,
  `orderOf_eq_card_of_forall_mem_zpowers`, `mem_powers_iff_mem_zpowers`,
  `Submonoid.mem_powers_iff`, `orderOf_pow`, `Fintype.card_zpowers`,
  `orderOf_dvd_of_pow_eq_one`, `orderOf_dvd_iff_pow_eq_one`,
  `IsCyclic.card_pow_eq_one_le` (the ≤ bound).
-/

namespace BoringMath

variable {α : Type*} [Group α] [Fintype α]

/-! ## The two containments -/

-- Reference: mathlib pin v4.35.0-rc3, `orderOf_eq_card_of_forall_mem_zpowers`,
-- `Nat.card_eq_fintype_card`, `Nat.gcd_dvd_left`, `Nat.gcd_dvd_right`,
-- `Nat.div_mul_cancel`, `Nat.mul_comm`, `Nat.mul_assoc`, `dvd_mul_right`,
-- `orderOf_dvd_iff_pow_eq_one`, `mem_powers_iff_mem_zpowers`,
-- `Submonoid.mem_powers_iff`, `pow_mul`, `Nat.mul_right_comm`, `one_pow`.
/-- Every element of `zpowers (g ^ (m / gcd n m))` is `n`-torsion (where
`m = Fintype.card α` and `g` generates): `(m / d) * n = m * (n / d)`, so
`m ∣ (m/d) * n` and `g` has order `m`. -/
theorem pow_eq_one_of_mem_zpowers_div_gcd {g : α} (hg : ∀ x, x ∈ Subgroup.zpowers g)
    {n : ℕ} {a : α}
    (ha : a ∈ Subgroup.zpowers (g ^ (Fintype.card α / Nat.gcd n (Fintype.card α)))) :
    a ^ n = 1 := by
  have hm : orderOf g = Fintype.card α :=
    (orderOf_eq_card_of_forall_mem_zpowers hg).trans Nat.card_eq_fintype_card
  have hdvdn : Nat.gcd n (Fintype.card α) ∣ n := Nat.gcd_dvd_left n (Fintype.card α)
  have hdvdm : Nat.gcd n (Fintype.card α) ∣ Fintype.card α :=
    Nat.gcd_dvd_right n (Fintype.card α)
  have hn' : n = Nat.gcd n (Fintype.card α) * (n / Nat.gcd n (Fintype.card α)) :=
    (Nat.div_mul_cancel hdvdn).symm.trans (Nat.mul_comm _ _)
  have hdiv : (Fintype.card α / Nat.gcd n (Fintype.card α)) * n
      = Fintype.card α * (n / Nat.gcd n (Fintype.card α)) :=
    (congrArg (fun u => (Fintype.card α / Nat.gcd n (Fintype.card α)) * u) hn').trans
      ((Nat.mul_assoc _ _ _).symm.trans
        (congrArg (fun u => u * (n / Nat.gcd n (Fintype.card α)))
          (Nat.div_mul_cancel hdvdm)))
  have hdvd : Fintype.card α ∣ (Fintype.card α / Nat.gcd n (Fintype.card α)) * n :=
    Eq.subst (motive := fun k => Fintype.card α ∣ k) hdiv.symm (dvd_mul_right _ _)
  have hpow : g ^ ((Fintype.card α / Nat.gcd n (Fintype.card α)) * n) = 1 :=
    (orderOf_dvd_iff_pow_eq_one).mp
      (Eq.subst (motive := fun k => k ∣ (Fintype.card α / Nat.gcd n (Fintype.card α)) * n)
        hm.symm hdvd)
  obtain ⟨j, hj⟩ := (Submonoid.mem_powers_iff a
      (g ^ (Fintype.card α / Nat.gcd n (Fintype.card α)))).mp
    (mem_powers_iff_mem_zpowers.2 ha)
  calc a ^ n = ((g ^ (Fintype.card α / Nat.gcd n (Fintype.card α))) ^ j) ^ n :=
        congrArg (fun u => u ^ n) hj.symm
    _ = (g ^ (Fintype.card α / Nat.gcd n (Fintype.card α))) ^ (j * n) := (pow_mul _ j n).symm
    _ = g ^ ((Fintype.card α / Nat.gcd n (Fintype.card α)) * (j * n)) := (pow_mul g _ _).symm
    _ = g ^ (((Fintype.card α / Nat.gcd n (Fintype.card α)) * n) * j) :=
        congrArg (fun u => g ^ u) ((Nat.mul_assoc _ _ _).symm.trans (Nat.mul_right_comm _ _ _))
    _ = (g ^ ((Fintype.card α / Nat.gcd n (Fintype.card α)) * n)) ^ j := pow_mul g _ _
    _ = 1 ^ j := congrArg (fun u => u ^ j) hpow
    _ = 1 := one_pow j

-- Reference: mathlib pin v4.35.0-rc3, `mem_powers_iff_mem_zpowers`,
-- `Submonoid.mem_powers_iff`, `pow_mul`, `orderOf_dvd_of_pow_eq_one`,
-- `orderOf_eq_card_of_forall_mem_zpowers`, `Nat.card_eq_fintype_card`,
-- `Nat.div_mul_cancel`, `Nat.mul_comm`, `Nat.mul_assoc`, `Nat.mul_right_comm`,
-- `Nat.dvd_of_mul_dvd_mul_right`, `Nat.coprime_div_gcd_div_gcd`,
-- `Nat.Coprime.dvd_of_dvd_mul_right`, `Nat.gcd_pos_of_pos_left`,
-- `Subgroup.mem_zpowers_iff`, `zpow_natCast`.
/-- Every `n`-torsion element of a finite cyclic group with generator `g` lies in
`zpowers (g ^ (m / gcd n m))` (`m = Fintype.card α`): `a = g ^ j` with
`m ∣ j * n`, and dividing by `d = gcd n m` gives `(m/d) ∣ j` by coprimality. -/
theorem mem_zpowers_div_gcd_of_pow_eq_one {g : α} (hg : ∀ x, x ∈ Subgroup.zpowers g)
    {n : ℕ} (hn : 0 < n) {a : α} (ha : a ^ n = 1) :
    a ∈ Subgroup.zpowers (g ^ (Fintype.card α / Nat.gcd n (Fintype.card α))) := by
  have hm : orderOf g = Fintype.card α :=
    (orderOf_eq_card_of_forall_mem_zpowers hg).trans Nat.card_eq_fintype_card
  have hdvdn : Nat.gcd n (Fintype.card α) ∣ n := Nat.gcd_dvd_left n (Fintype.card α)
  have hdvdm : Nat.gcd n (Fintype.card α) ∣ Fintype.card α :=
    Nat.gcd_dvd_right n (Fintype.card α)
  obtain ⟨j, hj⟩ := (Submonoid.mem_powers_iff a g).mp (mem_powers_iff_mem_zpowers.2 (hg a))
  -- `a = g ^ j` and `a ^ n = 1` give `orderOf g ∣ j * n`, i.e. `m ∣ j * n`
  have hjn : g ^ (j * n) = 1 :=
    (pow_mul g j n).trans ((congrArg (fun u => u ^ n) hj).trans ha)
  have hmdvd : Fintype.card α ∣ j * n :=
    Eq.subst (motive := fun k => k ∣ j * n) hm (orderOf_dvd_of_pow_eq_one hjn)
  -- divide by `d`: `m = d * (m/d)` and `n = d * (n/d)`, so
  -- `(m/d) * d ∣ (j * (n/d)) * d`, hence `(m/d) ∣ j * (n/d)`, and
  -- `Coprime (m/d) (n/d)` gives `(m/d) ∣ j`
  have hpos : 0 < Nat.gcd n (Fintype.card α) := Nat.gcd_pos_of_pos_left (Fintype.card α) hn
  have hn' : n = Nat.gcd n (Fintype.card α) * (n / Nat.gcd n (Fintype.card α)) :=
    (Nat.div_mul_cancel hdvdn).symm.trans (Nat.mul_comm _ _)
  have hjn2 : j * n = (j * (n / Nat.gcd n (Fintype.card α))) * Nat.gcd n (Fintype.card α) :=
    (congrArg (fun u => j * u) hn').trans
      ((Nat.mul_assoc _ _ _).symm.trans (Nat.mul_right_comm _ _ _))
  have hmdvd' : (Fintype.card α / Nat.gcd n (Fintype.card α)) * Nat.gcd n (Fintype.card α)
      ∣ j * n :=
    Eq.subst (motive := fun k => k ∣ j * n) (Nat.div_mul_cancel hdvdm).symm hmdvd
  have hkey : (Fintype.card α / Nat.gcd n (Fintype.card α)) * Nat.gcd n (Fintype.card α)
      ∣ (j * (n / Nat.gcd n (Fintype.card α))) * Nat.gcd n (Fintype.card α) :=
    Eq.subst (motive := fun k => (Fintype.card α / Nat.gcd n (Fintype.card α))
        * Nat.gcd n (Fintype.card α) ∣ k) hjn2 hmdvd'
  have hdiv2 : (Fintype.card α / Nat.gcd n (Fintype.card α))
      ∣ j * (n / Nat.gcd n (Fintype.card α)) :=
    Nat.dvd_of_mul_dvd_mul_right hpos hkey
  have hcop : Nat.Coprime (Fintype.card α / Nat.gcd n (Fintype.card α))
      (n / Nat.gcd n (Fintype.card α)) := (Nat.coprime_div_gcd_div_gcd hpos).symm
  have hje : (Fintype.card α / Nat.gcd n (Fintype.card α)) ∣ j :=
    hcop.dvd_of_dvd_mul_right hdiv2
  obtain ⟨t, ht⟩ := hje
  exact Subgroup.mem_zpowers_iff.mpr ⟨(t : ℤ), by
    exact (zpow_natCast (g ^ (Fintype.card α / Nat.gcd n (Fintype.card α))) t).trans
      ((pow_mul g _ _).symm.trans ((congrArg (fun u => g ^ u) ht.symm).trans hj))⟩

/-! ## The exact count -/

variable [DecidableEq α] [IsCyclic α]

-- Reference: mathlib pin v4.35.0-rc3, `IsCyclic.exists_generator`,
-- `Fintype.card_congr`, `Equiv.ofBijective`, `Fintype.card_zpowers`,
-- `orderOf_pow`, `Nat.gcd_eq_right`, `Nat.div_dvd_of_dvd`, `Nat.div_div_self`,
-- `Fintype.card_pos`, `orderOf_eq_card_of_forall_mem_zpowers`,
-- `Nat.card_eq_fintype_card`; the two lemmas above.
/-- **Exact `n`-torsion count in a finite cyclic group**: the number of solutions
of `x ^ n = 1` in a finite cyclic group of order `m` is `gcd n m` (proved). -/
theorem IsCyclic.card_pow_eq_one {n : ℕ} (hn : 0 < n) :
    Fintype.card {a : α // a ^ n = 1} = Nat.gcd n (Fintype.card α) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := α)
  have hm : orderOf g = Fintype.card α :=
    (orderOf_eq_card_of_forall_mem_zpowers hg).trans Nat.card_eq_fintype_card
  have hdvdm : Nat.gcd n (Fintype.card α) ∣ Fintype.card α :=
    Nat.gcd_dvd_right n (Fintype.card α)
  have hcard : Fintype.card {a : α // a ^ n = 1}
      = Fintype.card ↥(Subgroup.zpowers (g ^ (Fintype.card α / Nat.gcd n (Fintype.card α)))) :=
    Fintype.card_congr (Equiv.ofBijective
      (fun a => (⟨a.1, mem_zpowers_div_gcd_of_pow_eq_one hg hn a.2⟩ :
        ↥(Subgroup.zpowers (g ^ (Fintype.card α / Nat.gcd n (Fintype.card α))))))
      ⟨fun a b hab => Subtype.ext (congrArg (fun u : ↥(Subgroup.zpowers
          (g ^ (Fintype.card α / Nat.gcd n (Fintype.card α)))) => (u : α)) hab),
        fun b => ⟨⟨b.1, pow_eq_one_of_mem_zpowers_div_gcd hg b.2⟩, rfl⟩⟩)
  have hord : orderOf (g ^ (Fintype.card α / Nat.gcd n (Fintype.card α)))
      = Nat.gcd n (Fintype.card α) := by
    have h1 : orderOf (g ^ (Fintype.card α / Nat.gcd n (Fintype.card α)))
        = orderOf g / Nat.gcd (orderOf g) (Fintype.card α / Nat.gcd n (Fintype.card α)) :=
      orderOf_pow (x := g) (n := Fintype.card α / Nat.gcd n (Fintype.card α))
    have h2 : Nat.gcd (orderOf g) (Fintype.card α / Nat.gcd n (Fintype.card α))
        = Fintype.card α / Nat.gcd n (Fintype.card α) :=
      Eq.subst (motive := fun k => Nat.gcd k (Fintype.card α / Nat.gcd n (Fintype.card α))
          = Fintype.card α / Nat.gcd n (Fintype.card α)) hm.symm
        (Nat.gcd_eq_right (Nat.div_dvd_of_dvd hdvdm))
    have h3 : orderOf g / (Fintype.card α / Nat.gcd n (Fintype.card α))
        = Nat.gcd n (Fintype.card α) :=
      Eq.subst (motive := fun k => k / (Fintype.card α / Nat.gcd n (Fintype.card α))
          = Nat.gcd n (Fintype.card α)) hm.symm
        (Nat.div_div_self hdvdm Fintype.card_pos.ne')
    exact h1.trans (Eq.subst (motive := fun k => orderOf g / k = Nat.gcd n (Fintype.card α))
      h2.symm h3)
  exact hcard.trans ((Fintype.card_zpowers
    (x := g ^ (Fintype.card α / Nat.gcd n (Fintype.card α)))).trans hord)

end BoringMath
