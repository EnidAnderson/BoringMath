/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Order.Directed

/-!
# The `p`-core `O_p(G)` — the largest normal `p`-subgroup

Ticket CFSG.LIB.local (#241). `O_p(G)` is the join of all normal `p`-subgroups
of `G`; it is itself a normal `p`-subgroup and contains every normal
`p`-subgroup. Used throughout the local analysis (e.g. constrained groups).
mathlib at the pin has `normalCore` but no `p`-core.

## References
* [GLS] Number 2, ch. 1 (`O_p(G)`); Aschbacher, *Finite Group Theory*, ch. 8.
* mathlib pin v4.35.0-rc3: `IsPGroup`, `Subgroup.iSup_normal` (Pointwise.lean).
-/

namespace BoringMath

open Subgroup

variable (p : ℕ) (G : Type*) [Group G]

-- Reference: [GLS] Number 2, ch. 1 (definition of `O_p(G)`).
/-- The **`p`-core `O_p(G)`**: the join of all normal `p`-subgroups of `G`. -/
def oCore : Subgroup G :=
  ⨆ N : {N : Subgroup G // N.Normal ∧ IsPGroup p N}, N.1

-- Reference: mathlib pin v4.35.0-rc3, `Subgroup.iSup_normal`.
/-- Every normal subgroup in the family is normal (instance wrapper). -/
instance oCore_family_normal :
    ∀ N : {N : Subgroup G // N.Normal ∧ IsPGroup p N}, (N.1).Normal :=
  fun ⟨_, hN, _⟩ => hN

-- Reference: mathlib pin v4.35.0-rc3, `Subgroup.iSup_normal`; [GLS] Number 2.
/-- **`O_p(G)` is normal** (proved). -/
theorem oCore_normal : (oCore p G).Normal :=
  iSup_normal _

-- Reference: immediate from the definition (`le_iSup`); [GLS] Number 2
-- (`O_p(G)` contains every normal `p`-subgroup).
/-- **Every normal `p`-subgroup lies in `O_p(G)`** (proved). -/
theorem le_oCore {N : Subgroup G} (hN : N.Normal) (hP : IsPGroup p N) :
    N ≤ oCore p G :=
  le_iSup (fun M : {N : Subgroup G // N.Normal ∧ IsPGroup p N} => M.1) ⟨N, hN, hP⟩

-- Reference: mathlib pin v4.35.0-rc3, `isPGroup_iff_pow_pow_eq_one`,
-- `QuotientGroup.eq_one_iff`, `map_pow`, `pow_add`, `pow_mul`,
-- `Subgroup.coe_pow`; [GLS] Number 2 (an extension of a `p`-group by a
-- `p`-group is a `p`-group).
/-- **Extension lemma**: if `N` is a normal `p`-subgroup of `G` and `G ⧸ N` is
a `p`-group, then `G` is a `p`-group (proved). -/
theorem IsPGroup.of_normal_quotient {N : Subgroup G} [N.Normal] (hN : IsPGroup p ↥N)
    (hQ : IsPGroup p (G ⧸ N)) : IsPGroup p G := by
  apply isPGroup_iff_pow_pow_eq_one.mpr
  intro g
  obtain ⟨k, hk⟩ := isPGroup_iff_pow_pow_eq_one.mp hQ (QuotientGroup.mk' N g)
  have hmem : g ^ (p ^ k) ∈ N :=
    (QuotientGroup.eq_one_iff (g ^ (p ^ k))).mp
      ((map_pow (QuotientGroup.mk' N) g (p ^ k)).symm.trans hk)
  obtain ⟨m, hm⟩ := isPGroup_iff_pow_pow_eq_one.mp hN ⟨g ^ (p ^ k), hmem⟩
  refine ⟨k + m, ?_⟩
  have e1 : g ^ (p ^ (k + m)) = g ^ (p ^ k * p ^ m) := congrArg (g ^ ·) (pow_add p k m)
  have e2 : g ^ (p ^ k * p ^ m) = (g ^ (p ^ k)) ^ (p ^ m) := pow_mul g (p ^ k) (p ^ m)
  have e3 : (g ^ (p ^ k)) ^ (p ^ m) = 1 := by
    have h4 : ((⟨g ^ (p ^ k), hmem⟩ : ↥N) ^ (p ^ m) : G) = (g ^ (p ^ k)) ^ (p ^ m) :=
      Subgroup.coe_pow N ⟨g ^ (p ^ k), hmem⟩ (p ^ m)
    have h5 : ((⟨g ^ (p ^ k), hmem⟩ : ↥N) ^ (p ^ m) : G) = 1 :=
      (congrArg (fun u : ↥N => (u : G)) hm).trans rfl
    exact h4.symm.trans h5
  exact e1.trans (e2.trans e3)

-- Reference: mathlib pin v4.35.0-rc3, `Subgroup.mem_sup_of_normal_right`,
-- `Subgroup.mem_sup_left`, `Subgroup.mem_sup_right`, `Subgroup.mul_mem_sup`,
-- `Subgroup.Normal.comap`, `Subgroup.mem_comap`, `MonoidHom.codRestrict`,
-- `QuotientGroup.mk'_surjective`, `QuotientGroup.eq_one_iff`, `map_mul`,
-- `IsPGroup.of_injective`, `IsPGroup.of_surjective`, `one_mul`;
-- [GLS] Number 2 (the join of two normal `p`-subgroups is a `p`-group, via
-- `(H ⊔ K) ⧸ H` being a quotient of `K`).
/-- **The join of two normal `p`-subgroups is a `p`-group** (proved). -/
theorem IsPGroup.sup_of_normal {H K : Subgroup G} [H.Normal] [K.Normal]
    (hH : IsPGroup p ↥H) (hK : IsPGroup p ↥K) : IsPGroup p ↥(H ⊔ K) := by
  have hNnorm : (H.comap (H ⊔ K).subtype).Normal :=
    Subgroup.Normal.comap inferInstance (H ⊔ K).subtype
  have hN : IsPGroup p ↥(H.comap (H ⊔ K).subtype) :=
    IsPGroup.of_injective hH
      (MonoidHom.codRestrict ((H ⊔ K).subtype.comp (H.comap (H ⊔ K).subtype).subtype)
        H (fun x => x.2))
      (by
        intro a b hab
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun u : ↥H => (u : G)) hab)
  have hsurj : Function.Surjective
      ((QuotientGroup.mk' (H.comap (H ⊔ K).subtype)).comp
        (MonoidHom.codRestrict K.subtype (H ⊔ K) (fun k => Subgroup.mem_sup_right k.2))) := by
    intro x
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (H.comap (H ⊔ K).subtype) x
    rcases Subgroup.mem_sup_of_normal_right.mp y.2 with ⟨h, hh, k, hk, hyk⟩
    refine ⟨⟨k, hk⟩, ?_⟩
    change QuotientGroup.mk' (H.comap (H ⊔ K).subtype)
        (MonoidHom.codRestrict K.subtype (H ⊔ K) (fun kk => Subgroup.mem_sup_right kk.2)
          ⟨k, hk⟩) = x
    have h1 : QuotientGroup.mk' (H.comap (H ⊔ K).subtype) ⟨h, Subgroup.mem_sup_left hh⟩ = 1 :=
      (QuotientGroup.eq_one_iff (⟨h, Subgroup.mem_sup_left hh⟩ : ↥(H ⊔ K))).mpr
        (Subgroup.mem_comap.mpr hh)
    have h2 : y = ⟨h * k, Subgroup.mul_mem_sup hh hk⟩ := Subtype.ext hyk.symm
    calc QuotientGroup.mk' (H.comap (H ⊔ K).subtype)
          (MonoidHom.codRestrict K.subtype (H ⊔ K) (fun kk => Subgroup.mem_sup_right kk.2)
            ⟨k, hk⟩)
        = QuotientGroup.mk' (H.comap (H ⊔ K).subtype) ⟨k, Subgroup.mem_sup_right hk⟩ :=
          congrArg _ (Subtype.ext rfl)
      _ = 1 * QuotientGroup.mk' (H.comap (H ⊔ K).subtype) ⟨k, Subgroup.mem_sup_right hk⟩ :=
          (one_mul _).symm
      _ = QuotientGroup.mk' (H.comap (H ⊔ K).subtype) ⟨h, Subgroup.mem_sup_left hh⟩ *
            QuotientGroup.mk' (H.comap (H ⊔ K).subtype) ⟨k, Subgroup.mem_sup_right hk⟩ :=
          (congrArg (fun u =>
            u * QuotientGroup.mk' (H.comap (H ⊔ K).subtype) ⟨k, Subgroup.mem_sup_right hk⟩)
            h1).symm
      _ = QuotientGroup.mk' (H.comap (H ⊔ K).subtype)
            (⟨h, Subgroup.mem_sup_left hh⟩ * ⟨k, Subgroup.mem_sup_right hk⟩) := by
          exact (map_mul (QuotientGroup.mk' (H.comap (H ⊔ K).subtype))
            ⟨h, Subgroup.mem_sup_left hh⟩ ⟨k, Subgroup.mem_sup_right hk⟩).symm
      _ = QuotientGroup.mk' (H.comap (H ⊔ K).subtype)
            ⟨h * k, Subgroup.mul_mem_sup hh hk⟩ := congrArg _ (Subtype.ext rfl)
      _ = QuotientGroup.mk' (H.comap (H ⊔ K).subtype) y := congrArg _ h2.symm
      _ = x := hy
  exact IsPGroup.of_normal_quotient p ↥(H ⊔ K) hN
    (IsPGroup.of_surjective hK _ hsurj)

-- Reference: `IsPGroup.sup_of_normal`, `Subgroup.sup_normal`, `le_sup_left`,
-- `le_sup_right`; [GLS] Number 2.
/-- The family of normal `p`-subgroups is directed under `≤` (proved). -/
theorem oCore_family_directed :
    Directed (· ≤ ·) (fun N : {N : Subgroup G // N.Normal ∧ IsPGroup p N} => N.1) := by
  intro N M
  have hN1 : N.1.Normal := N.2.1
  have hM1 : M.1.Normal := M.2.1
  exact ⟨(⟨N.1 ⊔ M.1, inferInstance, IsPGroup.sup_of_normal p G N.2.2 M.2.2⟩ :
    {N : Subgroup G // N.Normal ∧ IsPGroup p N}), le_sup_left, le_sup_right⟩

-- Reference: mathlib pin v4.35.0-rc3, `Subgroup.mem_iSup_of_directed`,
-- `isPGroup_iff_pow_pow_eq_one`, `Subgroup.coe_pow`, `IsPGroup.of_bot`;
-- [GLS] Number 2 (`O_p(G)` is a `p`-group).
/-- **`O_p(G)` is a `p`-group** (proved: the family is directed, so every element
of the join lies in one of its members). -/
theorem oCore_isPGroup : IsPGroup p ↥(oCore p G) := by
  apply isPGroup_iff_pow_pow_eq_one.mpr
  intro g
  have hne : Nonempty {N : Subgroup G // N.Normal ∧ IsPGroup p N} :=
    ⟨⟨⊥, inferInstance, IsPGroup.of_bot⟩⟩
  rcases (Subgroup.mem_iSup_of_directed (oCore_family_directed p G)).mp g.2 with ⟨N, hN⟩
  obtain ⟨k, hk⟩ := isPGroup_iff_pow_pow_eq_one.mp N.2.2 ⟨(g : G), hN⟩
  have hco : ((⟨(g : G), hN⟩ : ↥N.1) ^ (p ^ k) : G) = (g : G) ^ (p ^ k) :=
    Subgroup.coe_pow N.1 ⟨(g : G), hN⟩ (p ^ k)
  have hkG : ((⟨(g : G), hN⟩ : ↥N.1) ^ (p ^ k) : G) = 1 :=
    (congrArg (fun u : ↥N.1 => (u : G)) hk).trans rfl
  refine ⟨k, Subtype.ext ?_⟩
  change ((g ^ (p ^ k) : ↥(oCore p G)) : G) = ((1 : ↥(oCore p G)) : G)
  exact (Subgroup.coe_pow (oCore p G) g (p ^ k)).trans (hco.symm.trans hkG)

end BoringMath
