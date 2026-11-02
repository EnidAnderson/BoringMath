/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringMath.GroupTheory.Simple.SLTransvection
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# Diagonals are products of transvections — step (2) of `SL_isPerfect` (#394)

For `i ≠ j` and `0 ≠ u`, the Weyl element `w_ij(u) = T_ij(u) T_ji(-u⁻¹) T_ij(u)`
and `h_ij(u) = w_ij(u) w_ij(-1) = diag2n(i,j,u)`. Hence every `diag2n` is a
product of transvections, so in rank `≥ 3` (where transvections are commutators,
`SLTransvection.lean`) every `diag2n` lies in the commutator subgroup.

## References
* [Carter] ch. 5; [Steinberg], *Lectures on Chevalley Groups* (the h_ij/w_ij
  identities).
* mathlib pin v4.35.0-rc3: `SpecialLinearGroup.diag2n`, `transvection`,
  `transvection_smul_single`, `diagonal_transvection_induction'`.
-/

namespace BoringMath

open Matrix
open scoped commutatorElement

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {F : Type*} [Field F]

-- Reference: [Steinberg] (the Weyl element as a product of transvections).
/-- The Weyl element `w_ij(u)` as a product of three transvections. -/
def wOf {i j : ι} (hij : i ≠ j) (u : F) (hu : u ≠ 0) : SpecialLinearGroup ι F :=
  SpecialLinearGroup.transvection hij u *
    SpecialLinearGroup.transvection (Ne.symm hij) (-u⁻¹) *
      SpecialLinearGroup.transvection hij u

-- Reference: [Steinberg] (h_ij(u) = w_ij(u) w_ij(-1) = diag(u, u⁻¹) in the (i,j) block).
/-- The torus element `h_ij(u) = w_ij(u) w_ij(-1)`. -/
def hOf {i j : ι} (hij : i ≠ j) (u : F) (hu : u ≠ 0) : SpecialLinearGroup ι F :=
  wOf hij u hu * wOf hij (-1) (neg_ne_zero.mpr one_ne_zero)

-- Reference: [Steinberg]; computation via the action on basis vectors, exactly
-- as in `commutator_transvection_transvection` (SLTransvection.lean):
-- `w_ij(u)` sends `e_i ↦ -u⁻¹ e_j`, `e_j ↦ u e_i`, fixes other `e_l`;
-- `h_ij(u)` sends `e_i ↦ u e_i`, `e_j ↦ u⁻¹ e_j`, fixes others = `diag2n`.
-- TEMPORARY SORRY with peeling plan.
/-- **The torus identity**: `h_ij(u) = diag2n(i, j, u)`. TEMPORARY SORRY with
peeling plan. -/
theorem hOf_eq_diag2n {i j : ι} (hij : i ≠ j) (u : F) (hu : u ≠ 0) :
    hOf hij u hu = SpecialLinearGroup.diag2n hij u hu := by
  sorry

-- Reference: `hOf_eq_diag2n` + `transvection_mem_commutator_of_card_three`
-- (SLTransvection.lean) + `Subgroup.mul_mem`; [Carter] ch. 5.
/-- In rank `≥ 3`, every `diag2n` lies in the commutator subgroup: it is a
product of six transvections, each a commutator. -/
theorem diag2n_mem_commutator_of_card_three {i j : ι} (hij : i ≠ j) (a : F) (ha : a ≠ 0)
    (hι : 3 ≤ Fintype.card ι) :
    SpecialLinearGroup.diag2n hij a ha ∈ commutator (SpecialLinearGroup ι F) := by
  have hT : ∀ (p q : ι) (hpq : p ≠ q) (b : F),
      SpecialLinearGroup.transvection hpq b ∈ commutator (SpecialLinearGroup ι F) :=
    fun p q hpq b => transvection_mem_commutator_of_card_three hpq b hι
  have e : SpecialLinearGroup.diag2n hij a ha = hOf hij a ha := (hOf_eq_diag2n hij a ha).symm
  refine Eq.subst (motive := fun x => x ∈ commutator (SpecialLinearGroup ι F)) e ?_
  -- `hOf = wOf * wOf`, each `wOf` a triple product of transvections
  show wOf hij a ha * wOf hij (-1) (neg_ne_zero.mpr one_ne_zero) ∈ _
  exact Subgroup.mul_mem _
    (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hT i j hij a)
      (hT j i (Ne.symm hij) (-a⁻¹))) (hT i j hij a))
    (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hT i j hij (-1))
      (hT j i (Ne.symm hij) (-(-1 : F)⁻¹))) (hT i j hij (-1)))

end BoringMath
