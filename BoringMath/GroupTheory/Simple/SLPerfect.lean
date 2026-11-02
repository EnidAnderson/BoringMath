/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
import BoringMath.GroupTheory.Simple.SLDiag

/-!
# Perfectness of `SL(n, F)` — the Iwasawa ingredient for sector C (#230)

`SL(2, F)` is perfect when `F` has an element `a ≠ 0` with `a² ≠ 1` (pin:
`SL2.commutator_eq_top`). For rank `n ≥ 3`, `SL(n, F)` is perfect because
transvections generate `SL` (`diagonal_transvection_induction'`) and every
transvection is a commutator. This is step (1) of the Iwasawa peeling plan for
`PSL(n, q)` simplicity.

## References
* mathlib pin v4.35.0-rc3: `SL2.commutator_eq_top`,
  `diagonal_transvection_induction'`, `SpecialLinearGroup.transvection`.
* [Carter] ch. 5; [Wilson] ch. 5 (SL(n,q) is perfect except (2,2),(2,3)).
-/

namespace BoringMath

open Matrix

-- Reference: mathlib pin v4.35.0-rc3, `SL2.commutator_eq_top` (PSL2.lean uses it);
-- [Carter] ch. 5.
/-- **`SL(2, F)` is perfect when `F` has an element `a ≠ 0` with `a² ≠ 1`**
(consumed at the pin; holds for `|F| ≥ 4`). -/
theorem SL2_isPerfect {F : Type*} [Field F] {a : F} (ha : a ≠ 0) (hasq : a ^ 2 ≠ 1) :
    Group.IsPerfect (SpecialLinearGroup (Fin 2) F) :=
  ⟨SL2.commutator_eq_top ha hasq⟩

-- Reference: [Carter] ch. 5 / [Wilson] ch. 5 (`SL(n, F)` is perfect for
-- `n ≥ 3` over any field). Steps (1) and (2) are landed:
-- `transvection_mem_commutator_of_card_three` (SLTransvection.lean) and
-- `diag2n_mem_commutator_of_card_three` (SLDiag.lean); step (3) is the pin's
-- `SpecialLinearGroup.diagonal_transvection_induction'` with
-- `P := (· ∈ commutator (SL ι F))`.
/-- **`SL(n, F)` is perfect for `n ≥ 3`** (over any field; proved). -/
theorem SL_isPerfect {ι : Type*} [Fintype ι] [DecidableEq ι] (F : Type*) [Field F]
    (hι : 3 ≤ Fintype.card ι) : Group.IsPerfect (SpecialLinearGroup ι F) := by
  haveI : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.mp
    (Nat.lt_of_lt_of_le (Nat.lt_succ_of_le (Nat.le_add_right 1 1)) hι)
  refine ⟨?_⟩
  apply eq_top_iff.mpr
  intro M _
  exact SpecialLinearGroup.diagonal_transvection_induction'
    (fun A => A ∈ commutator (SpecialLinearGroup ι F)) M
    (fun i j hij c hc => diag2n_mem_commutator_of_card_three hij c hc hι)
    (fun i j hij a => transvection_mem_commutator_of_card_three hij a hι)
    (fun A B hA hB => Subgroup.mul_mem _ hA hB)

end BoringMath
