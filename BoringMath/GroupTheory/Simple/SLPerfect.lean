/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

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
-- `n ≥ 3` over any field). TEMPORARY SORRY with peeling plan.
/-- **`SL(n, F)` is perfect for `n ≥ 3`** (over any field). TEMPORARY SORRY
with peeling plan. -/
theorem SL_isPerfect {ι : Type*} [Fintype ι] [DecidableEq ι] (F : Type*) [Field F]
    (hι : 3 ≤ Fintype.card ι) : Group.IsPerfect (SpecialLinearGroup ι F) := by
  -- TEMPORARY SORRY: the honest proof has not been instantiated yet.
  -- PEELING PLAN:
  --   (1) every transvection `T_ij(b)` lies in `⁅SL, SL⁆` for `n ≥ 3`:
  --       `T_ij(b) = ⁅T_ij(1), diag(..., b, ..., b⁻¹, ...)⁆`-style identity
  --       (pin has `commutatorElement`/`diag2_inv`/`transvection_inv` machinery
  --       at SpecialLinearGroup.lean:739);
  --   (2) diagonals with determinant 1 lie in `⁅SL, SL⁆` (product of
  --       `diag(a, a⁻¹, 1, …)` and each of those is `⁅T_12(1), T_21(a-1)⁆`-style);
  --   (3) `diagonal_transvection_induction'` (pin) closes: `⁅SL, SL⁆ = ⊤`.
  sorry

end BoringMath
