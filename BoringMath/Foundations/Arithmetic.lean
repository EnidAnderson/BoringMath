/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Nat.Cast.Order.Basic

/-!
# Basic real arithmetic (named term lemmas) — the boring arithmetic library

The most basic `ℝ`/cast facts used across the library, each proved ONCE as a
pure term (no tactics, no `norm_num`/`ring` — forbidden by STYLE §2): casts of
`0` and `1`, nonnegativity of halves, and the half-cast monotonicity used by
the area-spectrum gap (`Physics/LQG/AreaSpectrum.lean`, #352).

## References
* mathlib pin v4.35.0-rc3 (named lemmas only).
-/

namespace BoringMath

-- Reference: mathlib pin v4.35.0-rc3, `Nat.cast_nonneg`.
/-- `0 ≤ (n : ℝ)`. -/
theorem zero_le_cast (n : ℕ) : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n

-- Reference: mathlib pin v4.35.0-rc3, `Nat.one_le_cast` (Data/Nat/Cast/Order/Basic).
/-- `1 ≤ (n : ℝ)` from `1 ≤ n`. -/
theorem one_le_cast {n : ℕ} (h : 1 ≤ n) : (1 : ℝ) ≤ (n : ℝ) :=
  Nat.one_le_cast.mpr h

-- Reference: mathlib pin, `div_nonneg`, `two_pos`.
/-- `0 ≤ 1/2` in `ℝ`. -/
theorem half_nonneg : (0 : ℝ) ≤ (1 : ℝ) / 2 := div_nonneg zero_le_one two_pos.le

-- Reference: mathlib pin, `div_nonneg`.
/-- `0 ≤ (n : ℝ)/2`. -/
theorem half_cast_nonneg (n : ℕ) : (0 : ℝ) ≤ (n : ℝ) / 2 :=
  div_nonneg (Nat.cast_nonneg n) two_pos.le

-- Reference: mathlib pin, `add_nonneg`.
/-- `0 ≤ 1/2 + 1` in `ℝ`. -/
theorem half_add_one_nonneg : (0 : ℝ) ≤ (1 : ℝ) / 2 + 1 :=
  add_nonneg half_nonneg zero_le_one

-- Reference: mathlib pin, `div_le_div_of_nonneg_right`.
/-- `(1:ℝ)/2 ≤ (n:ℝ)/2` from `1 ≤ n` (half-cast monotonicity). -/
theorem half_le_half_cast {n : ℕ} (h : 1 ≤ n) : (1 : ℝ) / 2 ≤ (n : ℝ) / 2 :=
  div_le_div_of_nonneg_right (one_le_cast h) two_pos.le

end BoringMath
