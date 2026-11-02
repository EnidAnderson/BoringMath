/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringMath.GroupTheory.Simple.SLPerfect
import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

/-!
# Simplicity of `PSL(n, F)` for rank `n ≥ 3` — reduction to perfectness of `SL`

Ticket #230. The pin already provides, for the action of `PSL(n, F)` on the
projective space `ℙ F (ι → F)`: `FaithfulSMul` and `IsPreprimitive`
(`Projectivization/Action.lean`). What remains is the normal-subgroup argument,
which needs `SL(n, F)` perfect for `n ≥ 3` (transvections are commutators) —
tracked as the sanctioned sorry `SL_isPerfect` in `SLPerfect.lean`.

## References
* [Wilson] ch. 5 (PSL(n,q) simple for n ≥ 3); [GLS] Number 3.
* mathlib pin v4.35.0-rc3: `FaithfulSMul (PSL ι K) (ℙ K (ι → K))`,
  `IsPreprimitive (PSL ι K) (ℙ K (ι → K))` (Projectivization/Action.lean:238),
  `MulAction.IwasawaStructure.isSimpleGroup` (GroupAction/Iwasawa.lean).
-/

namespace BoringMath

open Matrix
open scoped MatrixGroups

-- Reference: [Wilson] ch. 5 (PSL(n,F) simple for n ≥ 3 given SL perfect);
-- pin's `IsPreprimitive`/`FaithfulSMul` for the projective action.
-- TEMPORARY SORRY with peeling plan.
/-- **`PSL(n, F)` is simple for `n ≥ 3`, given `SL(n, F)` is perfect**.
TEMPORARY SORRY with peeling plan. -/
theorem PSL_simple_of_SL_perfect {ι : Type*} [Fintype ι] [DecidableEq ι] {F : Type*}
    [Field F] (hι : 3 ≤ Fintype.card ι) [Group.IsPerfect (SpecialLinearGroup ι F)] :
    IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup ι F) := by
  -- TEMPORARY SORRY: the honest proof has not been instantiated yet.
  -- PEELING PLAN (normal-subgroup argument):
  --   (1) `N ⊲ PSL ι F`, `N ≠ ⊥`; the action on `ℙ F (ι → F)` is primitive
  --       (pin: `IsPreprimitive` instance), hence `N` acts transitively
  --       (`IsQuasiPreprimitive.isPretransitive_of_normal` — primitive ⇒
  --       quasiprimitive at the pin);
  --   (2) lift `N` to `N' ⊲ SL ι F` with `N' ⊇ center`; perfectness gives
  --       `⁅SL, SL⁆ = ⊤ ≤ N'`, so `N' = ⊤` (pin: `Group.IsPerfect`);
  --   (3) hence `N = ⊤` in `PSL` (quotient). Faithfulness of the action
  --       (pin: `FaithfulSMul (PSL ι F) (ℙ F (ι → F))`) rules out `N = ⊥`.
  sorry

-- Reference: as above, combined with `SL_isPerfect` (SLPerfect.lean).
/-- **`PSL(n, F)` is simple for `n ≥ 3`** (modulo the sanctioned
`SL_isPerfect` sorry). -/
theorem PSL_isSimpleGroup_rank_ge_three {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : Type*} [Field F] (hι : 3 ≤ Fintype.card ι) :
    IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup ι F) :=
  @PSL_simple_of_SL_perfect ι _ _ F _ hι (SL_isPerfect F hι)

end BoringMath
