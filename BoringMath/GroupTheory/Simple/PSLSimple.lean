/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finite.GaloisField
import BoringMath.GroupTheory.Simple.Classification
import BoringMath.GroupTheory.Simple.OrderTwelve
import BoringMath.GroupTheory.Simple.PSLSimpleRank

/-!
# Simplicity of `PSL(2, F_q)` — the rank-2 case of sector C (#230)

The pin already proves `Matrix.ProjectiveSpecialLinearGroup.rank_two_simple`:
`PSL(2, F)` is simple whenever `4 ≤ Nat.card F`, via the Iwasawa criterion on
the faithful action on the projective line (`Projectivization/PSL/PSL2.lean`).
This module consumes it over the concrete finite fields. The exceptions
`PSL(2,2)` and `PSL(2,3)` are handled in `Classification.lean` /
`SmallOrders.lean`; rank `≥ 3` remains open (see `PSL_isSimpleGroup` in
`Classification.lean`).

## References
* mathlib pin v4.35.0-rc3: `Matrix.ProjectiveSpecialLinearGroup.rank_two_simple`,
  `rank_two_simple'` (Projectivization/PSL/PSL2.lean, Iwasawa criterion);
  `GaloisField.card`; `ZMod.card`.
* [Wilson] ch. 5 (PSL(2,q) simple for q ≥ 4); [GLS] Number 3.
-/

namespace BoringMath

open Matrix
open scoped MatrixGroups

-- Reference: mathlib pin v4.35.0-rc3, `Matrix.ProjectiveSpecialLinearGroup.
-- rank_two_simple`; [Wilson] ch. 5.
/-- **`PSL(2, F)` is simple when `4 ≤ |F|`** (consumed at the pin). -/
theorem PSL2_isSimpleGroup {F : Type*} [Field F] (hF : 4 ≤ Nat.card F) :
    IsSimpleGroup (PSL(2, F)) :=
  Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hF

-- Reference: as above, over the prime field `F_p` (`Nat.card (ZMod p) = p`).
/-- **`PSL(2, p)` is simple for a prime `p ≥ 4`** (i.e. `p ≥ 5`) (consumed). -/
theorem PSL2_isSimpleGroup_zmod {p : ℕ} [Fact p.Prime] (hp : 4 ≤ p) :
    IsSimpleGroup (PSL(2, ZMod p)) :=
  PSL2_isSimpleGroup
    (Eq.subst (motive := fun n => 4 ≤ n)
      ((Nat.card_eq_fintype_card (α := ZMod p)).trans (ZMod.card p)).symm hp)

-- Reference: as above, over `F_{p^k}` (`GaloisField.card`).
/-- **`PSL(2, F_{p^k})` is simple when `p^k ≥ 4`** (consumed). -/
theorem PSL2_isSimpleGroup_galoisField {p k : ℕ} [Fact p.Prime] [NeZero k]
    (h : 4 ≤ p ^ k) : IsSimpleGroup (PSL(2, GaloisField p k)) :=
  PSL2_isSimpleGroup
    (Eq.subst (motive := fun n => 4 ≤ n)
      (GaloisField.card (p := p) (n := k) (NeZero.ne k)).symm h)

-- Reference: `card_PSL_2_3` (Classification.lean) + `not_isSimpleGroup_of_card_eq_twelve`
-- (OrderTwelve.lean); [Wilson] ch. 5 (`PSL(2,3) ≅ A_4`, not simple).
/-- **`PSL(2, F_3)` is not simple** (proved: it has order 12). -/
theorem not_isSimpleGroup_PSL_2_3 [Fact (Nat.Prime 3)] [NeZero 2] :
    ¬ IsSimpleGroup (PSL(2, ZMod 3)) :=
  not_isSimpleGroup_of_card_eq_twelve card_PSL_2_3


-- Reference: `PSL_isSimpleGroup_rank_ge_three` (PSLSimpleRank.lean, PROVED via the
-- Iwasawa criterion) + `Fintype.card_fin`; [Wilson] ch. 5.
/-- **`PSL(n, F_{p^k})` is simple for `n ≥ 3`** (rank ≥ 3 case of #230, proved). -/
theorem PSL_isSimpleGroup_galoisField_of_three_le {n p k : ℕ} [Fact p.Prime] [NeZero k]
    (hn : 3 ≤ n) : IsSimpleGroup (PSL(n, GaloisField p k)) :=
  PSL_isSimpleGroup_rank_ge_three (F := GaloisField p k) (ι := Fin n)
    (Eq.subst (motive := fun m => 3 ≤ m) (Fintype.card_fin n).symm hn)

-- Reference: as above, over the prime field `F_p` (`Fintype.card (ZMod p) = p` via
-- `Fintype.card_fin`).
/-- **`PSL(n, F_p)` is simple for `n ≥ 3`** (rank ≥ 3 case of #230, proved). -/
theorem PSL_isSimpleGroup_zmod_of_three_le {n p : ℕ} [Fact p.Prime] (hn : 3 ≤ n) :
    IsSimpleGroup (PSL(n, ZMod p)) :=
  PSL_isSimpleGroup_rank_ge_three (F := ZMod p) (ι := Fin n)
    (Eq.subst (motive := fun m => 3 ≤ m) (Fintype.card_fin n).symm hn)
end BoringMath
