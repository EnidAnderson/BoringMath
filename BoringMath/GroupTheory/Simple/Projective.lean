/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.Algebra.Field.ZMod

/-!
# The projective line `P^1(F_q)` has `q + 1` points

Ticket #230 (PSL simplicity, Iwasawa step). The projective line over a finite
field `F_q` has `q + 1` points, and `PSL(2, q)` acts faithfully on it (the pin
has `FaithfulSMul (PSL(2, F)) (ℙ F (Fin 2 → F))` in `Projectivization/PSL`).

## References
* mathlib pin v4.35.0-rc3: `Projectivization.card` (Cardinality.lean),
  `Nat.card_fun`, `Nat.sq_sub_sq`, `Nat.mul_right_cancel`.
* [Wilson] ch. 5 (the projective line has q+1 points; PSL(2,q) acts on it).
-/

namespace BoringMath

open scoped LinearAlgebra.Projectivization

-- Reference: mathlib pin v4.35.0-rc3, `Projectivization.card` +
-- `Nat.sq_sub_sq` + `Nat.mul_right_cancel`; [Wilson] ch. 5.
/-- **The projective line over a finite field `F` with `q ≥ 2` elements has
`q + 1` points** (proved). -/
theorem card_projectivization_fin_two {F : Type*} [Field F] [Fintype F]
    (hq2 : 2 ≤ Fintype.card F) :
    Nat.card (ℙ F (Fin 2 → F)) = Fintype.card F + 1 := by
  set q := Fintype.card F
  have hq : Nat.card F = q := Nat.card_eq_fintype_card
  have hV : Nat.card (Fin 2 → F) = q ^ 2 :=
    (Nat.card_fun (α := Fin 2) (β := F)).trans
      ((congrArg (· ^ Nat.card (Fin 2)) hq).trans
        ((congrArg (q ^ ·) (Nat.card_fin 2))))
  have h := Projectivization.card F (Fin 2 → F)
  have h2 : q ^ 2 - 1 = Nat.card (ℙ F (Fin 2 → F)) * (q - 1) :=
    (congrArg (· - 1) hV).symm.trans
      (h.trans (congrArg (fun t => Nat.card (ℙ F (Fin 2 → F)) * t) (congrArg (· - 1) hq)))
  have hsq : q ^ 2 - 1 = (q + 1) * (q - 1) :=
    (congrArg (fun t => q ^ 2 - t) (one_pow 2)).symm.trans (Nat.sq_sub_sq q 1)
  have hpos : 0 < q - 1 := Nat.sub_pos_of_lt (Nat.lt_of_succ_le hq2)
  exact Nat.mul_right_cancel hpos (h2.symm.trans hsq)

end BoringMath
