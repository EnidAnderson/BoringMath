/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Algebra.Field.Basic
import BoringMath.FormalPeriods.FreeMod
import BoringMath.FormalPeriods.FormalPeriods.FinSum
import BoringMath.FormalPeriods.FormalPeriods.FreeModHomModule

/-!
# The dual (contragredient) map and the dual pairing

`dualMap f ω = ω ∘ f` (precomposition), the scalar pairing `dualVal ω x`,
and its expansion in the standard basis `dualValEqSum`.  Split out of
`BoringMath.FormalPeriods.FormalPeriods`.
-/

universe u

namespace BoringMath.FormalPeriods

variable {B K L : Type u} [Field B] [Field K] [Field L] [Algebra B K] [Algebra K L]
variable {m n : ℕ}

/-! ## The dual (contragredient) map and the dual pairing -/

-- Reference: line 372 (precompDual, map_add' field: `rw [f.map_add' x y]`).
/-- Peel: precomposition unfolds `f` on `x + y`. -/
theorem precompDualMapAdd (f : FreeModHom K m n) (ω : FreeModDual K n) (x y : FreeMod K m) :
    ω.toFun (f.toFun (x + y)) = ω.toFun (f.toFun x) + ω.toFun (f.toFun y) :=
  Eq.trans (congrArg ω.toFun (f.map_add' x y)) (ω.map_add' (f.toFun x) (f.toFun y))

-- Reference: line 376 (precompDual, map_smul' field: `rw [f.map_smul' c x]`).
/-- Peel: precomposition unfolds `f` on `c • x`. -/
theorem precompDualMapSmul (f : FreeModHom K m n) (ω : FreeModDual K n) (c : K) (x : FreeMod K m) :
    ω.toFun (f.toFun (c • x)) = c • ω.toFun (f.toFun x) :=
  Eq.trans (congrArg ω.toFun (f.map_smul' c x)) (ω.map_smul' c (f.toFun x))

-- Reference: Axler, LADR 4th ed., Ch. 3 (precomposition `ω ↦ ω ∘ α` is a linear
-- map into the one-dimensional target); Hörmann, arXiv:2106.03803, Def 2.3
-- (the relation uses `α∨`).
/-- Precomposition of a dual vector by `f`: the underlying map of `f∨(ω)`. -/
def precompDual (f : FreeModHom K m n) (ω : FreeModDual K n) : FreeModDual K m :=
  ⟨fun x => ω.toFun (f.toFun x),
    fun x y => precompDualMapAdd f ω x y,
    fun c x => precompDualMapSmul f ω c x⟩

-- Reference: Hörmann, arXiv:2106.03803, Def 2.3 (the relation uses `α∨`, the
-- dual of `α : M → N` acting on `H_dR(N)∨`); Axler, LADR 4th ed., Ch. 3 (the
-- dual map `T ↦ T'` is precomposition).
/-- The dual (contragredient) of a morphism of basis-carrying free modules:
precomposition, `α∨(ω) = ω ∘ α`. -/
def dualMap (f : FreeModHom K m n) : FreeModDual K n → FreeModDual K m :=
  fun ω => precompDual f ω

-- Reference: Axler, LADR 4th ed., Ch. 3 (a linear functional on `F^n` is
-- evaluated by its values on the standard basis); Hörmann, arXiv:2106.03803,
-- Def 2.5 (`eval_∫` evaluates `ω` at `∫_M(σ)`).
/-- The scalar value of a dual vector `ω : FreeModDual K n` at `x : FreeMod K n`:
the `0`-th coordinate of `ω x` in the one-dimensional target `FreeMod K 1`. -/
def dualVal (ω : FreeModDual K n) (x : FreeMod K n) : K := (ω.toFun x) 0

-- Reference: Axler, LADR 4th ed., Ch. 3 (precomposition unfolds definitionally);
-- primitive definitional lemma.
/-- The dual pairing unfolds through the dual map: `α∨(ω)(x) = ω(α x)`. -/
theorem dualValDualMap (f : FreeModHom K m n) (ω : FreeModDual K n) (x : FreeMod K m) :
    dualVal (dualMap f ω) x = dualVal ω (f.toFun x) := rfl

-- Reference: Axler, LADR 4th ed., Ch. 3; mathlib (`Pi.add_apply`).
/-- The dual pairing is additive in the dual argument. -/
theorem dualValAdd (ω₁ ω₂ : FreeModDual K n) (x : FreeMod K n) :
    dualVal (ω₁ + ω₂) x = dualVal ω₁ x + dualVal ω₂ x :=
  Pi.add_apply (ω₁.toFun x) (ω₂.toFun x) 0

-- Reference: Axler, LADR 4th ed., Ch. 3; mathlib (`Pi.smul_apply`, `smul_eq_mul`).
/-- The dual pairing is `K`-linear in the dual argument. -/
theorem dualValSmul (c : K) (ω : FreeModDual K n) (x : FreeMod K n) :
    dualVal (c • ω) x = c * dualVal ω x :=
  Eq.trans (Pi.smul_apply c (ω.toFun x) 0) (smul_eq_mul c (dualVal ω x))

-- Reference: Axler, LADR 4th ed., Ch. 3; mathlib (`Pi.zero_apply`).
/-- The zero dual vector pairs to zero. -/
theorem dualValZero (x : FreeMod K n) : dualVal (0 : FreeModDual K n) x = 0 :=
  Pi.zero_apply 0

-- Reference: Axler, LADR 4th ed., Ch. 2–3 (a linear functional is determined by
-- its values on the standard basis: `ω(x) = ∑ j, x j * ω(eⱼ)`); Hörmann,
-- arXiv:2106.03803, Def 2.5 (the period pairing `ω(∫_M σ)`).
/-- The dual pairing expands in the standard basis:
`ω(x) = ∑ j, x j * ω(eⱼ)`. -/
theorem dualValEqSum (ω : FreeModDual K n) (x : FreeMod K n) :
    dualVal ω x = finSum n (fun j => x j * dualVal ω (Pi.single j 1)) := by
  have h1 : ω.toFun x = finSum n (fun j => x j • ω.toFun (Pi.single j (1 : K))) :=
    Eq.trans (congrArg ω.toFun (freeModEqSumSingle x))
      (Eq.trans (freeModHomMapSum ω n (fun j => x j • Pi.single j (1 : K)))
        (listSum_congr (List.finRange n) _ _ (fun j => ω.map_smul' (x j) (Pi.single j (1 : K)))))
  calc (ω.toFun x) 0
      = (finSum n (fun j => x j • ω.toFun (Pi.single j (1 : K)))) 0 :=
          congrArg (fun v : FreeMod K 1 => v 0) h1
    _ = finSum n (fun j => (x j • ω.toFun (Pi.single j (1 : K))) 0) :=
          listSum_apply (List.finRange n) (fun j => x j • ω.toFun (Pi.single j (1 : K))) 0
    _ = finSum n (fun j => x j * (ω.toFun (Pi.single j (1 : K))) 0) :=
          listSum_congr (List.finRange n) _ _ (fun j =>
            Eq.trans (Pi.smul_apply (x j) (ω.toFun (Pi.single j (1 : K))) 0)
              (smul_eq_mul (x j) ((ω.toFun (Pi.single j (1 : K))) 0)))


end BoringMath.FormalPeriods
