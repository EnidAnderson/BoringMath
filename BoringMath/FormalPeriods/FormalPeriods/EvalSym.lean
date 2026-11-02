/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Quot
import BoringMath.FormalPeriods.FreeMod
import BoringMath.FormalPeriods.FormalPeriods.LinearAbelian
import BoringMath.FormalPeriods.FormalPeriods.Quadruple
import BoringMath.FormalPeriods.FormalPeriods.Symbols
import BoringMath.FormalPeriods.FormalPeriods.Quotient
import BoringMath.FormalPeriods.FormalPeriods.Dual
import BoringMath.FormalPeriods.FormalPeriods.BaseChange
import BoringMath.FormalPeriods.FormalPeriods.PairL

/-!
# The value of `eval_∫` on symbols, and the raw evaluation on formal sums

`evalSym Q M σ ω = ω(∫_M σ)` (the pairing of `ω` with the base-changed
comparison `∫_M σ`) with its linearity laws and the morphism-relation law
`evalSymMorph` (exactly the naturality of `∫`), and `evalRaw Q` on raw
formal sums.  Split out of `BoringMath.FormalPeriods.FormalPeriods`.
-/

universe u

namespace BoringMath.FormalPeriods

open CategoryTheory

variable {B K L : Type u} [Field B] [Field K] [Field L] [Algebra B K] [Algebra K L]
variable {A : Type u} [Category A] [Preadditive A] [AbelianCat A]
variable [∀ X Y : A, Module B (X ⟶ Y)]
variable [LinearCat A B]
variable {m n : ℕ}

/-! ## The evaluation map eval_∫ -/

-- Reference: Hörmann, arXiv:2106.03803, Def 2.5 (verified against the arXiv
-- HTML, v2): `eval_∫` sends `(σ ⊗ ω)_M` to `∫σ ω := ω(∫_M(σ))` — the pairing of
-- `ω ∈ H_dR(M)∨` with the base-changed comparison `∫_M(σ) ∈ H_dR(M) ⊗_K L`,
-- computed in the standard bases.
/-- The value of `eval_∫` on a symbol `(σ ⊗ ω)_M`: the pairing of `ω` with
`∫_M(σ)` (base changed to `L`), i.e. Hörmann's `ω(∫_M(σ))`. -/
def evalSym (Q : PeriodQuadruple A B K L) (M : A) (σ : FreeMod B (Q.hB.dim M))
    (ω : FreeModDual K (Q.hD.dim M)) : L :=
  pairL (algebraMap K L) ω ((Q.int M).toFun (baseChangeOf (algBL B K L) σ))

-- Reference: Lean 4 core (definitional unfolding of `evalSym`); primitive
-- definitional lemma.
/-- Unfolding of `evalSym`. -/
theorem evalSymEq (Q : PeriodQuadruple A B K L) (M : A) (σ : FreeMod B (Q.hB.dim M))
    (ω : FreeModDual K (Q.hD.dim M)) :
    evalSym Q M σ ω
      = pairL (algebraMap K L) ω ((Q.int M).toFun (baseChangeOf (algBL B K L) σ)) :=
  Eq.refl _

-- Reference: line 1073 (evalSymAddLeft, `rw [evalSymEq ...]` chain).
/-- Peel: `evalSym` on `σ₁ + σ₂` unfolds to the pairing of the sum of the
base-changed images under `∫_M`. -/
theorem evalSymAddLeftUnfold (Q : PeriodQuadruple A B K L) (M : A)
    (σ₁ σ₂ : FreeMod B (Q.hB.dim M)) (ω : FreeModDual K (Q.hD.dim M)) :
    evalSym Q M (σ₁ + σ₂) ω
      = pairL (algebraMap K L) ω
          ((Q.int M).toFun (baseChangeOf (algBL B K L) σ₁)
            + (Q.int M).toFun (baseChangeOf (algBL B K L) σ₂)) :=
  Eq.trans (evalSymEq Q M (σ₁ + σ₂) ω)
    (Eq.trans (congrArg (fun v => pairL (algebraMap K L) ω ((Q.int M).toFun v))
        (baseChangeOfAdd (algBL B K L) σ₁ σ₂))
      (congrArg (fun v => pairL (algebraMap K L) ω v)
        ((Q.int M).map_add' (baseChangeOf (algBL B K L) σ₁) (baseChangeOf (algBL B K L) σ₂))))

-- Reference: Hörmann, arXiv:2106.03803, Def 2.5 (`eval_∫` is linear); the proof
-- chains base-change additivity, linearity of `∫_M`, and `pairLAddRight`.
/-- `evalSym` is additive in the Betti argument `σ`. -/
theorem evalSymAddLeft (Q : PeriodQuadruple A B K L) (M : A)
    (σ₁ σ₂ : FreeMod B (Q.hB.dim M)) (ω : FreeModDual K (Q.hD.dim M)) :
    evalSym Q M (σ₁ + σ₂) ω = evalSym Q M σ₁ ω + evalSym Q M σ₂ ω :=
  Eq.trans (evalSymAddLeftUnfold Q M σ₁ σ₂ ω)
    (Eq.trans (pairLAddRight (algebraMap K L) ω ((Q.int M).toFun (baseChangeOf (algBL B K L) σ₁))
        ((Q.int M).toFun (baseChangeOf (algBL B K L) σ₂)))
      (Eq.trans (congrArg (fun w => w + evalSym Q M σ₂ ω) (evalSymEq Q M σ₁ ω))
        (congrArg (fun w => pairL (algebraMap K L) ω
            ((Q.int M).toFun (baseChangeOf (algBL B K L) σ₁)) + w) (evalSymEq Q M σ₂ ω))).symm)

-- Reference: line 1086 (evalSymSmulLeft, `rw [evalSymEq ...]` chain).
/-- Peel: `evalSym` on `c • σ` unfolds to the pairing of the scaled base-changed
image under `∫_M`. -/
theorem evalSymSmulLeftUnfold (Q : PeriodQuadruple A B K L) (M : A) (c : B)
    (σ : FreeMod B (Q.hB.dim M)) (ω : FreeModDual K (Q.hD.dim M)) :
    evalSym Q M (c • σ) ω
      = pairL (algebraMap K L) ω
          ((algBL B K L) c • (Q.int M).toFun (baseChangeOf (algBL B K L) σ)) :=
  Eq.trans (evalSymEq Q M (c • σ) ω)
    (Eq.trans (congrArg (fun v => pairL (algebraMap K L) ω ((Q.int M).toFun v))
        (baseChangeOfSmul (algBL B K L) c σ))
      (congrArg (fun v => pairL (algebraMap K L) ω v)
        ((Q.int M).map_smul' ((algBL B K L) c) (baseChangeOf (algBL B K L) σ))))

-- Reference: Hörmann, arXiv:2106.03803, Def 2.5; the proof chains base-change
-- linearity, linearity of `∫_M`, and `pairLSmulRight`.
/-- `evalSym` is `B`-linear in the Betti argument `σ`. -/
theorem evalSymSmulLeft (Q : PeriodQuadruple A B K L) (M : A) (c : B)
    (σ : FreeMod B (Q.hB.dim M)) (ω : FreeModDual K (Q.hD.dim M)) :
    evalSym Q M (c • σ) ω = (algBL B K L) c * evalSym Q M σ ω :=
  Eq.trans (evalSymSmulLeftUnfold Q M c σ ω)
    (Eq.trans (pairLSmulRight (algebraMap K L) ω ((algBL B K L) c)
        ((Q.int M).toFun (baseChangeOf (algBL B K L) σ)))
      (congrArg (fun w => (algBL B K L) c * w) (evalSymEq Q M σ ω)).symm)

-- Reference: Hörmann, arXiv:2106.03803, Def 2.5; `pairLAddLeft`.
/-- `evalSym` is additive in the dual argument `ω`. -/
theorem evalSymAddRight (Q : PeriodQuadruple A B K L) (M : A)
    (σ : FreeMod B (Q.hB.dim M)) (ω₁ ω₂ : FreeModDual K (Q.hD.dim M)) :
    evalSym Q M σ (ω₁ + ω₂) = evalSym Q M σ ω₁ + evalSym Q M σ ω₂ :=
  Eq.trans (evalSymEq Q M σ (ω₁ + ω₂))
    (Eq.trans (pairLAddLeft (algebraMap K L) ω₁ ω₂
        ((Q.int M).toFun (baseChangeOf (algBL B K L) σ)))
      (Eq.trans (congrArg (fun w => w + evalSym Q M σ ω₂) (evalSymEq Q M σ ω₁))
        (congrArg (fun w => pairL (algebraMap K L) ω₁
            ((Q.int M).toFun (baseChangeOf (algBL B K L) σ)) + w) (evalSymEq Q M σ ω₂))).symm)

-- Reference: Hörmann, arXiv:2106.03803, Def 2.5; `pairLSmulLeft` (the `B`-action
-- on `H_dR(M)∨` is via `algebraMap B K`, and `algBL` is the composite
-- `B → K → L`, definitionally).
/-- `evalSym` is `B`-linear in the dual argument `ω`. -/
theorem evalSymSmulRight (Q : PeriodQuadruple A B K L) (M : A) (c : B)
    (σ : FreeMod B (Q.hB.dim M)) (ω : FreeModDual K (Q.hD.dim M)) :
    evalSym Q M σ (c • ω) = (algBL B K L) c * evalSym Q M σ ω :=
  Eq.trans (evalSymEq Q M σ (c • ω))
    (Eq.trans (pairLSmulLeft (algebraMap K L) (algebraMap B K c) ω
        ((Q.int M).toFun (baseChangeOf (algBL B K L) σ)))
      (congrArg (fun w => (algebraMap K L) (algebraMap B K c) * w) (evalSymEq Q M σ ω)).symm)

-- Reference: Hörmann, arXiv:2106.03803, Def 2.5 (bilinearity kills zero);
-- base change kills zero, `∫_M` kills zero, `pairLZeroRight`.
/-- `evalSym` vanishes at `σ = 0`. -/
theorem evalSymZeroLeft (Q : PeriodQuadruple A B K L) (M : A)
    (ω : FreeModDual K (Q.hD.dim M)) : evalSym Q M 0 ω = 0 :=
  Eq.trans (evalSymEq Q M 0 ω)
    (Eq.trans (congrArg (fun v => pairL (algebraMap K L) ω ((Q.int M).toFun v))
        (baseChangeOfZero (algBL B K L)))
      (Eq.trans (congrArg (fun v => pairL (algebraMap K L) ω v) (freeModHomMapZero (Q.int M)))
        (pairLZeroRight (algebraMap K L) ω)))

-- Reference: Hörmann, arXiv:2106.03803, Def 2.5 (bilinearity kills zero);
-- `pairLZeroLeft`.
/-- `evalSym` vanishes at `ω = 0`. -/
theorem evalSymZeroRight (Q : PeriodQuadruple A B K L) (M : A)
    (σ : FreeMod B (Q.hB.dim M)) : evalSym Q M σ 0 = 0 :=
  Eq.trans (evalSymEq Q M σ 0)
    (pairLZeroLeft (algebraMap K L) ((Q.int M).toFun (baseChangeOf (algBL B K L) σ)))

-- Reference: Hörmann, arXiv:2106.03803, Def 2.3 relation (2) + 2.2 (naturality
-- of `∫`): the morphism case of eval_∫'s well-definedness is exactly
-- `evalSym M σ (α∨ ω) = evalSym N (α σ) ω`, which follows from naturality of
-- `∫` (`intNat`) via the key pairing identity `pairLBaseHom` and the base-change
-- commutation `baseChangeHomOfApply`.
/-- The morphism-relation case: `ω(∫_M σ)` with `ω` replaced by `α∨(ω)` equals
`(α σ)` paired with `ω` at `N` — naturality of `∫`. -/
theorem evalSymMorph (Q : PeriodQuadruple A B K L) {M N : A} (α : M ⟶ N)
    (σ : FreeMod B (Q.hB.dim M)) (ω : FreeModDual K (Q.hD.dim N)) :
    evalSym Q M σ (dualMap (Q.hD.map α) ω)
      = evalSym Q N ((Q.hB.map α).toFun σ) ω := by
  have hint : (Q.int N).toFun
        ((baseChangeHomOf (algBL B K L) (Q.hB.map α)).toFun
          (baseChangeOf (algBL B K L) σ))
      = (baseChangeHomOf (algebraMap K L) (Q.hD.map α)).toFun
          ((Q.int M).toFun (baseChangeOf (algBL B K L) σ)) :=
    congrArg (fun F : FreeModHom L (Q.hB.dim M) (Q.hD.dim N) =>
      F.toFun (baseChangeOf (algBL B K L) σ)) (Q.intNat α)
  calc evalSym Q M σ (dualMap (Q.hD.map α) ω)
      = pairL (algebraMap K L) (dualMap (Q.hD.map α) ω)
          ((Q.int M).toFun (baseChangeOf (algBL B K L) σ)) :=
          evalSymEq Q M σ (dualMap (Q.hD.map α) ω)
    _ = pairL (algebraMap K L) ω ((baseChangeHomOf (algebraMap K L) (Q.hD.map α)).toFun
          ((Q.int M).toFun (baseChangeOf (algBL B K L) σ))) :=
          (pairLBaseHom (algebraMap K L) (Q.hD.map α) ω
            ((Q.int M).toFun (baseChangeOf (algBL B K L) σ))).symm
    _ = pairL (algebraMap K L) ω ((Q.int N).toFun
          ((baseChangeHomOf (algBL B K L) (Q.hB.map α)).toFun
            (baseChangeOf (algBL B K L) σ))) :=
          congrArg (fun v => pairL (algebraMap K L) ω v) hint.symm
    _ = pairL (algebraMap K L) ω ((Q.int N).toFun
          (baseChangeOf (algBL B K L) ((Q.hB.map α).toFun σ))) :=
          congrArg (fun v => pairL (algebraMap K L) ω ((Q.int N).toFun v))
            (baseChangeHomOfApply (algBL B K L) (Q.hB.map α) σ).symm
    _ = evalSym Q N ((Q.hB.map α).toFun σ) ω :=
          (evalSymEq Q N ((Q.hB.map α).toFun σ) ω).symm

-- Reference: Hörmann, arXiv:2106.03803, Def 2.5 (eval_∫ is defined on symbols
-- by `(σ⊗ω)_M ↦ ω(∫_M(σ))` and extended linearly); Dummit–Foote, §10.4 (the
-- lift to the free module on symbols, by recursion on formal sums).
/-- The raw evaluation on formal sums: the empty sum maps to `0`, a symbol
`(σ ⊗ ω)_M` maps to `ω(∫_M(σ))`, addition and `B`-scalars map to the
operations of `L` (via `algBL`). -/
def evalRaw (Q : PeriodQuadruple A B K L) : PeriodSym Q → L
  | PeriodSym.nil => 0
  | PeriodSym.sym M σ ω => evalSym Q M σ ω
  | PeriodSym.add x y => evalRaw Q x + evalRaw Q y
  | PeriodSym.smul c x => (algBL B K L) c * evalRaw Q x

-- Reference: Lean 4 core (definitional unfolding of `evalRaw`); primitive
-- definitional lemma.
/-- The empty formal sum evaluates to `0`. -/
theorem evalRawNil (Q : PeriodQuadruple A B K L) : evalRaw Q PeriodSym.nil = 0 := Eq.refl _

-- Reference: Lean 4 core (definitional unfolding of `evalRaw`); primitive
-- definitional lemma.
/-- A symbol `(σ ⊗ ω)_M` evaluates to `ω(∫_M(σ))`. -/
theorem evalRawSym (Q : PeriodQuadruple A B K L) (M : A) (σ : FreeMod B (Q.hB.dim M))
    (ω : FreeModDual K (Q.hD.dim M)) :
    evalRaw Q (PeriodSym.sym M σ ω) = evalSym Q M σ ω := Eq.refl _

-- Reference: Lean 4 core (definitional unfolding of `evalRaw`); primitive
-- definitional lemma.
/-- Formal sums evaluate to sums of values. -/
theorem evalRawAdd (Q : PeriodQuadruple A B K L) (x y : PeriodSym Q) :
    evalRaw Q (PeriodSym.add x y) = evalRaw Q x + evalRaw Q y := Eq.refl _

-- Reference: Lean 4 core (definitional unfolding of `evalRaw`); primitive
-- definitional lemma.
/-- Formal scalar multiples evaluate to scalar multiples. -/
theorem evalRawSmul (Q : PeriodQuadruple A B K L) (c : B) (x : PeriodSym Q) :
    evalRaw Q (PeriodSym.smul c x) = (algBL B K L) c * evalRaw Q x := Eq.refl _


end BoringMath.FormalPeriods
