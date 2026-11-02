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
import Mathlib.Algebra.Field.Rat
import Mathlib.Data.Quot
import BoringMath.FormalPeriods.FreeMod
import BoringMath.FormalPeriods.AxiomLint
import BoringMath.FormalPeriods.FormalPeriods.FinSum
import BoringMath.FormalPeriods.FormalPeriods.LinearAbelian
import BoringMath.FormalPeriods.FormalPeriods.Quadruple
import BoringMath.FormalPeriods.FormalPeriods.Symbols
import BoringMath.FormalPeriods.FormalPeriods.Quotient
import BoringMath.FormalPeriods.FormalPeriods.Dual
import BoringMath.FormalPeriods.FormalPeriods.BaseChange
import BoringMath.FormalPeriods.FormalPeriods.PairL
import BoringMath.FormalPeriods.FormalPeriods.EvalSym

/-!
# The evaluation map `eval_∫`

Well-definedness of `evalRaw` on the quotient (induction on the witness
chain; the morphism-relation case is exactly the naturality of `∫`), the
descended map `eval : P Q → L` with `evalMk`/`evalSymMk`, the smoke test,
and the axiom lint.  Split out of `BoringMath.FormalPeriods.FormalPeriods`.
-/

universe u

namespace BoringMath.FormalPeriods

open CategoryTheory

variable {B K L : Type u} [Field B] [Field K] [Field L] [Algebra B K] [Algebra K L]
variable {A : Type u} [Category A] [Preadditive A] [AbelianCat A]
variable [∀ X Y : A, Module B (X ⟶ Y)]
variable [LinearCat A B]
variable {m n : ℕ}

-- Reference: line 1221 (eval_well_defined, addLeft case).
/-- Peel: `evalRaw` respects `PeriodChain.addLeft`. -/
theorem evalWellDefinedAddLeft (Q : PeriodQuadruple A B K L) (z x y : PeriodSym Q)
    (ih : evalRaw Q x = evalRaw Q y) :
    evalRaw Q (PeriodSym.add z x) = evalRaw Q (PeriodSym.add z y) :=
  Eq.trans (evalRawAdd Q z x)
    (Eq.trans (congrArg (fun w => evalRaw Q z + w) ih) (evalRawAdd Q z y).symm)

-- Reference: line 1225 (eval_well_defined, addRight case).
/-- Peel: `evalRaw` respects `PeriodChain.addRight`. -/
theorem evalWellDefinedAddRight (Q : PeriodQuadruple A B K L) (x y z : PeriodSym Q)
    (ih : evalRaw Q x = evalRaw Q y) :
    evalRaw Q (PeriodSym.add x z) = evalRaw Q (PeriodSym.add y z) :=
  Eq.trans (evalRawAdd Q x z)
    (Eq.trans (congrArg (fun w => w + evalRaw Q z) ih) (evalRawAdd Q y z).symm)

-- Reference: line 1229 (eval_well_defined, smulC case).
/-- Peel: `evalRaw` respects `PeriodChain.smulC`. -/
theorem evalWellDefinedSmulC (Q : PeriodQuadruple A B K L) (c : B) (x y : PeriodSym Q)
    (ih : evalRaw Q x = evalRaw Q y) :
    evalRaw Q (PeriodSym.smul c x) = evalRaw Q (PeriodSym.smul c y) :=
  Eq.trans (evalRawSmul Q c x)
    (Eq.trans (congrArg (fun w => (algBL B K L) c * w) ih) (evalRawSmul Q c y).symm)

-- Reference: line 1233 (eval_well_defined, nilLeft case).
/-- Peel: `evalRaw` respects `PeriodChain.nilLeft`. -/
theorem evalWellDefinedNilLeft (Q : PeriodQuadruple A B K L) (x : PeriodSym Q) :
    evalRaw Q (PeriodSym.add PeriodSym.nil x) = evalRaw Q x :=
  Eq.trans (evalRawAdd Q PeriodSym.nil x)
    (Eq.trans (congrArg (fun w => w + evalRaw Q x) (evalRawNil Q)) (zero_add (evalRaw Q x)))

-- Reference: line 1236 (eval_well_defined, nilRight case).
/-- Peel: `evalRaw` respects `PeriodChain.nilRight`. -/
theorem evalWellDefinedNilRight (Q : PeriodQuadruple A B K L) (x : PeriodSym Q) :
    evalRaw Q (PeriodSym.add x PeriodSym.nil) = evalRaw Q x :=
  Eq.trans (evalRawAdd Q x PeriodSym.nil)
    (Eq.trans (congrArg (fun w => evalRaw Q x + w) (evalRawNil Q)) (add_zero (evalRaw Q x)))

-- Reference: line 1239 (eval_well_defined, addAssoc case).
/-- Peel: `evalRaw` respects `PeriodChain.addAssoc`. -/
theorem evalWellDefinedAddAssoc (Q : PeriodQuadruple A B K L) (x y z : PeriodSym Q) :
    evalRaw Q (PeriodSym.add (PeriodSym.add x y) z)
      = evalRaw Q (PeriodSym.add x (PeriodSym.add y z)) :=
  Eq.trans (evalRawAdd Q (PeriodSym.add x y) z)
    (Eq.trans (congrArg (fun w => w + evalRaw Q z) (evalRawAdd Q x y))
      (Eq.trans (add_assoc (evalRaw Q x) (evalRaw Q y) (evalRaw Q z))
        (Eq.trans (congrArg (fun w => evalRaw Q x + w) (evalRawAdd Q y z).symm)
          (evalRawAdd Q x (PeriodSym.add y z)).symm)))

-- Reference: line 1244 (eval_well_defined, addComm case).
/-- Peel: `evalRaw` respects `PeriodChain.addComm`. -/
theorem evalWellDefinedAddComm (Q : PeriodQuadruple A B K L) (x y : PeriodSym Q) :
    evalRaw Q (PeriodSym.add x y) = evalRaw Q (PeriodSym.add y x) :=
  Eq.trans (evalRawAdd Q x y)
    (Eq.trans (add_comm (evalRaw Q x) (evalRaw Q y)) (evalRawAdd Q y x).symm)

-- Reference: line 1247 (eval_well_defined, smulNil case).
/-- Peel: `evalRaw` respects `PeriodChain.smulNil`. -/
theorem evalWellDefinedSmulNil (Q : PeriodQuadruple A B K L) (c : B) :
    evalRaw Q (PeriodSym.smul c PeriodSym.nil) = evalRaw Q PeriodSym.nil :=
  Eq.trans (evalRawSmul Q c PeriodSym.nil)
    (Eq.trans (congrArg (fun w => (algBL B K L) c * w) (evalRawNil Q))
      (Eq.trans (mul_zero ((algBL B K L) c)) (evalRawNil Q).symm))

-- Reference: line 1250 (eval_well_defined, smulAdd case).
/-- Peel: `evalRaw` respects `PeriodChain.smulAdd`. -/
theorem evalWellDefinedSmulAdd (Q : PeriodQuadruple A B K L) (c : B) (x y : PeriodSym Q) :
    evalRaw Q (PeriodSym.smul c (PeriodSym.add x y))
      = evalRaw Q (PeriodSym.add (PeriodSym.smul c x) (PeriodSym.smul c y)) :=
  Eq.trans (evalRawSmul Q c (PeriodSym.add x y))
    (Eq.trans (congrArg (fun w => (algBL B K L) c * w) (evalRawAdd Q x y))
      (Eq.trans (mul_add ((algBL B K L) c) (evalRaw Q x) (evalRaw Q y))
        (Eq.trans (congrArg (fun w => (algBL B K L) c * evalRaw Q x + w) (evalRawSmul Q c y).symm)
          (Eq.trans (congrArg (fun w => w + evalRaw Q (PeriodSym.smul c y))
              (evalRawSmul Q c x).symm)
            (evalRawAdd Q (PeriodSym.smul c x) (PeriodSym.smul c y)).symm))))

-- Reference: line 1255 (eval_well_defined, addSmul case).
/-- Peel: `evalRaw` respects `PeriodChain.addSmul`. -/
theorem evalWellDefinedAddSmul (Q : PeriodQuadruple A B K L) (a b : B) (x : PeriodSym Q) :
    evalRaw Q (PeriodSym.smul (a + b) x)
      = evalRaw Q (PeriodSym.add (PeriodSym.smul a x) (PeriodSym.smul b x)) :=
  Eq.trans (evalRawSmul Q (a + b) x)
    (Eq.trans (congrArg (fun w => w * evalRaw Q x) (map_add (algBL B K L) a b))
      (Eq.trans (add_mul ((algBL B K L) a) ((algBL B K L) b) (evalRaw Q x))
        (Eq.trans (congrArg (fun w => w + (algBL B K L) b * evalRaw Q x) (evalRawSmul Q a x).symm)
          (Eq.trans (congrArg (fun w => evalRaw Q (PeriodSym.smul a x) + w)
              (evalRawSmul Q b x).symm)
            (evalRawAdd Q (PeriodSym.smul a x) (PeriodSym.smul b x)).symm))))

-- Reference: line 1259 (eval_well_defined, oneSmul case).
/-- Peel: `evalRaw` respects `PeriodChain.oneSmul`. -/
theorem evalWellDefinedOneSmul (Q : PeriodQuadruple A B K L) (x : PeriodSym Q) :
    evalRaw Q (PeriodSym.smul 1 x) = evalRaw Q x :=
  Eq.trans (evalRawSmul Q 1 x)
    (Eq.trans (congrArg (fun w => w * evalRaw Q x) (map_one (algBL B K L)))
      (one_mul (evalRaw Q x)))

-- Reference: line 1262 (eval_well_defined, zeroSmul case).
/-- Peel: `evalRaw` respects `PeriodChain.zeroSmul`. -/
theorem evalWellDefinedZeroSmul (Q : PeriodQuadruple A B K L) (x : PeriodSym Q) :
    evalRaw Q (PeriodSym.smul 0 x) = evalRaw Q PeriodSym.nil :=
  Eq.trans (evalRawSmul Q 0 x)
    (Eq.trans (congrArg (fun w => w * evalRaw Q x) (map_zero (algBL B K L)))
      (Eq.trans (zero_mul (evalRaw Q x)) (evalRawNil Q).symm))

-- Reference: line 1265 (eval_well_defined, smulSmul case).
/-- Peel: `evalRaw` respects `PeriodChain.smulSmul`. -/
theorem evalWellDefinedSmulSmul (Q : PeriodQuadruple A B K L) (a b : B) (x : PeriodSym Q) :
    evalRaw Q (PeriodSym.smul a (PeriodSym.smul b x))
      = evalRaw Q (PeriodSym.smul (a * b) x) :=
  Eq.trans (evalRawSmul Q a (PeriodSym.smul b x))
    (Eq.trans (congrArg (fun w => (algBL B K L) a * w) (evalRawSmul Q b x))
      (Eq.trans (mul_assoc ((algBL B K L) a) ((algBL B K L) b) (evalRaw Q x)).symm
        (Eq.trans (congrArg (fun w => w * evalRaw Q x) (map_mul (algBL B K L) a b).symm)
          (evalRawSmul Q (a * b) x).symm)))

-- Reference: line 1269 (eval_well_defined, zeroSymRight case).
/-- Peel: `evalRaw` respects `PeriodChain.zeroSymRight`. -/
theorem evalWellDefinedZeroSymRight (Q : PeriodQuadruple A B K L) (x : PeriodSym Q)
    (M : A) (σ : FreeMod B (Q.hB.dim M)) :
    evalRaw Q (PeriodSym.add x (PeriodSym.sym M σ 0)) = evalRaw Q x :=
  Eq.trans (evalRawAdd Q x (PeriodSym.sym M σ 0))
    (Eq.trans (congrArg (fun w => evalRaw Q x + w) (evalRawSym Q M σ 0))
      (Eq.trans (congrArg (fun w => evalRaw Q x + w) (evalSymZeroRight Q M σ))
        (add_zero (evalRaw Q x))))

-- Reference: line 1273 (eval_well_defined, zeroSymLeft case).
/-- Peel: `evalRaw` respects `PeriodChain.zeroSymLeft`. -/
theorem evalWellDefinedZeroSymLeft (Q : PeriodQuadruple A B K L) (x : PeriodSym Q)
    (M : A) (ω : FreeModDual K (Q.hD.dim M)) :
    evalRaw Q (PeriodSym.add x (PeriodSym.sym M 0 ω)) = evalRaw Q x :=
  Eq.trans (evalRawAdd Q x (PeriodSym.sym M 0 ω))
    (Eq.trans (congrArg (fun w => evalRaw Q x + w) (evalRawSym Q M 0 ω))
      (Eq.trans (congrArg (fun w => evalRaw Q x + w) (evalSymZeroLeft Q M ω))
        (add_zero (evalRaw Q x))))

-- Reference: line 1277 (eval_well_defined, addSymLeft case).
/-- Peel: `evalRaw` respects `PeriodChain.addSymLeft`. -/
theorem evalWellDefinedAddSymLeft (Q : PeriodQuadruple A B K L) (x : PeriodSym Q)
    (M : A) (σ₁ σ₂ : FreeMod B (Q.hB.dim M)) (ω : FreeModDual K (Q.hD.dim M)) :
    evalRaw Q (PeriodSym.add x (PeriodSym.add (PeriodSym.sym M σ₁ ω) (PeriodSym.sym M σ₂ ω)))
      = evalRaw Q (PeriodSym.add x (PeriodSym.sym M (σ₁ + σ₂) ω)) :=
  Eq.trans (evalRawAdd Q x (PeriodSym.add (PeriodSym.sym M σ₁ ω) (PeriodSym.sym M σ₂ ω)))
    (Eq.trans (congrArg (fun w => evalRaw Q x + w)
        (evalRawAdd Q (PeriodSym.sym M σ₁ ω) (PeriodSym.sym M σ₂ ω)))
      (Eq.trans (congrArg (fun w => evalRaw Q x + w)
          (Eq.trans (congrArg (fun w => w + evalRaw Q (PeriodSym.sym M σ₂ ω))
              (evalRawSym Q M σ₁ ω))
            (congrArg (fun w => evalSym Q M σ₁ ω + w) (evalRawSym Q M σ₂ ω))))
        (Eq.trans (congrArg (fun w => evalRaw Q x + w) (evalSymAddLeft Q M σ₁ σ₂ ω)).symm
          (Eq.trans (congrArg (fun w => evalRaw Q x + w) (evalRawSym Q M (σ₁ + σ₂) ω)).symm
            (evalRawAdd Q x (PeriodSym.sym M (σ₁ + σ₂) ω)).symm))))

-- Reference: line 1284 (eval_well_defined, addSymRight case).
/-- Peel: `evalRaw` respects `PeriodChain.addSymRight`. -/
theorem evalWellDefinedAddSymRight (Q : PeriodQuadruple A B K L) (x : PeriodSym Q)
    (M : A) (σ : FreeMod B (Q.hB.dim M)) (ω₁ ω₂ : FreeModDual K (Q.hD.dim M)) :
    evalRaw Q (PeriodSym.add x (PeriodSym.add (PeriodSym.sym M σ ω₁) (PeriodSym.sym M σ ω₂)))
      = evalRaw Q (PeriodSym.add x (PeriodSym.sym M σ (ω₁ + ω₂))) :=
  Eq.trans (evalRawAdd Q x (PeriodSym.add (PeriodSym.sym M σ ω₁) (PeriodSym.sym M σ ω₂)))
    (Eq.trans (congrArg (fun w => evalRaw Q x + w)
        (evalRawAdd Q (PeriodSym.sym M σ ω₁) (PeriodSym.sym M σ ω₂)))
      (Eq.trans (congrArg (fun w => evalRaw Q x + w)
          (Eq.trans (congrArg (fun w => w + evalRaw Q (PeriodSym.sym M σ ω₂))
              (evalRawSym Q M σ ω₁))
            (congrArg (fun w => evalSym Q M σ ω₁ + w) (evalRawSym Q M σ ω₂))))
        (Eq.trans (congrArg (fun w => evalRaw Q x + w) (evalSymAddRight Q M σ ω₁ ω₂)).symm
          (Eq.trans (congrArg (fun w => evalRaw Q x + w) (evalRawSym Q M σ (ω₁ + ω₂))).symm
            (evalRawAdd Q x (PeriodSym.sym M σ (ω₁ + ω₂))).symm))))

-- Reference: line 1291 (eval_well_defined, smulSym case).
/-- Peel: `evalRaw` respects `PeriodChain.smulSym`. -/
theorem evalWellDefinedSmulSym (Q : PeriodQuadruple A B K L) (x : PeriodSym Q)
    (M : A) (σ : FreeMod B (Q.hB.dim M)) (ω : FreeModDual K (Q.hD.dim M)) (c : B) :
    evalRaw Q (PeriodSym.add x (PeriodSym.sym M σ (c • ω)))
      = evalRaw Q (PeriodSym.add x (PeriodSym.sym M (c • σ) ω)) :=
  Eq.trans (evalRawAdd Q x (PeriodSym.sym M σ (c • ω)))
    (Eq.trans (congrArg (fun w => evalRaw Q x + w) (evalRawSym Q M σ (c • ω)))
      (Eq.trans (congrArg (fun w => evalRaw Q x + w)
          (Eq.trans (evalSymSmulRight Q M c σ ω) (evalSymSmulLeft Q M c σ ω).symm))
        (Eq.trans (congrArg (fun w => evalRaw Q x + w) (evalRawSym Q M (c • σ) ω)).symm
          (evalRawAdd Q x (PeriodSym.sym M (c • σ) ω)).symm)))

-- Reference: line 1297 (eval_well_defined, smulSymLeft case).
/-- Peel: `evalRaw` respects `PeriodChain.smulSymLeft`. -/
theorem evalWellDefinedSmulSymLeft (Q : PeriodQuadruple A B K L) (x : PeriodSym Q)
    (M : A) (σ : FreeMod B (Q.hB.dim M)) (ω : FreeModDual K (Q.hD.dim M)) (c : B) :
    evalRaw Q (PeriodSym.add x (PeriodSym.smul c (PeriodSym.sym M σ ω)))
      = evalRaw Q (PeriodSym.add x (PeriodSym.sym M (c • σ) ω)) :=
  Eq.trans (evalRawAdd Q x (PeriodSym.smul c (PeriodSym.sym M σ ω)))
    (Eq.trans (congrArg (fun w => evalRaw Q x + w) (evalRawSmul Q c (PeriodSym.sym M σ ω)))
      (Eq.trans (congrArg (fun w => evalRaw Q x + w)
          (congrArg (fun w => (algBL B K L) c * w) (evalRawSym Q M σ ω)))
        (Eq.trans (congrArg (fun w => evalRaw Q x + w) (evalSymSmulLeft Q M c σ ω).symm)
          (Eq.trans (congrArg (fun w => evalRaw Q x + w) (evalRawSym Q M (c • σ) ω)).symm
            (evalRawAdd Q x (PeriodSym.sym M (c • σ) ω)).symm))))

-- Reference: line 1303 (eval_well_defined, morphRel case).
/-- Peel: `evalRaw` respects `PeriodChain.morphRel`. -/
theorem evalWellDefinedMorphRel (Q : PeriodQuadruple A B K L) (x : PeriodSym Q)
    {M N : A} (α : M ⟶ N) (σ : FreeMod B (Q.hB.dim M)) (ω : FreeModDual K (Q.hD.dim N)) :
    evalRaw Q (PeriodSym.add x (PeriodSym.sym M σ (dualMap (Q.hD.map α) ω)))
      = evalRaw Q (PeriodSym.add x (PeriodSym.sym N ((Q.hB.map α).toFun σ) ω)) :=
  Eq.trans (evalRawAdd Q x (PeriodSym.sym M σ (dualMap (Q.hD.map α) ω)))
    (Eq.trans (congrArg (fun w => evalRaw Q x + w)
        (evalRawSym Q M σ (dualMap (Q.hD.map α) ω)))
      (Eq.trans (congrArg (fun w => evalRaw Q x + w) (evalSymMorph Q α σ ω))
        (Eq.trans (congrArg (fun w => evalRaw Q x + w)
            (evalRawSym Q N ((Q.hB.map α).toFun σ) ω)).symm
          (evalRawAdd Q x (PeriodSym.sym N ((Q.hB.map α).toFun σ) ω)).symm)))

-- Reference: Hörmann, arXiv:2106.03803, Def 2.3 + Def 2.5 (eval_∫ is
-- well-defined on the quotient P(𝒜) — the main theorem of ticket P.4): the
-- raw evaluation respects every generator of the witness-carrying relation;
-- the morphism-relation case is `evalSymMorph` (naturality of `∫`), the
-- bilinearity cases are the `evalSym` linearity lemmas, and the free-module
-- cases are the module laws of `L`.  Proved by induction on the witness
-- `PeriodChain`, exactly as `tensorSymLiftRel` in
-- `BoringMath.FormalPeriods.FreeTensor`.
/-- **eval_∫ is well-defined on the quotient**: the raw evaluation respects the
witness-carrying relation, so it descends to `P(𝒜)`. -/
theorem eval_well_defined (Q : PeriodQuadruple A B K L) (x y : PeriodSym Q)
    (h : periodRel Q x y) : evalRaw Q x = evalRaw Q y := by
  obtain ⟨ch⟩ := h
  induction ch
  case refl x => exact Eq.refl _
  case symm x y ch ih => exact Eq.symm ih
  case trans x y z c₁ c₂ ih₁ ih₂ => exact Eq.trans ih₁ ih₂
  case addLeft x y z ch ih => exact evalWellDefinedAddLeft Q z x y ih
  case addRight x y z ch ih => exact evalWellDefinedAddRight Q x y z ih
  case smulC c x y hch ih => exact evalWellDefinedSmulC Q c x y ih
  case nilLeft x => exact evalWellDefinedNilLeft Q x
  case nilRight x => exact evalWellDefinedNilRight Q x
  case addAssoc x y z => exact evalWellDefinedAddAssoc Q x y z
  case addComm x y => exact evalWellDefinedAddComm Q x y
  case smulNil c => exact evalWellDefinedSmulNil Q c
  case smulAdd c x y => exact evalWellDefinedSmulAdd Q c x y
  case addSmul a b x => exact evalWellDefinedAddSmul Q a b x
  case oneSmul x => exact evalWellDefinedOneSmul Q x
  case zeroSmul x => exact evalWellDefinedZeroSmul Q x
  case smulSmul a b x => exact evalWellDefinedSmulSmul Q a b x
  case zeroSymRight x M σ => exact evalWellDefinedZeroSymRight Q x M σ
  case zeroSymLeft x M ω => exact evalWellDefinedZeroSymLeft Q x M ω
  case addSymLeft x M σ₁ σ₂ ω => exact evalWellDefinedAddSymLeft Q x M σ₁ σ₂ ω
  case addSymRight x M σ ω₁ ω₂ => exact evalWellDefinedAddSymRight Q x M σ ω₁ ω₂
  case smulSym x M σ ω c => exact evalWellDefinedSmulSym Q x M σ ω c
  case smulSymLeft x M σ ω c => exact evalWellDefinedSmulSymLeft Q x M σ ω c
  case morphRel x M N α σ ω => exact evalWellDefinedMorphRel Q x α σ ω

-- Reference: Hörmann, arXiv:2106.03803, Def 2.5 (verified against the arXiv
-- HTML, v2): `eval_∫ : P(𝒜) → ℂ` (here `L`) is the `K`-linear map
-- `(σ⊗ω)_M ↦ ∫σ ω := ω(∫_M(σ))`; Dummit–Foote, §10.4 (the lift descends to
-- the quotient); Lean 4 core, Init/Prelude.lean (`Quot.lift`).  Well-definedness
-- is `eval_well_defined`, the main theorem of ticket P.4.
/-- The evaluation map `eval_∫ : P(𝒜) → L`, descended from the raw evaluation
by `Quot.lift` (well-defined by `eval_well_defined`). -/
def eval (Q : PeriodQuadruple A B K L) : P Q → L :=
  Quot.lift (evalRaw Q) (fun x y h => eval_well_defined Q x y h)

-- Reference: mathlib, Mathlib/Data/Quot.lean (`Quot.lift_mk`, proved by `rfl`);
-- primitive definitional lemma.
/-- The lift of the raw evaluation on a class is the raw evaluation. -/
theorem evalMk (Q : PeriodQuadruple A B K L) (x : PeriodSym Q) :
    eval Q (Quot.mk (periodRel Q) x) = evalRaw Q x :=
  Quot.lift_mk (evalRaw Q) (fun x y h => eval_well_defined Q x y h) x

-- Reference: Hörmann, arXiv:2106.03803, Def 2.5 (the formula
-- `eval_∫ (σ⊗ω)_M = ω(∫_M(σ))`).
/-- The beta rule of `eval_∫`: `eval_∫ (σ⊗ω)_M = ω(∫_M(σ))`. -/
theorem evalSymMk (Q : PeriodQuadruple A B K L) (M : A) (σ : FreeMod B (Q.hB.dim M))
    (ω : FreeModDual K (Q.hD.dim M)) :
    eval Q (Quot.mk (periodRel Q) (PeriodSym.sym M σ ω)) = evalSym Q M σ ω :=
  Eq.trans (evalMk Q (PeriodSym.sym M σ ω)) (evalRawSym Q M σ ω)

/-! ## Smoke test -/

-- Reference: smoke test for the P.4 acceptance criterion (usable at concrete
-- fields; unlinted like the `ℚ` examples in `BoringMath.FormalPeriods.FreeTensor`,
-- since `Rat.instField` is choice-tainted at the pin).
/-- Smoke test: the key pairing identity `ω(φ f x) = (f∨ ω)(x)` at `K = L = ℚ`. -/
example {m n : ℕ} (f : FreeModHom ℚ m n) (ω : FreeModDual ℚ n) (x : FreeMod ℚ m) :
    pairL (RingHom.id ℚ) ω ((baseChangeHomOf (RingHom.id ℚ) f).toFun x)
      = pairL (RingHom.id ℚ) (dualMap f ω) x :=
  pairLBaseHom (RingHom.id ℚ) f ω x

/-! ## Axiom lint -/

#lint_axioms BoringMath.FormalPeriods.finSum
#lint_axioms BoringMath.FormalPeriods.listSum_congr
#lint_axioms BoringMath.FormalPeriods.listSum_map_add
#lint_axioms BoringMath.FormalPeriods.listSum_map_mul_left
#lint_axioms BoringMath.FormalPeriods.listSum_apply
#lint_axioms BoringMath.FormalPeriods.listSum_zero
#lint_axioms BoringMath.FormalPeriods.listSum_ite_zero
#lint_axioms BoringMath.FormalPeriods.listSum_ite_mem
#lint_axioms BoringMath.FormalPeriods.finSum_ite
#lint_axioms BoringMath.FormalPeriods.mapListSum
#lint_axioms BoringMath.FormalPeriods.LinearCat
#lint_axioms BoringMath.FormalPeriods.AbelianCat
#lint_axioms BoringMath.FormalPeriods.freeModHomZeroInst
#lint_axioms BoringMath.FormalPeriods.freeModHomAddInst
#lint_axioms BoringMath.FormalPeriods.freeModHomSMulKInst
#lint_axioms BoringMath.FormalPeriods.freeModHomSMulBInst
#lint_axioms BoringMath.FormalPeriods.freeModHomMapZero
#lint_axioms BoringMath.FormalPeriods.freeModEqSumSingle
#lint_axioms BoringMath.FormalPeriods.freeModHomMapListSum
#lint_axioms BoringMath.FormalPeriods.freeModHomMapSum
#lint_axioms BoringMath.FormalPeriods.precompDual
#lint_axioms BoringMath.FormalPeriods.dualMap
#lint_axioms BoringMath.FormalPeriods.dualVal
#lint_axioms BoringMath.FormalPeriods.dualValDualMap
#lint_axioms BoringMath.FormalPeriods.dualValAdd
#lint_axioms BoringMath.FormalPeriods.dualValSmul
#lint_axioms BoringMath.FormalPeriods.dualValZero
#lint_axioms BoringMath.FormalPeriods.dualValEqSum
#lint_axioms BoringMath.FormalPeriods.algBL
#lint_axioms BoringMath.FormalPeriods.baseChangeOf
#lint_axioms BoringMath.FormalPeriods.baseChangeOfAdd
#lint_axioms BoringMath.FormalPeriods.baseChangeOfSmul
#lint_axioms BoringMath.FormalPeriods.baseChangeOfZero
#lint_axioms BoringMath.FormalPeriods.baseChangeHomOfFun
#lint_axioms BoringMath.FormalPeriods.baseChangeHomOfFunAdd
#lint_axioms BoringMath.FormalPeriods.baseChangeHomOfFunSmul
#lint_axioms BoringMath.FormalPeriods.baseChangeHomOf
#lint_axioms BoringMath.FormalPeriods.baseChangeHomOfDecomp
#lint_axioms BoringMath.FormalPeriods.baseChangeHomOfApply
#lint_axioms BoringMath.FormalPeriods.pairL
#lint_axioms BoringMath.FormalPeriods.pairLAddRight
#lint_axioms BoringMath.FormalPeriods.pairLSmulRight
#lint_axioms BoringMath.FormalPeriods.pairLZeroRight
#lint_axioms BoringMath.FormalPeriods.pairLListSum
#lint_axioms BoringMath.FormalPeriods.pairLSumRight
#lint_axioms BoringMath.FormalPeriods.pairLAddLeft
#lint_axioms BoringMath.FormalPeriods.pairLSmulLeft
#lint_axioms BoringMath.FormalPeriods.pairLZeroLeft
#lint_axioms BoringMath.FormalPeriods.pairLBase
#lint_axioms BoringMath.FormalPeriods.pairLBaseHom
#lint_axioms BoringMath.FormalPeriods.IsMonoFreeModHom
#lint_axioms BoringMath.FormalPeriods.IsEpiFreeModHom
#lint_axioms BoringMath.FormalPeriods.FiberFunctor
#lint_axioms BoringMath.FormalPeriods.PeriodQuadruple
#lint_axioms BoringMath.FormalPeriods.PeriodSym
#lint_axioms BoringMath.FormalPeriods.periodSym
#lint_axioms BoringMath.FormalPeriods.PeriodChain
#lint_axioms BoringMath.FormalPeriods.periodRel
#lint_axioms BoringMath.FormalPeriods.periodRelAddLeft
#lint_axioms BoringMath.FormalPeriods.periodRelAddRight
#lint_axioms BoringMath.FormalPeriods.periodRelSmul
#lint_axioms BoringMath.FormalPeriods.P
#lint_axioms BoringMath.FormalPeriods.periodAddInst
#lint_axioms BoringMath.FormalPeriods.periodSmulOp
#lint_axioms BoringMath.FormalPeriods.periodSMulInst
#lint_axioms BoringMath.FormalPeriods.periodZeroInst
#lint_axioms BoringMath.FormalPeriods.periodAddMk
#lint_axioms BoringMath.FormalPeriods.periodSmulMk
#lint_axioms BoringMath.FormalPeriods.periodZeroMk
#lint_axioms BoringMath.FormalPeriods.isSymSumAt
#lint_axioms BoringMath.FormalPeriods.PM
#lint_axioms BoringMath.FormalPeriods.evalSym
#lint_axioms BoringMath.FormalPeriods.evalSymEq
#lint_axioms BoringMath.FormalPeriods.evalSymAddLeft
#lint_axioms BoringMath.FormalPeriods.evalSymSmulLeft
#lint_axioms BoringMath.FormalPeriods.evalSymAddRight
#lint_axioms BoringMath.FormalPeriods.evalSymSmulRight
#lint_axioms BoringMath.FormalPeriods.evalSymZeroLeft
#lint_axioms BoringMath.FormalPeriods.evalSymZeroRight
#lint_axioms BoringMath.FormalPeriods.evalSymMorph
#lint_axioms BoringMath.FormalPeriods.evalRaw
#lint_axioms BoringMath.FormalPeriods.evalRawNil
#lint_axioms BoringMath.FormalPeriods.evalRawSym
#lint_axioms BoringMath.FormalPeriods.evalRawAdd
#lint_axioms BoringMath.FormalPeriods.evalRawSmul
#lint_axioms BoringMath.FormalPeriods.eval_well_defined
#lint_axioms BoringMath.FormalPeriods.eval
#lint_axioms BoringMath.FormalPeriods.evalMk
#lint_axioms BoringMath.FormalPeriods.evalSymMk


end BoringMath.FormalPeriods
