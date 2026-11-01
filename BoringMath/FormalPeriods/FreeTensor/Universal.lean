/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Data.Quot
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Field.Rat
import BoringMath.FormalPeriods.FreeMod
import BoringMath.FormalPeriods.FreeTensor.Basic
import BoringMath.FormalPeriods.FreeTensor.Relations
/-!
# The constructive tensor product: the universal property (part 3)

Piece 3 of `BoringMath.FormalPeriods.FreeTensor`: bilinear maps into a
module (`TensorBilMap`), the lift to formal sums (`tensorSymLift`) and to
the quotient (`tensorLift`), the uniqueness of the factorization
(`tensorLift_unique`), and the `K = ℚ` smoke tests.
-/

universe u v

namespace BoringMath

variable {K : Type u} [Field K] {m n : ℕ}

/-! ## Bilinear maps into a module, and the universal property -/

variable {W : Type v} [AddCommGroup W] [Module K W]

-- Reference: Dummit–Foote, §10.4 (bilinear maps `M × N → W`); Axler, *Linear
-- Algebra Done Right*, 4th ed., Ch. 1 (linearity in each variable).
/-- A bilinear map `FreeMod K m → FreeMod K n → W` into a `K`-module `W`, as
explicit data (function plus the four linearity proofs). -/
structure TensorBilMap (K : Type u) [Field K] (m n : ℕ) (W : Type v)
    [AddCommGroup W] [Module K W] where
  toFun : FreeMod K m → FreeMod K n → W
  map_add_left : ∀ (σ₁ σ₂ : FreeMod K m) (ω : FreeMod K n),
    toFun (σ₁ + σ₂) ω = toFun σ₁ ω + toFun σ₂ ω
  map_add_right : ∀ (σ : FreeMod K m) (ω₁ ω₂ : FreeMod K n),
    toFun σ (ω₁ + ω₂) = toFun σ ω₁ + toFun σ ω₂
  map_smul_left : ∀ (c : K) (σ : FreeMod K m) (ω : FreeMod K n),
    toFun (c • σ) ω = c • toFun σ ω
  map_smul_right : ∀ (c : K) (σ : FreeMod K m) (ω : FreeMod K n),
    toFun σ (c • ω) = c • toFun σ ω

-- Reference: Dummit–Foote, §10.4 (bilinearity kills zero); Axler, Ch. 1.
/-- A bilinear map vanishes in the first variable at `0`. -/
theorem TensorBilMap.map_zero_left (β : TensorBilMap K m n W) (ω : FreeMod K n) :
    β.toFun 0 ω = 0 :=
  Eq.trans (congrArg (fun σ => β.toFun σ ω) (zero_smul K (0 : FreeMod K m)).symm)
    (Eq.trans (β.map_smul_left (0 : K) 0 ω) (zero_smul K (β.toFun 0 ω)))

-- Reference: Dummit–Foote, §10.4 (bilinearity kills zero); Axler, Ch. 1.
/-- A bilinear map vanishes in the second variable at `0`. -/
theorem TensorBilMap.map_zero_right (β : TensorBilMap K m n W) (σ : FreeMod K m) :
    β.toFun σ 0 = 0 :=
  Eq.trans (congrArg (β.toFun σ) (zero_smul K (0 : FreeMod K n)).symm)
    (Eq.trans (β.map_smul_right (0 : K) σ 0) (zero_smul K (β.toFun σ 0)))

-- Reference: Dummit–Foote, §10.4 (the lift of a bilinear map to the free
-- module on symbols, by recursion on formal sums).
/-- The lift of a bilinear map `β` to the raw formal sums: the empty sum maps
to `0`, a symbol `σ⊗ω` maps to `β σ ω`, addition and scalar multiplication
map to the module operations of `W`. -/
def tensorSymLift (β : TensorBilMap K m n W) : TensorSym K m n → W
  | TensorSym.nil => 0
  | TensorSym.sym σ ω => β.toFun σ ω
  | TensorSym.add x y => tensorSymLift β x + tensorSymLift β y
  | TensorSym.smul c x => c • tensorSymLift β x

-- Reference: Lean 4 core (definitional unfolding of `tensorSymLift`); primitive
-- definitional lemmas.
/-- The lift of the empty formal sum is `0`. -/
theorem tensorSymLiftNil (β : TensorBilMap K m n W) :
    tensorSymLift β TensorSym.nil = 0 := Eq.refl _

-- Reference: Lean 4 core (definitional unfolding of `tensorSymLift`); primitive
-- definitional lemma.
/-- The lift of a symbol is the bilinear value. -/
theorem tensorSymLiftSym (β : TensorBilMap K m n W) (σ : FreeMod K m) (ω : FreeMod K n) :
    tensorSymLift β (TensorSym.sym σ ω) = β.toFun σ ω := Eq.refl _

-- Reference: Lean 4 core (definitional unfolding of `tensorSymLift`); primitive
-- definitional lemma.
/-- The lift of a formal sum is the sum of the lifts. -/
theorem tensorSymLiftAdd (β : TensorBilMap K m n W) (x y : TensorSym K m n) :
    tensorSymLift β (TensorSym.add x y) = tensorSymLift β x + tensorSymLift β y :=
  Eq.refl _

-- Reference: Lean 4 core (definitional unfolding of `tensorSymLift`); primitive
-- definitional lemma.
/-- The lift of a formal scalar multiple is the scalar multiple of the lift. -/
theorem tensorSymLiftSmul (β : TensorBilMap K m n W) (c : K) (x : TensorSym K m n) :
    tensorSymLift β (TensorSym.smul c x) = c • tensorSymLift β x := Eq.refl _

-- Reference: Dummit–Foote, §10.4 (the lift respects the relations); Hörmann,
-- arXiv:2106.03803, Key Lemma 3.2 (relations (i)–(iv)); mathlib class axioms
-- of `Module`/`DistribMulAction` on `W`.
/-- The lift of `β` to formal sums respects the quotient relation: each
constructor of `TensorChain` is sent to an equality in `W` (the module laws of
`W` for the free-module laws, bilinearity of `β` for relations (i)–(iv) and
the scalar relation). -/
theorem tensorSymLiftRel (β : TensorBilMap K m n W) (x y : TensorSym K m n)
    (h : tensorRel K m n x y) : tensorSymLift β x = tensorSymLift β y := by
  obtain ⟨ch⟩ := h
  induction ch
  case refl x => exact Eq.refl _
  case symm x y ch ih => exact Eq.symm ih
  case trans x y z ch₁ ch₂ ih₁ ih₂ => exact Eq.trans ih₁ ih₂
  case addLeft x y z ch ih =>
    calc tensorSymLift β (TensorSym.add z x) = tensorSymLift β z + tensorSymLift β x :=
            tensorSymLiftAdd β z x
      _ = tensorSymLift β z + tensorSymLift β y :=
            congrArg (fun w => tensorSymLift β z + w) ih
      _ = tensorSymLift β (TensorSym.add z y) := (tensorSymLiftAdd β z y).symm
  case addRight x y z ch ih =>
    calc tensorSymLift β (TensorSym.add x z) = tensorSymLift β x + tensorSymLift β z :=
            tensorSymLiftAdd β x z
      _ = tensorSymLift β y + tensorSymLift β z :=
            congrArg (fun w => w + tensorSymLift β z) ih
      _ = tensorSymLift β (TensorSym.add y z) := (tensorSymLiftAdd β y z).symm
  case smulC x y a ch ih =>
    calc tensorSymLift β (TensorSym.smul a x) = a • tensorSymLift β x := tensorSymLiftSmul β a x
      _ = a • tensorSymLift β y := congrArg (fun w => a • w) ih
      _ = tensorSymLift β (TensorSym.smul a y) := (tensorSymLiftSmul β a y).symm
  case nilLeft x =>
    calc tensorSymLift β (TensorSym.add TensorSym.nil x)
        = tensorSymLift β TensorSym.nil + tensorSymLift β x := tensorSymLiftAdd β _ x
      _ = 0 + tensorSymLift β x :=
            congrArg (fun w => w + tensorSymLift β x) (tensorSymLiftNil β)
      _ = tensorSymLift β x := zero_add _
  case nilRight x =>
    calc tensorSymLift β (TensorSym.add x TensorSym.nil)
        = tensorSymLift β x + tensorSymLift β TensorSym.nil := tensorSymLiftAdd β x _
      _ = tensorSymLift β x + 0 :=
            congrArg (fun w => tensorSymLift β x + w) (tensorSymLiftNil β)
      _ = tensorSymLift β x := add_zero _
  case addAssoc x y z =>
    calc tensorSymLift β (TensorSym.add (TensorSym.add x y) z)
        = tensorSymLift β (TensorSym.add x y) + tensorSymLift β z := tensorSymLiftAdd β _ z
      _ = (tensorSymLift β x + tensorSymLift β y) + tensorSymLift β z :=
            congrArg (fun w => w + tensorSymLift β z) (tensorSymLiftAdd β x y)
      _ = tensorSymLift β x + (tensorSymLift β y + tensorSymLift β z) := add_assoc _ _ _
      _ = tensorSymLift β x + tensorSymLift β (TensorSym.add y z) :=
            congrArg (fun w => tensorSymLift β x + w) (tensorSymLiftAdd β y z).symm
      _ = tensorSymLift β (TensorSym.add x (TensorSym.add y z)) :=
            (tensorSymLiftAdd β x _).symm
  case addComm x y =>
    calc tensorSymLift β (TensorSym.add x y) = tensorSymLift β x + tensorSymLift β y :=
            tensorSymLiftAdd β x y
      _ = tensorSymLift β y + tensorSymLift β x := add_comm _ _
      _ = tensorSymLift β (TensorSym.add y x) := (tensorSymLiftAdd β y x).symm
  case smulNil c =>
    calc tensorSymLift β (TensorSym.smul c TensorSym.nil) = c • tensorSymLift β TensorSym.nil :=
            tensorSymLiftSmul β c _
      _ = c • 0 := congrArg (fun w => c • w) (tensorSymLiftNil β)
      _ = 0 := smul_zero _
      _ = tensorSymLift β TensorSym.nil := (tensorSymLiftNil β).symm
  case smulAdd c x y =>
    calc tensorSymLift β (TensorSym.smul c (TensorSym.add x y))
        = c • tensorSymLift β (TensorSym.add x y) := tensorSymLiftSmul β c _
      _ = c • (tensorSymLift β x + tensorSymLift β y) :=
            congrArg (fun w => c • w) (tensorSymLiftAdd β x y)
      _ = c • tensorSymLift β x + c • tensorSymLift β y := smul_add _ _ _
      _ = tensorSymLift β (TensorSym.smul c x) + tensorSymLift β (TensorSym.smul c y) :=
            Eq.trans
              (congrArg (fun w => w + tensorSymLift β (TensorSym.smul c y))
                (tensorSymLiftSmul β c x).symm)
              (congrArg (fun w => tensorSymLift β (TensorSym.smul c x) + w)
                (tensorSymLiftSmul β c y).symm)
      _ = tensorSymLift β (TensorSym.add (TensorSym.smul c x) (TensorSym.smul c y)) :=
            (tensorSymLiftAdd β (TensorSym.smul c x) (TensorSym.smul c y)).symm
  case addSmul a b x =>
    calc tensorSymLift β (TensorSym.smul (a + b) x) = (a + b) • tensorSymLift β x :=
            tensorSymLiftSmul β _ x
      _ = a • tensorSymLift β x + b • tensorSymLift β x := add_smul _ _ _
      _ = tensorSymLift β (TensorSym.smul a x) + tensorSymLift β (TensorSym.smul b x) :=
            Eq.trans
              (congrArg (fun w => w + tensorSymLift β (TensorSym.smul b x))
                (tensorSymLiftSmul β a x).symm)
              (congrArg (fun w => tensorSymLift β (TensorSym.smul a x) + w)
                (tensorSymLiftSmul β b x).symm)
      _ = tensorSymLift β (TensorSym.add (TensorSym.smul a x) (TensorSym.smul b x)) :=
            (tensorSymLiftAdd β (TensorSym.smul a x) (TensorSym.smul b x)).symm
  case oneSmul x =>
    calc tensorSymLift β (TensorSym.smul 1 x) = 1 • tensorSymLift β x := tensorSymLiftSmul β _ x
      _ = tensorSymLift β x := one_smul K _
  case zeroSmul x =>
    calc tensorSymLift β (TensorSym.smul 0 x) = 0 • tensorSymLift β x := tensorSymLiftSmul β _ x
      _ = 0 := zero_smul K _
      _ = tensorSymLift β TensorSym.nil := (tensorSymLiftNil β).symm
  case smulSmul a b x =>
    calc tensorSymLift β (TensorSym.smul a (TensorSym.smul b x))
        = a • tensorSymLift β (TensorSym.smul b x) := tensorSymLiftSmul β a _
      _ = a • (b • tensorSymLift β x) :=
            congrArg (fun w => a • w) (tensorSymLiftSmul β b x)
      _ = (a * b) • tensorSymLift β x := (mul_smul a b _).symm
      _ = tensorSymLift β (TensorSym.smul (a * b) x) := (tensorSymLiftSmul β _ x).symm
  case zeroSymRight x σ =>
    calc tensorSymLift β (TensorSym.add x (TensorSym.sym σ 0))
        = tensorSymLift β x + tensorSymLift β (TensorSym.sym σ 0) := tensorSymLiftAdd β x _
      _ = tensorSymLift β x + β.toFun σ 0 :=
            congrArg (fun w => tensorSymLift β x + w) (tensorSymLiftSym β σ 0)
      _ = tensorSymLift β x + 0 := congrArg (fun w => tensorSymLift β x + w) (β.map_zero_right σ)
      _ = tensorSymLift β x := add_zero _
  case zeroSymLeft x ω =>
    calc tensorSymLift β (TensorSym.add x (TensorSym.sym 0 ω))
        = tensorSymLift β x + tensorSymLift β (TensorSym.sym 0 ω) := tensorSymLiftAdd β x _
      _ = tensorSymLift β x + β.toFun 0 ω :=
            congrArg (fun w => tensorSymLift β x + w) (tensorSymLiftSym β 0 ω)
      _ = tensorSymLift β x + 0 := congrArg (fun w => tensorSymLift β x + w) (β.map_zero_left ω)
      _ = tensorSymLift β x := add_zero _
  case addSymLeft x σ₁ σ₂ ω =>
    calc tensorSymLift β (TensorSym.add x
          (TensorSym.add (TensorSym.sym σ₁ ω) (TensorSym.sym σ₂ ω)))
        = tensorSymLift β x
            + tensorSymLift β (TensorSym.add (TensorSym.sym σ₁ ω) (TensorSym.sym σ₂ ω)) :=
            tensorSymLiftAdd β x _
      _ = tensorSymLift β x + (β.toFun σ₁ ω + β.toFun σ₂ ω) :=
            congrArg (fun w => tensorSymLift β x + w) (tensorSymLiftAdd β _ _)
      _ = tensorSymLift β x + β.toFun (σ₁ + σ₂) ω :=
            congrArg (fun w => tensorSymLift β x + w) (β.map_add_left σ₁ σ₂ ω).symm
      _ = tensorSymLift β x + tensorSymLift β (TensorSym.sym (σ₁ + σ₂) ω) :=
            congrArg (fun w => tensorSymLift β x + w) (tensorSymLiftSym β (σ₁ + σ₂) ω).symm
      _ = tensorSymLift β (TensorSym.add x (TensorSym.sym (σ₁ + σ₂) ω)) :=
            (tensorSymLiftAdd β x _).symm
  case addSymRight x σ ω₁ ω₂ =>
    calc tensorSymLift β (TensorSym.add x
          (TensorSym.add (TensorSym.sym σ ω₁) (TensorSym.sym σ ω₂)))
        = tensorSymLift β x
            + tensorSymLift β (TensorSym.add (TensorSym.sym σ ω₁) (TensorSym.sym σ ω₂)) :=
            tensorSymLiftAdd β x _
      _ = tensorSymLift β x + (β.toFun σ ω₁ + β.toFun σ ω₂) :=
            congrArg (fun w => tensorSymLift β x + w) (tensorSymLiftAdd β _ _)
      _ = tensorSymLift β x + β.toFun σ (ω₁ + ω₂) :=
            congrArg (fun w => tensorSymLift β x + w) (β.map_add_right σ ω₁ ω₂).symm
      _ = tensorSymLift β x + tensorSymLift β (TensorSym.sym σ (ω₁ + ω₂)) :=
            congrArg (fun w => tensorSymLift β x + w) (tensorSymLiftSym β σ (ω₁ + ω₂)).symm
      _ = tensorSymLift β (TensorSym.add x (TensorSym.sym σ (ω₁ + ω₂))) :=
            (tensorSymLiftAdd β x _).symm
  case smulSym x σ ω c =>
    calc tensorSymLift β (TensorSym.add x (TensorSym.sym σ (c • ω)))
        = tensorSymLift β x + tensorSymLift β (TensorSym.sym σ (c • ω)) := tensorSymLiftAdd β x _
      _ = tensorSymLift β x + β.toFun σ (c • ω) :=
            congrArg (fun w => tensorSymLift β x + w) (tensorSymLiftSym β σ (c • ω))
      _ = tensorSymLift β x + c • β.toFun σ ω :=
            congrArg (fun w => tensorSymLift β x + w) (β.map_smul_right c σ ω)
      _ = tensorSymLift β x + β.toFun (c • σ) ω :=
            congrArg (fun w => tensorSymLift β x + w) (β.map_smul_left c σ ω).symm
      _ = tensorSymLift β x + tensorSymLift β (TensorSym.sym (c • σ) ω) :=
            congrArg (fun w => tensorSymLift β x + w) (tensorSymLiftSym β (c • σ) ω).symm
      _ = tensorSymLift β (TensorSym.add x (TensorSym.sym (c • σ) ω)) :=
            (tensorSymLiftAdd β x _).symm
  case smulSymLeft x σ ω c =>
    calc tensorSymLift β (TensorSym.add x (TensorSym.smul c (TensorSym.sym σ ω)))
        = tensorSymLift β x + tensorSymLift β (TensorSym.smul c (TensorSym.sym σ ω)) :=
            tensorSymLiftAdd β x _
      _ = tensorSymLift β x + c • tensorSymLift β (TensorSym.sym σ ω) :=
            congrArg (fun w => tensorSymLift β x + w) (tensorSymLiftSmul β c _)
      _ = tensorSymLift β x + c • β.toFun σ ω :=
            congrArg (fun w => tensorSymLift β x + w)
              (congrArg (fun w => c • w) (tensorSymLiftSym β σ ω))
      _ = tensorSymLift β x + β.toFun (c • σ) ω :=
            congrArg (fun w => tensorSymLift β x + w) (β.map_smul_left c σ ω).symm
      _ = tensorSymLift β x + tensorSymLift β (TensorSym.sym (c • σ) ω) :=
            congrArg (fun w => tensorSymLift β x + w) (tensorSymLiftSym β (c • σ) ω).symm
      _ = tensorSymLift β (TensorSym.add x (TensorSym.sym (c • σ) ω)) :=
            (tensorSymLiftAdd β x (TensorSym.sym (c • σ) ω)).symm

-- Reference: Dummit–Foote, §10.4 (universal property: the lift descends to
-- the quotient); Lean 4 core, Init/Prelude.lean (`Quot.lift`).
/-- The lift of a bilinear map `β` to the tensor product. -/
def tensorLift (β : TensorBilMap K m n W) : FreeTensor K m n → W :=
  Quot.lift (tensorSymLift β) (tensorSymLiftRel β)

-- Reference: mathlib, Mathlib/Data/Quot.lean (`Quot.lift_mk`, proved by `rfl`);
-- primitive definitional lemma.
/-- The lift of the class of a formal sum is the lift of the formal sum. -/
theorem tensorLiftMk (β : TensorBilMap K m n W) (x : TensorSym K m n) :
    tensorLift β (Quot.mk (tensorRel K m n) x) = tensorSymLift β x := by
  unfold tensorLift
  exact Quot.lift_mk (tensorSymLift β) (tensorSymLiftRel β) x

-- Reference: Dummit–Foote, §10.4 (universal property, beta rule).
/-- Beta rule of the universal property: the lift of `β` sends `σ⊗ω` to
`β σ ω`. -/
theorem tensorLift_beta (β : TensorBilMap K m n W) (σ : FreeMod K m) (ω : FreeMod K n) :
    tensorLift β (tensorMk σ ω) = β.toFun σ ω :=
  Eq.trans (tensorLiftMk β (tensorSym σ ω)) (tensorSymLiftSym β σ ω)

-- Reference: Dummit–Foote, §10.4 (the lift is additive); mathlib,
-- Mathlib/Data/Quot.lean (`Quot.induction_on₂`).
/-- The lift of a bilinear map is additive. -/
theorem tensorLift_add (β : TensorBilMap K m n W) (x y : FreeTensor K m n) :
    tensorLift β (x + y) = tensorLift β x + tensorLift β y :=
  Quot.induction_on₂ x y (fun a b =>
    calc tensorLift β (Quot.mk (tensorRel K m n) a + Quot.mk (tensorRel K m n) b)
        = tensorLift β (Quot.mk (tensorRel K m n) (TensorSym.add a b)) :=
          congrArg (tensorLift β) (tensorAddMk a b)
      _ = tensorSymLift β (TensorSym.add a b) := tensorLiftMk β (TensorSym.add a b)
      _ = tensorSymLift β a + tensorSymLift β b := tensorSymLiftAdd β a b
      _ = tensorLift β (Quot.mk (tensorRel K m n) a) + tensorLift β (Quot.mk (tensorRel K m n) b) :=
          Eq.trans
            (congrArg (fun w => w + tensorSymLift β b) (tensorLiftMk β a).symm)
            (congrArg (fun w => tensorLift β (Quot.mk (tensorRel K m n) a) + w)
              (tensorLiftMk β b).symm))

-- Reference: Dummit–Foote, §10.4 (the lift is linear); Lean 4 core,
-- Init/Core.lean (`Quot.inductionOn`).
/-- The lift of a bilinear map is linear. -/
theorem tensorLift_smul (β : TensorBilMap K m n W) (c : K) (x : FreeTensor K m n) :
    tensorLift β (c • x) = c • tensorLift β x :=
  Quot.inductionOn (motive := fun q => tensorLift β (c • q) = c • tensorLift β q) x (fun a =>
    calc tensorLift β (c • Quot.mk (tensorRel K m n) a)
        = tensorLift β (Quot.mk (tensorRel K m n) (TensorSym.smul c a)) :=
          congrArg (tensorLift β) (tensorSmulMk c a)
      _ = tensorSymLift β (TensorSym.smul c a) := tensorLiftMk β _
      _ = c • tensorSymLift β a := tensorSymLiftSmul β c a
      _ = c • tensorLift β (Quot.mk (tensorRel K m n) a) :=
          congrArg (fun w => c • w) (tensorLiftMk β a).symm)

-- Reference: Hörmann, arXiv:2106.03803, Key Lemma 3.2, relation (i) (the empty
-- sum is zero); Dummit–Foote, §10.4.
/-- The lift of a bilinear map sends `0` to `0`. -/
theorem tensorLift_zero (β : TensorBilMap K m n W) : tensorLift β 0 = 0 :=
  calc tensorLift β (0 : FreeTensor K m n) = tensorSymLift β TensorSym.nil :=
        tensorLiftMk β TensorSym.nil
    _ = 0 := tensorSymLiftNil β

-- Reference: Hörmann, arXiv:2106.03803, Key Lemma 3.2, relation (i) (scalar
-- zero kills the zero tensor).
/-- Scalar zero kills the zero tensor: `(0:K) • 0 = 0`. -/
theorem tensorZeroSmulZero : (0 : K) • (0 : FreeTensor K m n) = (0 : FreeTensor K m n) :=
  Eq.trans (tensorSmulMk (0 : K) TensorSym.nil)
    (Eq.trans (Quot.sound (Nonempty.intro (TensorChain.zeroSmul TensorSym.nil)))
      tensorZeroMk.symm)

-- Reference: Dummit–Foote, §10.4 (universal property, uniqueness: bilinear
-- maps factor uniquely through the tensor product).
/-- Uniqueness of the factorization: any function `f` out of the tensor product
that is additive, linear, and agrees with `β` on the symbols `σ⊗ω` equals the
lift of `β`. -/
theorem tensorLift_unique (β : TensorBilMap K m n W) (f : FreeTensor K m n → W)
    (hadd : ∀ x y, f (x + y) = f x + f y)
    (hsmul : ∀ (c : K) (x : FreeTensor K m n), f (c • x) = c • f x)
    (hbeta : ∀ σ ω, f (tensorMk σ ω) = β.toFun σ ω) : f = tensorLift β :=
  funext fun X =>
    Quot.inductionOn (motive := fun q => f q = tensorLift β q) X (fun x => by
      induction x with
      | nil =>
          calc f (Quot.mk (tensorRel K m n) TensorSym.nil) = f (0 : FreeTensor K m n) :=
                congrArg f tensorZeroMk.symm
            _ = f ((0 : K) • (0 : FreeTensor K m n)) := congrArg f tensorZeroSmulZero.symm
            _ = (0 : K) • f (0 : FreeTensor K m n) := hsmul _ _
            _ = 0 := zero_smul K _
            _ = tensorSymLift β TensorSym.nil := (tensorSymLiftNil β).symm
            _ = tensorLift β (Quot.mk (tensorRel K m n) TensorSym.nil) :=
                  (tensorLiftMk β TensorSym.nil).symm
      | sym σ ω =>
          calc f (Quot.mk (tensorRel K m n) (TensorSym.sym σ ω)) = β.toFun σ ω := hbeta σ ω
            _ = tensorSymLift β (TensorSym.sym σ ω) := (tensorSymLiftSym β σ ω).symm
            _ = tensorLift β (Quot.mk (tensorRel K m n) (TensorSym.sym σ ω)) :=
                  (tensorLiftMk β (tensorSym σ ω)).symm
      | add x y ihx ihy =>
          calc f (Quot.mk (tensorRel K m n) (TensorSym.add x y))
              = f (Quot.mk (tensorRel K m n) x + Quot.mk (tensorRel K m n) y) :=
                  congrArg f (tensorAddMk x y).symm
            _ = f (Quot.mk (tensorRel K m n) x) + f (Quot.mk (tensorRel K m n) y) := hadd _ _
            _ = tensorLift β (Quot.mk (tensorRel K m n) x)
                + tensorLift β (Quot.mk (tensorRel K m n) y) :=
                  Eq.trans (congrArg (fun w => w + f (Quot.mk (tensorRel K m n) y)) ihx)
                    (congrArg (fun w => tensorLift β (Quot.mk (tensorRel K m n) x) + w) ihy)
            _ = tensorLift β (Quot.mk (tensorRel K m n) x + Quot.mk (tensorRel K m n) y) :=
                  (tensorLift_add β _ _).symm
            _ = tensorLift β (Quot.mk (tensorRel K m n) (TensorSym.add x y)) :=
                  congrArg (tensorLift β) (tensorAddMk x y)
      | smul c x ih =>
          calc f (Quot.mk (tensorRel K m n) (TensorSym.smul c x))
              = f (c • Quot.mk (tensorRel K m n) x) := congrArg f (tensorSmulMk c x).symm
            _ = c • f (Quot.mk (tensorRel K m n) x) := hsmul c _
            _ = c • tensorLift β (Quot.mk (tensorRel K m n) x) := congrArg (fun w => c • w) ih
            _ = tensorLift β (c • Quot.mk (tensorRel K m n) x) := (tensorLift_smul β c _).symm
            _ = tensorLift β (Quot.mk (tensorRel K m n) (TensorSym.smul c x)) :=
                  congrArg (tensorLift β) (tensorSmulMk c x))

/-! ## Smoke tests at `K = ℚ` -/

-- Reference: smoke test for the P.1.2 acceptance criterion (usable at K = ℚ).
/-- Smoke test: the tensor of two basis-carrying `ℚ`-modules is inhabited. -/
example : FreeTensor ℚ 2 3 := tensorMk (fun _ => (1 : ℚ)) (fun _ => (0 : ℚ))

-- Reference: smoke test — relation (ii) at `K = ℚ`.
/-- Smoke test: the peel (ii) at `K = ℚ`. -/
example (σ₁ σ₂ : FreeMod ℚ 2) (ω : FreeMod ℚ 3) :
    tensorMk σ₁ ω + tensorMk σ₂ ω = tensorMk (σ₁ + σ₂) ω :=
  tensorAdd σ₁ σ₂ ω

-- Reference: Dummit–Foote, §10.4 (the zero bilinear map).
/-- The zero bilinear map `FreeMod K m → FreeMod K n → W`, as a `TensorBilMap`.
Generic in `K`, `m`, `n`, `W` so that the declaration itself lints CLEAN (the
concrete `Rat.instField` instance is CHOICE-TAINTED at the pin, so only the
unlinted `ℚ` smoke examples below touch `ℚ`). -/
def zeroBilMap : TensorBilMap K m n W where
  toFun := fun _ _ => 0
  map_add_left := fun _ _ _ => (add_zero (0 : W)).symm
  map_add_right := fun _ _ _ => (add_zero (0 : W)).symm
  map_smul_left := fun _ _ _ => (smul_zero _).symm
  map_smul_right := fun _ _ _ => (smul_zero _).symm

-- Reference: smoke test — the universal property at `K = ℚ`, `W = ℚ`.
/-- Smoke test: the beta rule of the lift of the zero bilinear map at `ℚ`. -/
example (σ : FreeMod ℚ 2) (ω : FreeMod ℚ 3) :
    tensorLift (zeroBilMap (K := ℚ) (m := 2) (n := 3) (W := ℚ)) (tensorMk σ ω) = (0 : ℚ) :=
  Eq.trans (tensorLift_beta (zeroBilMap (K := ℚ) (m := 2) (n := 3) (W := ℚ)) σ ω) (Eq.refl _)

end BoringMath
