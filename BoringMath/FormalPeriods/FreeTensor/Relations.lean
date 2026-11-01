/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Data.Quot
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Field.Basic
import BoringMath.FormalPeriods.FreeMod
import BoringMath.FormalPeriods.FreeTensor.Basic
/-!
# The constructive tensor product: relations (i)-(iv) and the bilinear map (part 2)

Piece 2 of `BoringMath.FormalPeriods.FreeTensor`: the witness chains for
Hörmann's relations (i)-(iv), the corresponding equalities in the quotient,
and the canonical bilinear map `tensorBil` with its four linearity lemmas.
-/

universe u v

namespace BoringMath

variable {K : Type u} [Field K] {m n : ℕ}

/-! ## The relations (i)–(iv) as witness chains and as equalities -/

-- Reference: Hörmann, arXiv:2106.03803, Key Lemma 3.2, relation (ii); the
-- `nilLeft` steps strip the empty sum.
/-- Witness chain for relation (ii) at the symbol level. -/
def tensorChainAdd (σ₁ σ₂ : FreeMod K m) (ω : FreeMod K n) :
    TensorChain K m n (TensorSym.add (tensorSym σ₁ ω) (tensorSym σ₂ ω))
      (tensorSym (σ₁ + σ₂) ω) :=
  TensorChain.trans
    (TensorChain.symm (TensorChain.nilLeft (TensorSym.add (tensorSym σ₁ ω) (tensorSym σ₂ ω))))
    (TensorChain.trans (TensorChain.addSymLeft TensorSym.nil σ₁ σ₂ ω)
      (TensorChain.nilLeft (tensorSym (σ₁ + σ₂) ω)))

-- Reference: Hörmann, arXiv:2106.03803, Key Lemma 3.2, relation (iii).
/-- Witness chain for relation (iii) at the symbol level. -/
def tensorChainAddRight (σ : FreeMod K m) (ω₁ ω₂ : FreeMod K n) :
    TensorChain K m n (TensorSym.add (tensorSym σ ω₁) (tensorSym σ ω₂))
      (tensorSym σ (ω₁ + ω₂)) :=
  TensorChain.trans
    (TensorChain.symm (TensorChain.nilLeft (TensorSym.add (tensorSym σ ω₁) (tensorSym σ ω₂))))
    (TensorChain.trans (TensorChain.addSymRight TensorSym.nil σ ω₁ ω₂)
      (TensorChain.nilLeft (tensorSym σ (ω₁ + ω₂))))

-- Reference: Hörmann, arXiv:2106.03803, Key Lemma 3.2, relation (iv).
/-- Witness chain for relation (iv) at the symbol level. -/
def tensorChainSmulSym (σ : FreeMod K m) (ω : FreeMod K n) (c : K) :
    TensorChain K m n (tensorSym σ (c • ω)) (tensorSym (c • σ) ω) :=
  TensorChain.trans (TensorChain.symm (TensorChain.nilLeft (tensorSym σ (c • ω))))
    (TensorChain.trans (TensorChain.smulSym TensorSym.nil σ ω c)
      (TensorChain.nilLeft (tensorSym (c • σ) ω)))

-- Reference: Hörmann, arXiv:2106.03803, Key Lemma 3.2, relation (iv) read as
-- the definition of the scalar action on the quotient (free-module form
-- `c(σ⊗ω) ∼ (cσ)⊗ω`).
/-- Witness chain for the scalar relation `c(σ⊗ω) ∼ (cσ)⊗ω` at the symbol
level. -/
def tensorChainSmulSymLeft (σ : FreeMod K m) (ω : FreeMod K n) (c : K) :
    TensorChain K m n (TensorSym.smul c (tensorSym σ ω)) (tensorSym (c • σ) ω) :=
  TensorChain.trans
    (TensorChain.symm (TensorChain.nilLeft (TensorSym.smul c (tensorSym σ ω))))
    (TensorChain.trans (TensorChain.smulSymLeft TensorSym.nil σ ω c)
      (TensorChain.nilLeft (tensorSym (c • σ) ω)))

-- Reference: Hörmann, arXiv:2106.03803, Key Lemma 3.2, relation (i) (right
-- half, verbatim: x + σ⊗0 ∼ x).
/-- Peel of relation (i): adding `σ ⊗ 0` to any tensor does nothing. -/
theorem tensorZeroRight (x : FreeTensor K m n) (σ : FreeMod K m) :
    x + tensorMk σ 0 = x :=
  Quot.inductionOn (motive := fun q => q + tensorMk σ 0 = q) x (fun x' =>
    Eq.trans (tensorAddMk x' (tensorSym σ 0))
      (Quot.sound (Nonempty.intro (TensorChain.zeroSymRight x' σ))))

-- Reference: Hörmann, arXiv:2106.03803, Key Lemma 3.2, relation (i) (left
-- half, verbatim: x + 0⊗ω ∼ x).
/-- Peel of relation (i): adding `0 ⊗ ω` to any tensor does nothing. -/
theorem tensorZeroLeft (x : FreeTensor K m n) (ω : FreeMod K n) :
    x + tensorMk 0 ω = x :=
  Quot.inductionOn (motive := fun q => q + tensorMk 0 ω = q) x (fun x' =>
    Eq.trans (tensorAddMk x' (tensorSym 0 ω))
      (Quot.sound (Nonempty.intro (TensorChain.zeroSymLeft x' ω))))

-- Reference: Hörmann, arXiv:2106.03803, Key Lemma 3.2, relation (ii) (verbatim:
-- x + σ₁⊗ω + σ₂⊗ω ∼ x + (σ₁+σ₂)⊗ω, at x = 0).
/-- Peel of relation (ii): `σ₁⊗ω + σ₂⊗ω = (σ₁+σ₂)⊗ω`. -/
theorem tensorAdd (σ₁ σ₂ : FreeMod K m) (ω : FreeMod K n) :
    tensorMk σ₁ ω + tensorMk σ₂ ω = tensorMk (σ₁ + σ₂) ω :=
  Eq.trans (tensorAddMk (tensorSym σ₁ ω) (tensorSym σ₂ ω))
    (Quot.sound (Nonempty.intro (tensorChainAdd σ₁ σ₂ ω)))

-- Reference: Hörmann, arXiv:2106.03803, Key Lemma 3.2, relation (iii)
-- (verbatim: x + σ⊗ω₁ + σ⊗ω₂ ∼ x + σ⊗(ω₁+ω₂), at x = 0).
/-- Peel of relation (iii): `σ⊗ω₁ + σ⊗ω₂ = σ⊗(ω₁+ω₂)`. -/
theorem tensorAddRight (σ : FreeMod K m) (ω₁ ω₂ : FreeMod K n) :
    tensorMk σ ω₁ + tensorMk σ ω₂ = tensorMk σ (ω₁ + ω₂) :=
  Eq.trans (tensorAddMk (tensorSym σ ω₁) (tensorSym σ ω₂))
    (Quot.sound (Nonempty.intro (tensorChainAddRight σ ω₁ ω₂)))

-- Reference: Hörmann, arXiv:2106.03803, Key Lemma 3.2, relation (iv) (verbatim:
-- x + σ⊗(λω) ∼ x + (λσ)⊗ω, at x = 0).
/-- Peel of relation (iv): `σ⊗(cω) = (cσ)⊗ω`. -/
theorem tensorSmul (c : K) (σ : FreeMod K m) (ω : FreeMod K n) :
    tensorMk σ (c • ω) = tensorMk (c • σ) ω :=
  Quot.sound (Nonempty.intro (tensorChainSmulSym σ ω c))

-- Reference: Hörmann, arXiv:2106.03803, Key Lemma 3.2, relation (iv) in the
-- free-module form: the scalar action on the quotient satisfies
-- `c(σ⊗ω) = (cσ)⊗ω`.
/-- Peel of the scalar relation: `c • (σ⊗ω) = (cσ)⊗ω`. -/
theorem tensorSmulLeft (c : K) (σ : FreeMod K m) (ω : FreeMod K n) :
    c • tensorMk σ ω = tensorMk (c • σ) ω :=
  Eq.trans (tensorSmulMk c (tensorSym σ ω))
    (Quot.sound (Nonempty.intro (tensorChainSmulSymLeft σ ω c)))

-- Reference: Hörmann, arXiv:2106.03803, Key Lemma 3.2, relations (iv) and the
-- scalar relation combined.
/-- Peel: `c • (σ⊗ω) = σ⊗(cω)`. -/
theorem tensorSmulRight (c : K) (σ : FreeMod K m) (ω : FreeMod K n) :
    c • tensorMk σ ω = tensorMk σ (c • ω) :=
  Eq.trans (tensorSmulLeft c σ ω) (tensorSmul c σ ω).symm

/-! ## The canonical bilinear map -/

-- Reference: Hörmann, arXiv:2106.03803, Key Lemma 3.2 (the map (σ,ω) ↦ σ⊗ω);
-- Dummit–Foote, §10.4.
/-- The canonical bilinear map `FreeMod K m → FreeMod K n → FreeTensor K m n`,
`(σ, ω) ↦ σ⊗ω`. -/
def tensorBil : FreeMod K m → FreeMod K n → FreeTensor K m n := tensorMk

-- Reference: Hörmann, arXiv:2106.03803, Key Lemma 3.2, relation (ii).
/-- The canonical map is additive in the first variable. -/
theorem tensorBilAddLeft (σ₁ σ₂ : FreeMod K m) (ω : FreeMod K n) :
    tensorBil (σ₁ + σ₂) ω = tensorBil σ₁ ω + tensorBil σ₂ ω :=
  (tensorAdd σ₁ σ₂ ω).symm

-- Reference: Hörmann, arXiv:2106.03803, Key Lemma 3.2, relation (iii).
/-- The canonical map is additive in the second variable. -/
theorem tensorBilAddRight (σ : FreeMod K m) (ω₁ ω₂ : FreeMod K n) :
    tensorBil σ (ω₁ + ω₂) = tensorBil σ ω₁ + tensorBil σ ω₂ :=
  (tensorAddRight σ ω₁ ω₂).symm

-- Reference: Hörmann, arXiv:2106.03803, Key Lemma 3.2, relation (iv) +
-- scalar relation.
/-- The canonical map is linear in the first variable. -/
theorem tensorBilSmulLeft (c : K) (σ : FreeMod K m) (ω : FreeMod K n) :
    tensorBil (c • σ) ω = c • tensorBil σ ω :=
  (tensorSmulLeft c σ ω).symm

-- Reference: Hörmann, arXiv:2106.03803, Key Lemma 3.2, relation (iv).
/-- The canonical map is linear in the second variable. -/
theorem tensorBilSmulRight (c : K) (σ : FreeMod K m) (ω : FreeMod K n) :
    tensorBil σ (c • ω) = c • tensorBil σ ω :=
  Eq.trans (tensorSmul c σ ω) (tensorSmulLeft c σ ω).symm

end BoringMath
