/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.LinearAlgebra.SymplecticGroup
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Liouville's theorem for the harmonic oscillator — ticket #358 (first law)

The first non-vacuity law of the Physics folder (roadmap acceptance criteria):
the harmonic oscillator flow `t ↦ rot t` on the 2-dimensional phase space
`(Fin 1 ⊕ Fin 1) ℝ` with the canonical symplectic form `J` preserves `J` —
i.e. `rot t ∈ symplecticGroup (Fin 1) ℝ` — proved from `Real.cos_sq_add_sin_sq`
via the block criterion `SymplecticGroup.fromBlocks_mem_iff`. This is Liouville
(phase-space volume/area preservation) on the toy; the general symplectic-flow
theorem is the peeling target.

## References
* [Goldstein] H. Goldstein, *Classical Mechanics*, ch. 8–9 (Liouville).
* [Arnold] V. I. Arnold, *Mathematical Methods of Classical Mechanics*, ch. 3.
* mathlib pin v4.35.0-rc3: `Matrix.symplecticGroup`, `Matrix.J`,
  `SymplecticGroup.fromBlocks_mem_iff`, `Real.cos_sq_add_sin_sq`.
-/

namespace BoringMath

open Matrix

-- Reference: [Goldstein], ch. 8 (the harmonic oscillator flow is rotation);
-- mathlib pin `Matrix.fromBlocks`.
-- `Real.cos` is noncomputable (defined through `Complex.exp`), which forces
-- `noncomputable` on `rot`.
/-- The harmonic-oscillator flow at time `t`: rotation by `t` on the 2D phase
space, in block form over `Fin 1 ⊕ Fin 1`. -/
noncomputable def rot (t : ℝ) : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ :=
  fromBlocks (Real.cos t • (1 : Matrix (Fin 1) (Fin 1) ℝ))
    (-Real.sin t • (1 : Matrix (Fin 1) (Fin 1) ℝ))
    (Real.sin t • (1 : Matrix (Fin 1) (Fin 1) ℝ))
    (Real.cos t • (1 : Matrix (Fin 1) (Fin 1) ℝ))

-- Reference: [Goldstein], ch. 9 (Liouville); block criterion
-- `SymplecticGroup.fromBlocks_mem_iff` reduced to `Real.cos_sq_add_sin_sq`.
/-- **Liouville for the harmonic oscillator**: the flow preserves the canonical
symplectic form: `rot t ∈ symplecticGroup (Fin 1) ℝ`, i.e.
`(rot t) * J * (rot t)ᵀ = J`. -/
theorem rot_mem_symplecticGroup (t : ℝ) : rot t ∈ symplecticGroup (Fin 1) ℝ := by
  -- A scalar multiple of the 1x1 identity matrix is symmetric.
  have hst : ∀ a : ℝ, (a • (1 : Matrix (Fin 1) (Fin 1) ℝ))ᵀ
      = a • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    intro a
    calc (a • (1 : Matrix (Fin 1) (Fin 1) ℝ))ᵀ
        = a • (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ := Matrix.transpose_smul a _
      _ = a • (1 : Matrix (Fin 1) (Fin 1) ℝ) :=
          congrArg (fun M => a • M) Matrix.transpose_one
  -- Products of scalar blocks: (a•1) * (b•1) = (a*b)•1.
  have hprod : ∀ a b : ℝ,
      (a • (1 : Matrix (Fin 1) (Fin 1) ℝ)) * (b • (1 : Matrix (Fin 1) (Fin 1) ℝ))
        = (a * b) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    intro a b
    calc (a • (1 : Matrix (Fin 1) (Fin 1) ℝ)) * (b • (1 : Matrix (Fin 1) (Fin 1) ℝ))
        = a • ((1 : Matrix (Fin 1) (Fin 1) ℝ)
            * (b • (1 : Matrix (Fin 1) (Fin 1) ℝ))) := Matrix.smul_mul a _ _
      _ = a • (b • ((1 : Matrix (Fin 1) (Fin 1) ℝ)
            * (1 : Matrix (Fin 1) (Fin 1) ℝ))) :=
          congrArg (fun M => a • M) (Matrix.mul_smul _ b _)
      _ = a • (b • (1 : Matrix (Fin 1) (Fin 1) ℝ)) :=
          congrArg (fun M => a • (b • M)) (Matrix.mul_one _)
      _ = (a * b) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := smul_smul a b _
  change (fromBlocks (Real.cos t • (1 : Matrix (Fin 1) (Fin 1) ℝ))
      (-Real.sin t • (1 : Matrix (Fin 1) (Fin 1) ℝ))
      (Real.sin t • (1 : Matrix (Fin 1) (Fin 1) ℝ))
      (Real.cos t • (1 : Matrix (Fin 1) (Fin 1) ℝ))) ∈ symplecticGroup (Fin 1) ℝ
  refine SymplecticGroup.fromBlocks_mem_iff.mpr ⟨?_, ?_, ?_⟩
  · -- Aᵀ * C = Cᵀ * A: both sides are scalar blocks, equal by commutativity.
    calc (Real.cos t • (1 : Matrix (Fin 1) (Fin 1) ℝ))ᵀ
        * (Real.sin t • (1 : Matrix (Fin 1) (Fin 1) ℝ))
      = (Real.cos t • (1 : Matrix (Fin 1) (Fin 1) ℝ))
        * (Real.sin t • (1 : Matrix (Fin 1) (Fin 1) ℝ)) :=
        congrArg (fun X => X * (Real.sin t • (1 : Matrix (Fin 1) (Fin 1) ℝ)))
          (hst (Real.cos t))
      _ = (Real.cos t * Real.sin t) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := hprod _ _
      _ = (Real.sin t * Real.cos t) • (1 : Matrix (Fin 1) (Fin 1) ℝ) :=
        congrArg (fun X => X • (1 : Matrix (Fin 1) (Fin 1) ℝ))
          (mul_comm (Real.cos t) (Real.sin t))
      _ = (Real.sin t • (1 : Matrix (Fin 1) (Fin 1) ℝ))
        * (Real.cos t • (1 : Matrix (Fin 1) (Fin 1) ℝ)) := (hprod _ _).symm
      _ = (Real.sin t • (1 : Matrix (Fin 1) (Fin 1) ℝ))ᵀ
        * (Real.cos t • (1 : Matrix (Fin 1) (Fin 1) ℝ)) :=
        (congrArg (fun X => X * (Real.cos t • (1 : Matrix (Fin 1) (Fin 1) ℝ)))
          (hst (Real.sin t))).symm
  · -- Bᵀ * D = Dᵀ * B: both sides are scalar blocks, equal by commutativity.
    calc (-Real.sin t • (1 : Matrix (Fin 1) (Fin 1) ℝ))ᵀ
        * (Real.cos t • (1 : Matrix (Fin 1) (Fin 1) ℝ))
      = (-Real.sin t • (1 : Matrix (Fin 1) (Fin 1) ℝ))
        * (Real.cos t • (1 : Matrix (Fin 1) (Fin 1) ℝ)) :=
        congrArg (fun X => X * (Real.cos t • (1 : Matrix (Fin 1) (Fin 1) ℝ)))
          (hst (-Real.sin t))
      _ = ((-Real.sin t) * Real.cos t) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := hprod _ _
      _ = (Real.cos t * (-Real.sin t)) • (1 : Matrix (Fin 1) (Fin 1) ℝ) :=
        congrArg (fun X => X • (1 : Matrix (Fin 1) (Fin 1) ℝ)) (mul_comm _ _)
      _ = (Real.cos t • (1 : Matrix (Fin 1) (Fin 1) ℝ))
        * (-Real.sin t • (1 : Matrix (Fin 1) (Fin 1) ℝ)) := (hprod _ _).symm
      _ = (Real.cos t • (1 : Matrix (Fin 1) (Fin 1) ℝ))ᵀ
        * (-Real.sin t • (1 : Matrix (Fin 1) (Fin 1) ℝ)) :=
        (congrArg (fun X => X * (-Real.sin t • (1 : Matrix (Fin 1) (Fin 1) ℝ)))
          (hst (Real.cos t))).symm
  · -- Aᵀ * D - Cᵀ * B = 1: (c*c)•1 + (s*s)•1 = (c²+s²)•1 = 1.
    have hAD : (Real.cos t • (1 : Matrix (Fin 1) (Fin 1) ℝ))ᵀ
        * (Real.cos t • (1 : Matrix (Fin 1) (Fin 1) ℝ))
      = (Real.cos t * Real.cos t) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
      calc (Real.cos t • (1 : Matrix (Fin 1) (Fin 1) ℝ))ᵀ
          * (Real.cos t • (1 : Matrix (Fin 1) (Fin 1) ℝ))
        = (Real.cos t • (1 : Matrix (Fin 1) (Fin 1) ℝ))
          * (Real.cos t • (1 : Matrix (Fin 1) (Fin 1) ℝ)) :=
          congrArg (fun X => X * (Real.cos t • (1 : Matrix (Fin 1) (Fin 1) ℝ)))
            (hst (Real.cos t))
        _ = (Real.cos t * Real.cos t) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := hprod _ _
    have hCB : (Real.sin t • (1 : Matrix (Fin 1) (Fin 1) ℝ))ᵀ
        * (-Real.sin t • (1 : Matrix (Fin 1) (Fin 1) ℝ))
      = -((Real.sin t * Real.sin t) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) := by
      calc (Real.sin t • (1 : Matrix (Fin 1) (Fin 1) ℝ))ᵀ
          * (-Real.sin t • (1 : Matrix (Fin 1) (Fin 1) ℝ))
        = (Real.sin t • (1 : Matrix (Fin 1) (Fin 1) ℝ))
          * (-Real.sin t • (1 : Matrix (Fin 1) (Fin 1) ℝ)) :=
          congrArg (fun X => X * (-Real.sin t • (1 : Matrix (Fin 1) (Fin 1) ℝ)))
            (hst (Real.sin t))
        _ = (Real.sin t * (-Real.sin t)) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := hprod _ _
        _ = (-(Real.sin t * Real.sin t)) • (1 : Matrix (Fin 1) (Fin 1) ℝ) :=
          congrArg (fun X => X • (1 : Matrix (Fin 1) (Fin 1) ℝ)) (mul_neg _ _)
        _ = -((Real.sin t * Real.sin t) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) :=
          neg_smul _ _
    calc (Real.cos t • (1 : Matrix (Fin 1) (Fin 1) ℝ))ᵀ
        * (Real.cos t • (1 : Matrix (Fin 1) (Fin 1) ℝ))
        - (Real.sin t • (1 : Matrix (Fin 1) (Fin 1) ℝ))ᵀ
        * (-Real.sin t • (1 : Matrix (Fin 1) (Fin 1) ℝ))
      = (Real.cos t * Real.cos t) • (1 : Matrix (Fin 1) (Fin 1) ℝ)
        - (Real.sin t • (1 : Matrix (Fin 1) (Fin 1) ℝ))ᵀ
        * (-Real.sin t • (1 : Matrix (Fin 1) (Fin 1) ℝ)) :=
        congrArg (fun X => X - (Real.sin t • (1 : Matrix (Fin 1) (Fin 1) ℝ))ᵀ
          * (-Real.sin t • (1 : Matrix (Fin 1) (Fin 1) ℝ))) hAD
      _ = (Real.cos t * Real.cos t) • (1 : Matrix (Fin 1) (Fin 1) ℝ)
        - (-((Real.sin t * Real.sin t) • (1 : Matrix (Fin 1) (Fin 1) ℝ))) :=
        congrArg (fun X => (Real.cos t * Real.cos t) • (1 : Matrix (Fin 1) (Fin 1) ℝ)
          - X) hCB
      _ = (Real.cos t * Real.cos t) • (1 : Matrix (Fin 1) (Fin 1) ℝ)
        + (-(-((Real.sin t * Real.sin t) • (1 : Matrix (Fin 1) (Fin 1) ℝ)))) :=
        sub_eq_add_neg _ _
      _ = (Real.cos t * Real.cos t) • (1 : Matrix (Fin 1) (Fin 1) ℝ)
        + ((Real.sin t * Real.sin t) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) :=
        congrArg (fun X => (Real.cos t * Real.cos t) • (1 : Matrix (Fin 1) (Fin 1) ℝ)
          + X) (neg_neg _)
      _ = (Real.cos t * Real.cos t + Real.sin t * Real.sin t)
        • (1 : Matrix (Fin 1) (Fin 1) ℝ) := (add_smul _ _ _).symm
      _ = (Real.cos t ^ 2 + Real.sin t ^ 2) • (1 : Matrix (Fin 1) (Fin 1) ℝ) :=
        congrArg (fun X => X • (1 : Matrix (Fin 1) (Fin 1) ℝ))
          (congrArg₂ (fun x y => x + y) (pow_two _).symm (pow_two _).symm)
      _ = (1 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ) :=
        congrArg (fun X => X • (1 : Matrix (Fin 1) (Fin 1) ℝ))
          (Real.cos_sq_add_sin_sq t)
      _ = (1 : Matrix (Fin 1) (Fin 1) ℝ) := one_smul _ _

end BoringMath
