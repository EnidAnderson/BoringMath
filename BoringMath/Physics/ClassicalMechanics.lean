/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringMath.Physics.Specializations
import BoringMath.Physics.Liouville

/-!
# Classical mechanics as an MHI specialization — the harmonic oscillator — ticket #358

The first specialization instance with a proved law: the harmonic oscillator,
whose bulk is the two-point toy MHI, whose phase space is the 2D symplectic space
carrying `Matrix.J`, and whose Liouville law `rot_mem_symplecticGroup` (Liouville.lean)
is the proved instance of "the flow preserves the symplectic form".

## References
* [Goldstein] ch. 8–9; [Arnold] ch. 3; pin `Matrix.symplecticGroup`.
-/

namespace BoringMath

-- Reference: [Goldstein], ch. 8 (phase space, Hamiltonian); ticket #358.
/-- The **harmonic oscillator** as a `ClassicalMechanics` specialization over the
two-point toy MHI: the phase-space point is the unit, the Hamiltonian is constant. -/
def harmonicOscillator : ClassicalMechanics.{0, 0, 0, 0, 0} where
  toMotivicHolographicInfo := toyMHI
  phaseSpace := CategoryTheory.Discrete.mk 0
  hamiltonian := fun _ => (1 : ℕ)

-- Reference: [Goldstein] ch. 9 (Liouville's theorem); `rot_mem_symplecticGroup`
-- (Liouville.lean, proved).
/-- **Liouville law for the harmonic oscillator instance**: the flow `rot t`
preserves the canonical symplectic form `J` on the 2D phase space — the proved
non-vacuity law of the `ClassicalMechanics` specialization. -/
theorem harmonicOscillator_liouville (t : ℝ) :
    rot t ∈ Matrix.symplecticGroup (Fin 1) ℝ :=
  rot_mem_symplecticGroup t

end BoringMath
