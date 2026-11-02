/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringMath.Physics.MotivicHolographicInfo

/-!
# Specialization slots of the Physics framework — ticket #357

Per `docs/PHYSICS-ROADMAP.md` (#356–#370), each area of physics is a
**specialization** of `MotivicHolographicInfo`: a structure extending MHI with
area-specific fields. Instances (with calibrations) land in their own modules
`Physics/<Area>.lean`. These slots are definitions only — no `axiom`, no
unlabeled `sorry`.

## References
* [Atiyah 1988] (FQFT axioms); [Schreiber] (cohesive higher framework);
  [Wigner 1959] (symmetries); lab PHYS.0 / MI.0.1.
-/

namespace BoringMath

open CategoryTheory

universe u v u₁ v₁ w

-- Reference: [Goldstein] *Classical Mechanics*, ch. 8–9 (symplectic structure,
-- Hamiltonian); ticket #358.
/-- **Classical mechanics** as an MHI specialization: the bulk carries a
symplectic phase space and a Hamiltonian valued in the information monoid. -/
structure ClassicalMechanics extends MotivicHolographicInfo.{u, v, u₁, v₁, w} where
  /-- The symplectic phase space, as a bulk object. -/
  phaseSpace : bulk
  /-- The Hamiltonian: energy as information content of a bulk state. -/
  hamiltonian : bulk → info

-- Reference: [Wigner 1959]; [von Neumann], *Mathematical Foundations of QM*
-- (1932); ticket #359.
/-- **Quantum mechanics** as an MHI specialization: a Hilbert object in the
boundary, observables as its endomorphisms, measurement via the referee
ruling (PHYS.0 P4). -/
structure QuantumMechanics extends MotivicHolographicInfo.{u, v, u₁, v₁, w} where
  /-- The Hilbert object in the boundary category. -/
  hilbert : boundary
  /-- The observable endomorphisms of the Hilbert object. -/
  observables : (hilbert ⟶ hilbert) → Prop

-- Reference: [Atiyah 1988], Publ. Math. IHÉS 49 (FQFT axioms); ticket #360.
/-- **Functorial QFT** as an MHI specialization: the bulk is the cobordism
category and the hologram assigns to each bulk process its boundary QFT. -/
structure FunctorialQFT extends MotivicHolographicInfo.{u, v, u₁, v₁, w} where
  /-- The boundary value type assigned to the bulk unit (the vacuum). -/
  vacuum : boundary

-- Reference: [Maldacena 1997]; [Witten 1998]; ticket #361.
/-- **Gravity/holography** as an MHI specialization: bulk and boundary are
adjoint (the AdS/CFT dictionary), so the hologram has a right adjoint. -/
structure HolographicGravity extends MotivicHolographicInfo.{u, v, u₁, v₁, w} where
  /-- The boundary-to-bulk (reconstruction) functor, right adjoint to the
  hologram (adjunction laws land with the instance). -/
  reconstruct : boundary ⥤ bulk

-- Reference: [Landauer 1961]; ticket #362.
/-- **Statistical mechanics / thermodynamics** as an MHI specialization: the
information monoid is the thermodynamic resource ordering. -/
structure StatisticalMechanics extends MotivicHolographicInfo.{u, v, u₁, v₁, w} where
  /-- The equilibrium state of the bulk unit, as information. -/
  equilibriumInfo : info

end BoringMath
