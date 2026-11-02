/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import BoringMath.AlgebraicGeometry.AlgebraicCycle.RationalEquivalence

/-!
# Projective space over a base (V.3, part 1)

`P^{n-1}_ℤ` as mathlib's `Proj` of the standard-graded polynomial ring
`ℤ[x₀,…,x_{n-1}]` (`MvPolynomial.homogeneousSubmodule` + the local
`MvPolynomial.gradedAlgebra` instance), its structure map to `Spec ℤ` (the
terminal map), and `P^{n-1}_S = P^{n-1}_ℤ ×_ℤ S` over a base `S`; `P¹_S` is the
case `n = 2`. Properness over `ℤ` rides mathlib's `IsProper (Proj.toSpecZero 𝒜)`
(ProjectiveSpectrum/Proper.lean, transported along terminal uniqueness);
smoothness of `P^{n-1}_S → S` is a named Tier-2 peel (locally affine space,
base change).

The twisting sheaf `O(1)` and the hyperplane class are the named next peels
(V.3 part 2, ticket #285) — they need the Serre twisting sheaf on `Proj`,
absent at the pin.

## References
* Hartshorne, *Algebraic Geometry*, GTM 52, ch. II, §7 (Proj; P^n as
  Proj of the polynomial ring — REVIEW(citation): pin the exercise).
* Stacks Project, tag 01M8 (Proj of a graded ring), tag 01O8 (projective
  space). REVIEW(citation): pin tags.
* Eisenbud–Harris, *3264 and All That* (final draft in refs/), ch. 3.2
  (P^n as G(1,n+1), the Plücker case k=1).
-/

universe u

namespace AlgebraicGeometry

open CategoryTheory Limits

section StandardGrading

attribute [local instance] MvPolynomial.gradedAlgebra

-- Reference: the standard grading on the polynomial ring
-- `ℤ[x₀,…,x_{n-1}]` by total degree (Hartshorne II.7; Stacks 01M8).
/-- The standard-graded polynomial ring `ℤ[x₀,…,x_{n-1}]` as a graded ring
(homogeneous submodules of `MvPolynomial`). `abbrev` so the local grading
instance applies. -/
abbrev projectiveSpaceGradedRing (n : ℕ) :
    ℕ → Submodule (ULift.{u} ℤ) (MvPolynomial (Fin n) (ULift.{u} ℤ)) :=
  MvPolynomial.homogeneousSubmodule (Fin n) (ULift.{u} ℤ)

-- Reference: Hartshorne II.7 — `P^{n-1} = Proj ℤ[x₀,…,x_{n-1}]`.
-- `noncomputable`: `Proj` is choice-backed at the pin.
/-- **Projective space** `P^{n-1}_ℤ = Proj ℤ[x₀,…,x_{n-1}]` (mathlib's `Proj`
of the standard-graded polynomial ring). -/
noncomputable def projectiveSpace (n : ℕ) : Scheme.{u} :=
  «Proj» (projectiveSpaceGradedRing n)

-- Reference: the structure map `P^{n-1}_ℤ ⟶ Spec ℤ` is the terminal map
-- (mathlib's `Proj.toSpecZero` is hidden under a `public section` at the pin;
-- the terminal map agrees with it by uniqueness of maps into `Spec ℤ`).
/-- The structure map `P^{n-1}_ℤ ⟶ Spec ℤ` (the terminal map). -/
noncomputable def projectiveSpaceToSpecZ (n : ℕ) : projectiveSpace n ⟶ specZ :=
  specULiftZIsTerminal.from (projectiveSpace n)

end StandardGrading

-- Reference: `P^{n-1}_S = P^{n-1}_ℤ ×_ℤ S` (base change along the terminal
-- maps; Hartshorne II.7).
/-- **Projective space over a base** `S`: `P^{n-1}_S = P^{n-1}_ℤ ×_ℤ S`.
`noncomputable`: chosen fiber product. -/
noncomputable def projectiveSpaceOver (n : ℕ) (S : Scheme.{u}) : Scheme.{u} :=
  pullback (specULiftZIsTerminal.from S) (projectiveSpaceToSpecZ n)

-- Reference: the projection `P^{n-1}_S ⟶ S` (the first projection of the
-- fiber product).
/-- The projection `P^{n-1}_S ⟶ S`. -/
noncomputable def projectiveSpaceOverProj (n : ℕ) (S : Scheme.{u}) :
    projectiveSpaceOver n S ⟶ S :=
  pullback.fst _ _

-- Reference: `P¹_S` is the case `n = 2` (Hartshorne II.7).
/-- The **projective line** `P¹_S` over `S`. -/
noncomputable def projectiveLine (S : Scheme.{u}) : Scheme.{u} :=
  projectiveSpaceOver 2 S

-- Reference: `Proj` of a finite-type graded ring over its degree-0 part is
-- proper (mathlib `IsProper (Proj.toSpecZero 𝒜)`, ProjectiveSpectrum/Proper.lean,
-- Stacks 01M9?).
-- TEMPORARY SORRY peeling plan: the instance needs `Algebra.FiniteType ↥(𝒜 0) A`
-- (Proper.lean:372); supply it via `MvPolynomial.homogeneousSubmodule_zero`
-- (`𝒜 0 = 1`, so `↥(𝒜 0) ≃ₐ ULift ℤ` by `AlgEquiv.ofInjective (Algebra.ofId _ _)`)
-- and `Algebra.FiniteType.trans` with the `MvPolynomial` finite-type instance;
-- transport `IsProper` along `Spec ↥(𝒜 0) ≅ specZ` (`specULiftZIsTerminal.hom_ext`,
-- `MorphismProperty.RespectsIso @IsProper`).
-- Reference: Stacks 01M9 (properness of Proj of a finite-type graded ring).
/-- `P^{n-1}_ℤ ⟶ Spec ℤ` is proper. -/
theorem isProper_projectiveSpaceToSpecZ (n : ℕ) :
    IsProper (projectiveSpaceToSpecZ n) := by
  -- TEMPORARY SORRY: peeling plan above.
  sorry

-- Reference: `P^{n-1}_S ⟶ S` is smooth (locally affine space; base change of
-- `P^{n-1}_ℤ ⟶ Spec ℤ` smooth — Stacks 01M8/01V? — REVIEW(citation)).
-- TEMPORARY SORRY: peeling plan — smoothness of `Proj` of a polynomial ring
-- (standard opens are affine spaces), stable under base change
-- (`smooth_isStableUnderBaseChange`). -/
theorem smooth_projectiveSpaceOverProj (n : ℕ) (S : Scheme.{u}) :
    Smooth (projectiveSpaceOverProj n S) := by
  -- TEMPORARY SORRY: peeling plan above.
  sorry

end AlgebraicGeometry
