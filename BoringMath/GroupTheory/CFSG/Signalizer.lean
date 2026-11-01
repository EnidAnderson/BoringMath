/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Signalizer functors — the core machinery of the CFSG reduction

Ticket CFSG.LIB (#236), feeding CFSG.R.1 (#227). A **signalizer functor** `θ` on
a finite group `G` for a set `π` of primes assigns to every `p`-subgroup `P` of
`G` (with `p ∈ π`) a subgroup `θ(P) ≤ C_G(P)`, nontrivial when `P` is,
conjugation-invariant, and complete (`P ≤ Q` implies `θ(P) ≤ θ(Q)`). The balance
theorem and the nonsolvable signalizer functor theorem are the deep results
built on this definition.

mathlib at the pin has `IsPGroup` and centralizers but no signalizer functors.

## References
* [GLS] Number 2 (signalizer functors, balance); Goldschmidt (1981);
  Flavell, arXiv:1609.08311 (new proof, in `refs/`).
-/

namespace BoringMath

open Subgroup

variable {G : Type*} [Group G]

-- Reference: [GLS] Number 2, ch. 1 (definition of a complete signalizer
-- functor); Flavell arXiv:1609.08311 §2 (same axioms).
/-- A **signalizer functor** on `G` for the prime set `π`: to each `p`-subgroup
`P` (`p ∈ π`) a subgroup `θ P ≤ C_G(P)`, nontrivial on nontrivial `P`,
conjugation-invariant, and complete. -/
structure SignalizerFunctor (G : Type*) [Group G] (π : Set ℕ) where
  /-- The assigned subgroup of the centralizer. -/
  theta : (p : ℕ) → p ∈ π → (P : Subgroup G) → IsPGroup p P → Subgroup G
  /-- `θ(P)` centralizes `P`. -/
  theta_le_centralizer : ∀ (p : ℕ) (hp : p ∈ π) (P : Subgroup G) (hP : IsPGroup p P),
    theta p hp P hP ≤ centralizer (P : Set G)
  /-- `θ(P)` is nontrivial when `P` is. -/
  theta_ne_bot : ∀ (p : ℕ) (hp : p ∈ π) (P : Subgroup G) (hP : IsPGroup p P), P ≠ ⊥ →
    theta p hp P hP ≠ ⊥
  /-- Conjugation invariance: `θ(P^g) = θ(P)^g`. -/
  theta_conj : ∀ (p : ℕ) (hp : p ∈ π) (P : Subgroup G) (hP : IsPGroup p P) (g : G),
    theta p hp (P.map (MulAut.conj g).toMonoidHom) (hP.map (MulAut.conj g).toMonoidHom) =
      (theta p hp P hP).map (MulAut.conj g).toMonoidHom
  /-- Completeness: `P ≤ Q` implies `θ(P) ≤ θ(Q)`. -/
  theta_mono : ∀ (p : ℕ) (hp : p ∈ π) (P Q : Subgroup G) (hP : IsPGroup p P)
    (hQ : IsPGroup p Q), P ≤ Q → theta p hp P hP ≤ theta p hp Q hQ

end BoringMath
