/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card

/-!
# Spectral sequences — ticket #557

Homological spectral sequences as data: pages `Eʳ`, differentials
`dʳ : Eʳ_{p,q} → Eʳ_{p+r, q-r+1}` with `dʳ ∘ dʳ = 0`. Extends
`Cohomology/GroupCohomology.lean` (#315) toward the Lyndon–Hochschild–Serre
and Grothendieck spectral sequences (CFSG reduction phase #248).

## References
* [Weibel] *The K-book* / *An Introduction to Homological Algebra*, ch. 5.
* [McCleary] J. McCleary, *A User's Guide to Spectral Sequences*, ch. 1–2.
* mathlib pin v4.35.0-rc3: `RepresentationTheory/Homological` (group
  cohomology); MISSING: spectral sequences.
-/

namespace BoringMath

-- Reference: [McCleary], ch. 1 (a homological spectral sequence: pages and
-- differentials with `d² = 0`).
/-- A **homological spectral sequence**: pages `E r p q` (abelian groups) and
differentials `d r : E r p q → E r (p+r) (q-r+1)` squaring to zero. -/
structure SpectralSequence where
  E : ℕ → ℕ → ℕ → Type
  instAdd : ∀ r p q, AddCommGroup (E r p q)
  d : ∀ (r p q : ℕ) (_x : E r p q), E r (p + r) (q - r + 1)
  d_sq : ∀ (r p q : ℕ) (x : E r p q), d r (p + r) (q - r + 1) (d r p q x) = 0

-- Reference: [McCleary], ch. 1 (each page `E r p q` is an abelian group; the
-- instance is derived from the structure field).
/-- Each page `E r p q` is an abelian group. -/
instance spectralSequence_addCommGroup (S : SpectralSequence) (r p q : ℕ) :
    AddCommGroup (S.E r p q) :=
  S.instAdd r p q

-- Reference: [Weibel], ch. 5.8 (Lyndon–Hochschild–Serre: for `N ⊴ G` the
-- spectral sequence `H_p(G/N, H_q(N, A)) ⇒ H_{p+q}(G, A)` exists).
-- TEMPORARY SORRY with peeling plan.
-- PEELING PLAN (#557, #248): (i) the bar resolution of `G` filtered by `N`
-- gives a double complex; (ii) its total complex carries the LHS spectral
-- sequence (existence as data + `d² = 0`); (iii) convergence to
-- `H_*(G, A)` by the comparison theorem (pin group cohomology).
/-- **Existence of the Lyndon–Hochschild–Serre spectral sequence**
(statement layer). -/
theorem exists_lyndon_hochschild_serre (G : Type*) [Group G]
    (N : Subgroup G) [N.Normal] [Fintype G] [DecidablePred (· ∈ N)] :
    ∃ (S : SpectralSequence), Nonempty (S.E (Fintype.card G) (Fintype.card ↥N) 0) := by
  sorry

end BoringMath
