/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Init

/-!
# Sequent calculus and cut elimination — ticket #538 (proposed #335–#338)

A sequent-calculus interface over an abstract formula type: sequents `Γ ⊢ Δ`,
a derivability relation, and Gentzen's cut-elimination theorem as the named
target. Mathlib at the pin has `Logic` and a rich `ModelTheory` but no proof
theory (audited: #335–#338 are gaps).

## References
* [Gentzen 1935] G. Gentzen, *Untersuchungen über das logische Schließen*,
  Math. Z. 39 (1935) 405–431 (cut elimination, Hauptsatz).
* [Takeuti] G. Takeuti, *Proof Theory*, North-Holland 1975, ch. 1.
* mathlib pin v4.35.0-rc3: `Logic`, `ModelTheory`; MISSING: sequent calculus,
  cut elimination.
-/

namespace BoringMath

-- Reference: [Takeuti], ch. 1, §2 (a sequent is `Γ ⊢ Δ`).
/-- A **sequent** over a formula type `F`: antecedents `Γ` and succedents `Δ`. -/
structure Sequent (F : Type*) where
  ante : List F
  succ : List F

-- Reference: [Takeuti], ch. 1, §3 (a sequent calculus is given by initial
-- sequents and inference rules, closing into a derivability relation).
/-- A **sequent calculus**: a derivability relation together with its
cut-free fragment, satisfying the closure laws. -/
structure SequentCalculus (F : Type*) where
  derivable : Sequent F → Prop
  cutFreeDerivable : Sequent F → Prop
  cutFree_subset : ∀ s, cutFreeDerivable s → derivable s

-- Reference: [Gentzen 1935], Hauptsatz. TEMPORARY SORRY with peeling plan.
-- PEELING PLAN (#538, #335): (i) define derivations as an inductive family
-- over the rules of `C`; (ii) prove by double induction on (cut-rank,
-- cut-degree) that every derivation of `Γ, A ⊢ Δ` and `Γ ⊢ A, Δ` reduces
-- to a cut-free derivation of `Γ ⊢ Δ` (the Gentzen reductions, one named
-- lemma per rule pair); (iii) conclude.
/-- **Cut elimination** (Gentzen's Hauptsatz): every derivable sequent has
a cut-free derivation. -/
theorem cut_elimination {F : Type*} (C : SequentCalculus F) (s : Sequent F)
    (h : C.derivable s) : C.cutFreeDerivable s := by
  sorry

end BoringMath
