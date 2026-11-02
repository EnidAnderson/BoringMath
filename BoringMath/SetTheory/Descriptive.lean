/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Topology.MetricSpace.Polish

/-!
# Descriptive set theory — ticket #535

The perfect-set theorem for closed subsets of Polish spaces (Cantor–
Bendixson), the entry point of the descriptive hierarchy. Mathlib at the
pin has `PolishSpace` but `SetTheory/Descriptive/` holds only a tree API
(audited: the descriptive hierarchy — Borel/analytic sets, perfect set
theorem — is a gap).

## References
* [Kechris] A. S. Kechris, *Classical Descriptive Set Theory*, GSM 156,
  Springer 1995, ch. I §6 (Cantor–Bendixson), ch. II (Borel sets).
* mathlib pin v4.35.0-rc3: `PolishSpace`; MISSING: `SetTheory/Descriptive`
  hierarchy, perfect set theorem.
-/

namespace BoringMath

variable {X : Type*} [TopologicalSpace X]

-- Reference: [Kechris], ch. I §4 (a set is perfect when it is closed and
-- has no isolated points).
/-- A set is **perfect**: closed and dense-in-itself (every point is a
cluster point of the rest). -/
def IsPerfectSet (A : Set X) : Prop :=
  IsClosed A ∧ ∀ x ∈ A, x ∈ closure (A \ {x})

-- Reference: [Kechris], ch. I, Theorem 6.4 (Cantor–Bendixson / perfect set
-- theorem for closed sets). TEMPORARY SORRY with peeling plan.
-- PEELING PLAN (#535): (i) the Cantor–Bendixson derivative
-- `A' = A \ {isolated points}` iterated transfinitely stabilizes at the
-- perfect kernel `P` (pin: `Ordinal` API); (ii) if `A` is uncountable, `P`
-- is nonempty (a countable scattered closed set is countable — construct the
-- CB rank injection into `ℕ`); (iii) `P` is perfect.
/-- **Perfect set theorem** (closed case): every uncountable closed subset
of a Polish space contains a nonempty perfect subset. -/
theorem perfect_set_theorem_closed {X : Type*} [TopologicalSpace X] [PolishSpace X]
    (A : Set X) (hA : IsClosed A) (hunc : ¬ A.Countable) :
    ∃ B : Set X, B ⊆ A ∧ B.Nonempty ∧ IsPerfectSet B := by
  sorry

end BoringMath
