/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Dynamics.Transitive
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Devaney chaos — ticket #309

For a self-map `f : α → α` on a metric space: topological transitivity,
dense periodic points, sensitive dependence, and Devaney chaos (all three).
Banks' theorem (transitivity + dense periodic points ⇒ sensitive dependence) is
stated with a peeling plan.

## References
* [Devaney] R. L. Devaney, *An Introduction to Chaotic Dynamical Systems*,
  Westview 1989, ch. 1.7.
* [Banks–Brooks–Cairns–Davis–Stacey 1992] (the implication proved in #310).
* mathlib pin v4.35.0-rc3: `Dynamics.periodicPts`, `Dynamics.Transitive`.
-/

namespace BoringMath

variable {α : Type*} [TopologicalSpace α] [PseudoMetricSpace α]

-- Reference: [Devaney], ch. 1.7 (topological transitivity of a self-map);
-- cf. pin's `MulAction.IsTopologicallyTransitive` for monoid actions.
/-- `f` is **topologically transitive**: every nonempty open set meets every
nonempty open set under some iterate. -/
def TopologicallyTransitive (f : α → α) : Prop :=
  ∀ U V : Set α, IsOpen U → U.Nonempty → IsOpen V → V.Nonempty →
    ∃ n : ℕ, ∃ x ∈ U, f^[n] x ∈ V

-- Reference: mathlib pin v4.35.0-rc3, `Dynamics.periodicPts`.
/-- `f` has **dense periodic points**. -/
def DensePeriodicPts (f : α → α) : Prop := Dense (Function.periodicPts f)

-- Reference: [Devaney], ch. 1.7 (sensitive dependence on initial conditions).
/-- `f` has **sensitive dependence on initial conditions**: some `δ > 0` works
at every point: every neighbourhood contains a point whose orbit eventually
separates by `δ`. -/
def SensitiveDependence (f : α → α) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ x : α, ∀ ε : ℝ, 0 < ε →
    ∃ y : α, dist x y < ε ∧ ∃ n : ℕ, δ < dist (f^[n] x) (f^[n] y)

-- Reference: [Devaney], ch. 1.7 (Devaney's definition of chaos).
/-- `f` is **chaotic in the sense of Devaney**. -/
def DevaneyChaos (f : α → α) : Prop :=
  TopologicallyTransitive f ∧ DensePeriodicPts f ∧ SensitiveDependence f

-- Reference: [Banks–Brooks–Cairns–Davis–Stacey 1992]. TEMPORARY SORRY with
-- peeling plan.
-- PEELING PLAN (#310): given transitivity and dense periodic points, take two
-- periodic points `p q` of periods `m n` with `dist p q > δ/2`-ish; by
-- transitivity some iterate of a neighbourhood of `x` lands near `p` and
-- another near `q`; the periodic orbits then separate by a fixed amount —
-- choose `δ` from `max` over finitely many relevant pairs (density reduces to
-- the countable/finite periodic set in the compact case; the general metric
-- proof uses the two periodic points directly).
/-- **Banks' theorem**: transitivity + dense periodic points ⇒ sensitive
dependence. TEMPORARY SORRY with peeling plan. -/
theorem sensitive_of_transitive_densePeriodic (f : α → α)
    (ht : TopologicallyTransitive f) (hp : DensePeriodicPts f) :
    SensitiveDependence f := by
  sorry

end BoringMath
