/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Graph theory — ticket #555

Extremal results on top of pin's `SimpleGraph`: Turán's theorem as the named
target. Sits next to `Combinatorics/Species.lean`/`GenFun.lean` (#293–#300);
spectral graph theory docks the adjacency eigenvalues (links
`InformationTheory` #542 and `RepresentationTheory` #315).

## References
* [Diestel] R. Diestel, *Graph Theory*, 5th ed., Springer 2017, ch. 7.
* [Turán 1941]; mathlib pin v4.35.0-rc3: `Combinatorics/SimpleGraph/*`;
  MISSING: Turán's theorem.
-/

namespace BoringMath

-- Reference: [Diestel], ch. 7.1 (Turán's theorem: a graph on `n` vertices
-- with no clique of size `r+1` has at most `(1 - 1/r) n²/2` edges).
-- TEMPORARY SORRY with peeling plan.
-- PEELING PLAN (#555): (i) Zykov symmetrization: among `K_{r+1}`-free graphs
-- on `n` vertices a maximal one is complete multipartite (symmetrize a
-- non-adjacent pair); (ii) the edge count of a complete `r`-partite graph is
-- maximized by the balanced one (integer convexity of `ab` under `a+b = n`);
-- (iii) the balanced count is `≤ (1 - 1/r) n²/2`.
/-- **Turán's theorem**: a `K_{r+1}`-free graph on `n` vertices has at most
`(1 - 1/r) n² / 2` edges. -/
theorem turan {n r : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hr : 0 < r)
    (hfree : ¬ ∃ S : Finset (Fin n), S.card = r + 1 ∧
      ∀ a ∈ S, ∀ b ∈ S, a ≠ b → G.Adj a b) :
    (G.edgeFinset.card : ℝ) ≤ (1 - 1 / (r : ℝ)) * (n : ℝ) ^ 2 / 2 := by
  sorry

end BoringMath
