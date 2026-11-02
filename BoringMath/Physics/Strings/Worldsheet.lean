/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic

/-!
# The lattice worldsheet and the Polyakov action — PHYS.STR.0 (#366, items 1–3)

The bosonic string's worldsheet, regularized as a finite lattice: vertices,
edges, and a scalar field `X` (the embedding into a 1-dimensional target as
the toy). The **lattice Polyakov action** `S = (T/2) Σ_edges (∂X)²` with string
tension `T`, and two of its exact laws proved outright: **nonnegativity** and
**translation invariance** (target-space translations are a symmetry of the
free action), plus quadratic homogeneity in the field.

## References
* J. Polchinski, *String Theory*, vol. 1, CUP 1998, ch. 1 §1.2 — the Polyakov
  action. REVIEW(citation): pin the equation number.
* D. Friedan, "Nonlinear models in 2+ε dimensions", Ann. Phys. 163 (1985)
  318, §2 — the lattice regularization. REVIEW(citation): pin the section.
* Program register: BoringMath #366 (PHYS.STR.0), items 1–3.
-/

namespace BoringMath

variable {ιv : Type*} [DecidableEq ιv]

-- Reference: [Friedan 1985] §2 — the worldsheet regularized as a finite
-- lattice: a finite set of vertices and of edges between them.
/-- A **lattice worldsheet**: finite vertex and edge sets, each edge joining
two vertices. -/
structure LatticeWorldsheet (ιv : Type*) [DecidableEq ιv] where
  /-- The finite vertex set (worldsheet lattice sites). -/
  vertices : Finset ιv
  /-- The finite edge set (worldsheet links). -/
  edges : Finset (ιv × ιv)
  /-- Every edge joins two vertices. -/
  edge_mem : ∀ e ∈ edges, e.1 ∈ vertices ∧ e.2 ∈ vertices

-- Reference: [Polchinski 1998] ch. 1 §1.2 — the Polyakov action on the
-- lattice: `S = (T/2) Σ (∂X)²` with string tension `T`.
/-- The **lattice Polyakov action**: `(T/2)` times the sum of squared edge
derivatives of the field `X`. -/
-- noncomputable: ℝ operations are noncomputable; the real action is the content.
noncomputable def polyakovAction (T : ℝ) {ιv : Type*} [DecidableEq ιv]
    (ws : LatticeWorldsheet ιv) (X : ιv → ℝ) : ℝ :=
  (T / 2) * ∑ e ∈ ws.edges, (X e.2 - X e.1) ^ 2

-- Reference: [Polchinski 1998] ch. 1 §1.2 — the action is nonnegative for
-- nonnegative string tension (the Euclidean lattice action is bounded below).
/-- **The lattice Polyakov action is nonnegative** for `T ≥ 0`. -/
theorem polyakovAction_nonneg (T : ℝ) {ιv : Type*} [DecidableEq ιv]
    (ws : LatticeWorldsheet ιv) (X : ιv → ℝ) (hT : 0 ≤ T) :
    0 ≤ polyakovAction T ws X :=
  mul_nonneg (div_nonneg hT two_pos.le) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

-- Reference: [Polchinski 1998] ch. 1 — translation invariance of the free
-- action: `X ↦ X + c` leaves the edge derivatives, hence the action, fixed.
/-- **The lattice Polyakov action is translation-invariant**: adding a
constant to the field does not change the action. -/
theorem polyakovAction_translate (T : ℝ) {ιv : Type*} [DecidableEq ιv]
    (ws : LatticeWorldsheet ιv) (X : ιv → ℝ) (c : ℝ) :
    polyakovAction T ws (fun v => X v + c) = polyakovAction T ws X := by
  change (T / 2) * ∑ e ∈ ws.edges, ((X e.2 + c) - (X e.1 + c)) ^ 2
    = (T / 2) * ∑ e ∈ ws.edges, (X e.2 - X e.1) ^ 2
  exact congrArg (fun z => (T / 2) * z)
    (Finset.sum_congr rfl fun e _ =>
      congrArg (fun z => z ^ 2) (add_sub_add_right_eq_sub (X e.2) (X e.1) c))

-- Reference: [Polchinski 1998] ch. 1 §1.2 — the action is quadratic in the
-- field: scaling `X` by `s` scales the action by `s²`.
/-- **The lattice Polyakov action is quadratic in the field**: scaling the
field by `s` scales the action by `s²`. -/
theorem polyakovAction_smul (T s : ℝ) {ιv : Type*} [DecidableEq ιv]
    (ws : LatticeWorldsheet ιv) (X : ιv → ℝ) :
    polyakovAction T ws (fun v => s * X v) = s ^ 2 * polyakovAction T ws X := by
  change (T / 2) * ∑ e ∈ ws.edges, ((s * X e.2) - (s * X e.1)) ^ 2
    = s ^ 2 * ((T / 2) * ∑ e ∈ ws.edges, (X e.2 - X e.1) ^ 2)
  have hsum : ∑ e ∈ ws.edges, ((s * X e.2) - (s * X e.1)) ^ 2
      = ∑ e ∈ ws.edges, s ^ 2 * (X e.2 - X e.1) ^ 2 :=
    Finset.sum_congr rfl fun e _ =>
      Eq.trans (congrArg (fun z => z ^ 2) (mul_sub s (X e.2) (X e.1)).symm)
        (mul_pow s (X e.2 - X e.1) 2)
  exact Eq.trans (congrArg (fun z => (T / 2) * z) hsum)
    (Eq.trans
      (congrArg (fun z => (T / 2) * z)
        (Finset.mul_sum ws.edges (fun e => (X e.2 - X e.1) ^ 2) (s ^ 2)).symm)
      (mul_left_comm (T / 2) (s ^ 2) _))



-- Reference: background independence at the lattice level — relabeling the
-- lattice sites is a symmetry of the data; [Friedan 1985] §2 (the lattice has
-- no fixed background, only the edge set).
/-- The **relabeling of a lattice worldsheet** by a vertex equivalence `e`:
vertices and edges are transported along `e`. -/
def LatticeWorldsheet.relabel {ιv : Type*} [DecidableEq ιv]
    (ws : LatticeWorldsheet ιv) (e : ιv ≃ ιv) : LatticeWorldsheet ιv where
  vertices := ws.vertices.map e.toEmbedding
  edges := ws.edges.map (e.prodCongr e).toEmbedding
  edge_mem := fun p hp => by
    obtain ⟨q, hq, hqp⟩ := Finset.mem_map.mp hp
    obtain ⟨h1, h2⟩ := ws.edge_mem q hq
    exact ⟨Finset.mem_map.mpr ⟨q.1, h1, congrArg Prod.fst hqp⟩,
      Finset.mem_map.mpr ⟨q.2, h2, congrArg Prod.snd hqp⟩⟩

-- Reference: [Friedan 1985] §2; background independence — the lattice Polyakov
-- action is invariant under relabeling the sites (transport the field along
-- the relabeling).
/-- **The lattice Polyakov action is relabeling-invariant**: transporting the
lattice and the field along a vertex equivalence leaves the action unchanged. -/
theorem polyakovAction_relabel (T : ℝ) {ιv : Type*} [DecidableEq ιv]
    (ws : LatticeWorldsheet ιv) (e : ιv ≃ ιv) (X : ιv → ℝ) :
    polyakovAction T (ws.relabel e) (fun v => X (e.symm v))
      = polyakovAction T ws X := by
  change (T / 2) * ∑ p ∈ ws.edges.map (e.prodCongr e).toEmbedding,
      ((X (e.symm p.2)) - (X (e.symm p.1))) ^ 2
    = (T / 2) * ∑ q ∈ ws.edges, (X q.2 - X q.1) ^ 2
  have hsum : ∑ p ∈ ws.edges.map (e.prodCongr e).toEmbedding,
      ((X (e.symm p.2)) - (X (e.symm p.1))) ^ 2
      = ∑ q ∈ ws.edges,
          ((X (e.symm ((e.prodCongr e) q).2)) - (X (e.symm ((e.prodCongr e) q).1))) ^ 2 :=
    Finset.sum_map ws.edges (e.prodCongr e).toEmbedding _
  have hterm : ∀ q : ιv × ιv,
      ((X (e.symm ((e.prodCongr e) q).2)) - (X (e.symm ((e.prodCongr e) q).1))) ^ 2
        = (X q.2 - X q.1) ^ 2 := by
    intro q
    have h1 : (e.prodCongr e) q = (e q.1, e q.2) := rfl
    have ha : X (e.symm ((e.prodCongr e) q).2) = X q.2 :=
      Eq.trans (congrArg (fun p => X (e.symm p.2)) h1)
        (congrArg X (Equiv.symm_apply_apply e q.2))
    have hb : X (e.symm ((e.prodCongr e) q).1) = X q.1 :=
      Eq.trans (congrArg (fun p => X (e.symm p.1)) h1)
        (congrArg X (Equiv.symm_apply_apply e q.1))
    exact congrArg (fun z => z ^ 2)
      (Eq.trans (congrArg (fun z => z - X (e.symm ((e.prodCongr e) q).1)) ha)
        (congrArg (fun z => X q.2 - z) hb))
  exact congrArg (fun z => (T / 2) * z)
    (Eq.trans hsum (Finset.sum_congr rfl fun q _ => hterm q))

end BoringMath
