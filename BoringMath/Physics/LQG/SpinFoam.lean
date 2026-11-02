/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringMath.Physics.LQG.SpinNetwork
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Cast.Order.Basic

/-!
# Spin foams: 2-complexes with labels, amplitudes, and boundaries — PHYS.LQG.0 (#352, items 13–15)

A spin foam as data: a finite 2-complex shadow — vertices, edges (with spins),
faces (with face spins), vertex amplitudes, and a designated boundary edge set.
The **amplitude** is the product of vertex amplitudes times the representation
dimensions `dim(j) = 2j + 1 = n + 1` of the edge and face labels. The
**boundary network** is the spin network on the boundary edges, and the
boundary area is proved bounded by the total (bulk) area — the finite
shadow of the holographic monotonicity of information.

## References
* L. Freidel, D. Louapre, "Ponzano–Regge model revisited", Nucl. Phys. B 641
  (2002) 307, hep-th/0205286, §2 — spin foams as labeled 2-complexes with
  vertex amplitudes. REVIEW(citation): pin the section.
* E. R. Livine, D. Oriti, "Spin foam models of quantum gravity", in *Handbook
  of Spacetime*, Springer 2014, arXiv:1205.2019 — the amplitude structure.
  REVIEW(citation): pin the section.
* J. W. Barrett, C. M. Rocek, "Classical and quantum gravity in 1+2 dimensions",
  in *Classical and Quantum Gravity* — the Ponzano–Regge amplitude.
  REVIEW(citation): pin.
* R. De Pietri, "Spin foam models for quantum gravity", J. Math. Phys. 40
  (1999) — dimensions of SU(2) irreps. REVIEW(citation): pin.
* Program register: BoringMath #352 (PHYS.LQG.0), items 13–15.
-/

namespace BoringMath

variable {ιv ιe ιf : Type*} [DecidableEq ιv] [DecidableEq ιe] [DecidableEq ιf]

-- Reference: [De Pietri 1999] — the spin-j irreducible representation of SU(2)
-- has dimension `2j + 1`; with `j = n/2` this is `n + 1`.
/-- The **dimension of the spin-j representation**: `dim(j) = 2j + 1 = n + 1`
for `j = n/2`. -/
def repDim (n : ℕ) : ℝ := (n : ℝ) + 1

-- Reference: [De Pietri 1999] — representation dimensions are positive.
/-- **Representation dimensions are positive**: `0 < dim(j)`. -/
theorem repDim_pos (n : ℕ) : 0 < repDim n :=
  add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) zero_lt_one

-- Reference: [Freidel–Louapre 2002] §2; [Livine–Oriti] — a spin foam is a
-- labeled 2-complex; all data explicit (computability discipline).
/-- A **spin foam** as data: a graph with edge spins, faces with face spins,
vertex amplitudes, and a designated boundary edge set. -/
structure Foam (ιv ιe ιf : Type*) [DecidableEq ιv] [DecidableEq ιe] [DecidableEq ιf]
    extends Graph ιv ιe where
  /-- The spin label of each (internal or boundary) edge. -/
  spin : ιe → ℕ
  /-- The finite face set. -/
  faces : Finset ιf
  /-- The face spin of each face. -/
  faceSpin : ιf → ℕ
  /-- The vertex amplitude at each vertex. -/
  vamp : ιv → ℝ
  /-- Vertex amplitudes are nonnegative (positivity of the amplitude). -/
  vamp_nonneg : ∀ v ∈ vertices, 0 ≤ vamp v
  /-- The boundary edge set. -/
  boundary : Finset ιe
  /-- Boundary edges are edges. -/
  boundary_mem : ∀ e ∈ boundary, e ∈ edges

-- Reference: [Freidel–Louapre 2002] §2 — the foam amplitude: product of vertex
-- amplitudes and representation dimensions of all labels.
/-- The **amplitude of a spin foam**: the product of the vertex amplitudes and
the representation dimensions of the edge and face spins. -/
-- noncomputable: ℝ multiplication is noncomputable; the real amplitude is the content.
noncomputable def Foam.amplitude {ιv ιe ιf : Type*} [DecidableEq ιv] [DecidableEq ιe]
    [DecidableEq ιf] (f : Foam ιv ιe ιf) : ℝ :=
  (∏ v ∈ f.vertices, f.vamp v) *
    ((∏ e ∈ f.edges, repDim (f.spin e)) * ∏ fc ∈ f.faces, repDim (f.faceSpin fc))

-- Reference: [Freidel–Louapre 2002] §2 — positivity of the amplitude from
-- positivity of vertex amplitudes and dimensions.
/-- **The amplitude is nonnegative** when vertex amplitudes are. -/
theorem Foam.amplitude_nonneg {ιv ιe ιf : Type*} [DecidableEq ιv] [DecidableEq ιe]
    [DecidableEq ιf] (f : Foam ιv ιe ιf) : 0 ≤ f.amplitude :=
  mul_nonneg (Finset.prod_nonneg fun v hv => f.vamp_nonneg v hv)
    (mul_nonneg (Finset.prod_nonneg fun e _ => (repDim_pos (f.spin e)).le)
      (Finset.prod_nonneg fun fc _ => (repDim_pos (f.faceSpin fc)).le))

-- Reference: [Rovelli 2004] ch. 6 — the boundary of a spin foam is a spin
-- network on the boundary edges.
/-- The **boundary spin network** of a foam: the boundary edges with their
spins. -/
def Foam.boundaryNetwork {ιv ιe ιf : Type*} [DecidableEq ιv] [DecidableEq ιe]
    [DecidableEq ιf] (f : Foam ιv ιe ιf) : SpinNetwork ιe := ⟨f.boundary, f.spin⟩

-- Reference: projection law (STYLE §5): peeled into its own named lemma.
/-- **Projection law**: the boundary network's area is the boundary edge sum. -/
theorem Foam.boundaryNetwork_area {ιv ιe ιf : Type*} [DecidableEq ιv] [DecidableEq ιe]
    [DecidableEq ιf] (f : Foam ιv ιe ιf) (A₀ : ℝ) :
    f.boundaryNetwork.area A₀
      = A₀ * ∑ e ∈ f.boundary, Real.sqrt (spinJ (f.spin e) * (spinJ (f.spin e) + 1)) := rfl

-- Reference: MHI (#356) — holographic monotonicity in finite form: the
-- boundary area is at most the total area (information does not grow from
-- bulk to boundary).
/-- **Boundary area ≤ bulk area**: the area of the boundary network is at most
the area of the whole foam's edge set. -/
theorem Foam.boundary_area_le {ιv ιe ιf : Type*} [DecidableEq ιv] [DecidableEq ιe]
    [DecidableEq ιf] (f : Foam ιv ιe ιf) {A₀ : ℝ} (hA : 0 ≤ A₀) :
    f.boundaryNetwork.area A₀
      ≤ A₀ * ∑ e ∈ f.edges, Real.sqrt (spinJ (f.spin e) * (spinJ (f.spin e) + 1)) := by
  change A₀ * ∑ e ∈ f.boundary, Real.sqrt (spinJ (f.spin e) * (spinJ (f.spin e) + 1))
    ≤ A₀ * ∑ e ∈ f.edges, Real.sqrt (spinJ (f.spin e) * (spinJ (f.spin e) + 1))
  exact mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum_of_subset_of_nonneg
      (fun e he => f.boundary_mem e he)
      fun e _ _ => Real.sqrt_nonneg _)
    hA

end BoringMath
