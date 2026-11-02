/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringMath.Physics.LQG.AreaSpectrum
import BoringMath.Physics.MotivicHolographicInfo
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Nat.Cast.Order.Basic

/-!
# Spin networks as data: graphs, relabelings, the diffeomorphism setoid

PHYS.LQG.0 (#352, items 3–6).

Deepening of `Physics/LQG/AreaSpectrum.lean` (#352, item 2): a spin network is
not just an edge set with spins but an **embedded colored graph** — vertices,
edges with endpoints, a spin label per edge, and an intertwiner datum per
vertex (carried as an explicit parameter type `ιw`, per the computability
discipline: no choice-backed data). Two networks related by a **relabeling**
(a pair of equivalences on vertices and edges commuting with all the structure)
are identified: this is the finite-combinatorial shadow of diffeomorphism
invariance, proved an equivalence relation (`relabelingSetoid`). The area and
the ℕ-valued information content `info` are proved invariant under relabeling
(`area_relabel`, `info_relabel`).

The motivic-information hook: `lqgKinematics` is a `MotivicHolographicInfo`
instance whose bulk is the discrete category of spin networks and whose
information measure is the total spin `info`, with the **discrete-info law**
(`lqgKinematics_info_gap`) proved — the ℕ-shadow of the area gap.

## References
* G. N. Rovelli, L. Smolin, "Discreteness of area and volume in quantum
  gravity", Phys. Rev. Lett. 74 (1995) 2318, gr-qc/9411007 — spin networks as
  graphs with spins and intertwiners. REVIEW(citation): pin the section.
* C. Rovelli, *Quantum Gravity*, CUP 2004, ch. 6 — spin networks and
  diffeomorphism invariance. REVIEW(citation): pin the section.
* Program register: BoringMath #352 (PHYS.LQG.0), items 3–6.
-/

namespace BoringMath

open CategoryTheory

variable {ιv ιe ιw : Type*} [DecidableEq ιv] [DecidableEq ιe]

-- Reference: [Rovelli–Smolin 1995]; [Rovelli 2004] ch. 6 — a spin network is
-- embedded in a 3-manifold; here the embedding is the finite incidence data.
/-- A **graph** as data: finite vertex and edge sets with endpoints, each edge
endpoint lying in the vertex set. -/
structure Graph (ιv ιe : Type*) [DecidableEq ιv] [DecidableEq ιe] where
  /-- The finite vertex set. -/
  vertices : Finset ιv
  /-- The finite edge set. -/
  edges : Finset ιe
  /-- The source endpoint of an edge. -/
  src : ιe → ιv
  /-- The target endpoint of an edge. -/
  tgt : ιe → ιv
  /-- Every edge's source is a vertex. -/
  src_mem : ∀ e ∈ edges, src e ∈ vertices
  /-- Every edge's target is a vertex. -/
  tgt_mem : ∀ e ∈ edges, tgt e ∈ vertices

-- Reference: [Rovelli–Smolin 1995]; [Rovelli 2004] ch. 6 — the edge spins
-- `j_e = n_e/2` and the vertex intertwiners; the intertwiner carrier `ιw` is
-- an explicit parameter (computability discipline: no chosen data).
/-- A **colored graph** (a spin network's combinatorial core): a graph with a
spin label per edge and an intertwiner datum per vertex. -/
structure ColoredGraph (ιv ιe ιw : Type*) [DecidableEq ιv] [DecidableEq ιe]
    extends Graph ιv ιe where
  /-- The spin label `n_e` of each edge (`j_e = n_e/2`). -/
  spin : ιe → ℕ
  /-- The intertwiner datum at each vertex. -/
  inter : ιv → ιw

-- Reference: [Rovelli–Smolin 1995] — the spin network forgets the embedding
-- and intertwiners, keeping the edge set and spins (the area data).
/-- The **underlying spin network** of a colored graph: the edge set and spin
labels, as in `AreaSpectrum.lean`. -/
def ColoredGraph.toSpinNetwork {ιv ιe ιw : Type*} [DecidableEq ιv] [DecidableEq ιe]
    (g : ColoredGraph ιv ιe ιw) : SpinNetwork ιe := ⟨g.edges, g.spin⟩

-- Reference: [Rovelli–Smolin 1995]; [Rovelli 2004] ch. 6 — the total area
-- `A₀ Σ_e √(j_e(j_e+1))` computed on the colored graph.
/-- The **area of a colored graph**: `A₀` times the sum of the edge
contributions `√(j_e (j_e + 1))`. -/
-- noncomputable: `Real.sqrt` is noncomputable; the real area spectrum is the content.
noncomputable def ColoredGraph.area {ιv ιe ιw : Type*} [DecidableEq ιv] [DecidableEq ιe]
    (g : ColoredGraph ιv ιe ιw) (A₀ : ℝ) : ℝ :=
  A₀ * ∑ e ∈ g.edges, Real.sqrt (spinJ (g.spin e) * (spinJ (g.spin e) + 1))

-- Reference: projection law for `toSpinNetwork` (STYLE §5: peeled into its
-- own named lemma; `rfl` permitted only here).
/-- **Projection law**: the area of a colored graph equals the area of its
underlying spin network. -/
theorem ColoredGraph.area_toSpinNetwork {ιv ιe ιw : Type*} [DecidableEq ιv] [DecidableEq ιe]
    (g : ColoredGraph ιv ιe ιw) (A₀ : ℝ) :
    g.area A₀ = g.toSpinNetwork.area A₀ := rfl

-- Reference: [Rovelli 2004] ch. 6 — diffeomorphism-equivalent networks are the
-- same state; a relabeling is a pair of equivalences commuting with all
-- structure (the finite shadow of a diffeomorphism).
/-- A **relabeling** between two colored graphs: equivalences on vertices and
edges preserving membership, endpoints, spins, and intertwiners. -/
def ColoredGraph.Relabeling {ιv ιe ιw : Type*} [DecidableEq ιv] [DecidableEq ιe]
    (g g' : ColoredGraph ιv ιe ιw) : Prop :=
  ∃ v : ιv ≃ ιv, ∃ e : ιe ≃ ιe,
    (∀ x, v x ∈ g'.vertices ↔ x ∈ g.vertices) ∧
    (∀ x, e x ∈ g'.edges ↔ x ∈ g.edges) ∧
    (∀ x, g'.src (e x) = v (g.src x)) ∧
    (∀ x, g'.tgt (e x) = v (g.tgt x)) ∧
    (∀ x, g'.spin (e x) = g.spin x) ∧
    (∀ x, g'.inter (v x) = g.inter x)

-- Reference: [Rovelli 2004] ch. 6 — the identity diffeomorphism; relabeling
-- is reflexive.
/-- **Relabeling is reflexive**: the identity equivalences relabel a graph to
itself. -/
theorem ColoredGraph.relabeling_refl {ιv ιe ιw : Type*} [DecidableEq ιv] [DecidableEq ιe]
    (g : ColoredGraph ιv ιe ιw) : ColoredGraph.Relabeling g g :=
  ⟨Equiv.refl _, Equiv.refl _, fun _ => Iff.rfl, fun _ => Iff.rfl,
    fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

-- Reference: [Rovelli 2004] ch. 6 — the inverse diffeomorphism; relabeling is
-- symmetric.
/-- **Relabeling is symmetric**: the inverse equivalences relabel back. -/
theorem ColoredGraph.relabeling_symm {ιv ιe ιw : Type*} [DecidableEq ιv] [DecidableEq ιe]
    {g g' : ColoredGraph ιv ιe ιw} (h : ColoredGraph.Relabeling g g') :
    ColoredGraph.Relabeling g' g := by
  obtain ⟨v, e, hv, he, hs, ht, hsp, hi⟩ := h
  refine ⟨v.symm, e.symm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    exact (Eq.subst (motive := fun z => z ∈ g'.vertices ↔ v.symm x ∈ g.vertices)
      (Equiv.apply_symm_apply v x) (hv (v.symm x))).symm
  · intro x
    exact (Eq.subst (motive := fun z => z ∈ g'.edges ↔ e.symm x ∈ g.edges)
      (Equiv.apply_symm_apply e x) (he (e.symm x))).symm
  · intro x
    have h1 := hs (e.symm x)
    have h2 : g'.src x = v (g.src (e.symm x)) :=
      Eq.subst (motive := fun z => g'.src z = v (g.src (e.symm x)))
        (Equiv.apply_symm_apply e x) h1
    have h3 := congrArg v.symm h2
    exact (Eq.trans h3 (Equiv.symm_apply_apply v (g.src (e.symm x)))).symm
  · intro x
    have h1 := ht (e.symm x)
    have h2 : g'.tgt x = v (g.tgt (e.symm x)) :=
      Eq.subst (motive := fun z => g'.tgt z = v (g.tgt (e.symm x)))
        (Equiv.apply_symm_apply e x) h1
    have h3 := congrArg v.symm h2
    exact (Eq.trans h3 (Equiv.symm_apply_apply v (g.tgt (e.symm x)))).symm
  · intro x
    exact (Eq.subst (motive := fun z => g'.spin z = g.spin (e.symm x))
      (Equiv.apply_symm_apply e x) (hsp (e.symm x))).symm
  · intro x
    exact (Eq.subst (motive := fun z => g'.inter z = g.inter (v.symm x))
      (Equiv.apply_symm_apply v x) (hi (v.symm x))).symm

-- Reference: [Rovelli 2004] ch. 6 — composing diffeomorphisms; relabeling is
-- transitive.
/-- **Relabeling is transitive**: composed equivalences relabel through. -/
theorem ColoredGraph.relabeling_trans {ιv ιe ιw : Type*} [DecidableEq ιv] [DecidableEq ιe]
    {g g' g'' : ColoredGraph ιv ιe ιw}
    (h : ColoredGraph.Relabeling g g') (h' : ColoredGraph.Relabeling g' g'') :
    ColoredGraph.Relabeling g g'' := by
  obtain ⟨v₁, e₁, hv₁, he₁, hs₁, ht₁, hsp₁, hi₁⟩ := h
  obtain ⟨v₂, e₂, hv₂, he₂, hs₂, ht₂, hsp₂, hi₂⟩ := h'
  refine ⟨v₁.trans v₂, e₁.trans e₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    exact Eq.subst (motive := fun z => z ∈ g''.vertices ↔ x ∈ g.vertices)
      (Equiv.trans_apply v₁ v₂ x) (Iff.trans (hv₂ (v₁ x)) (hv₁ x))
  · intro x
    exact Eq.subst (motive := fun z => z ∈ g''.edges ↔ x ∈ g.edges)
      (Equiv.trans_apply e₁ e₂ x) (Iff.trans (he₂ (e₁ x)) (he₁ x))
  · intro x
    have h1 : g''.src (e₂ (e₁ x)) = v₂ (v₁ (g.src x)) :=
      Eq.trans (hs₂ (e₁ x)) (congrArg v₂ (hs₁ x))
    have hA : g''.src (e₂ (e₁ x)) = (v₁.trans v₂) (g.src x) :=
      Eq.subst (motive := fun z => g''.src (e₂ (e₁ x)) = z)
        (Equiv.trans_apply v₁ v₂ (g.src x)).symm h1
    exact Eq.subst (motive := fun z => g''.src z = (v₁.trans v₂) (g.src x))
      (Equiv.trans_apply e₁ e₂ x) hA
  · intro x
    have h1 : g''.tgt (e₂ (e₁ x)) = v₂ (v₁ (g.tgt x)) :=
      Eq.trans (ht₂ (e₁ x)) (congrArg v₂ (ht₁ x))
    have hA : g''.tgt (e₂ (e₁ x)) = (v₁.trans v₂) (g.tgt x) :=
      Eq.subst (motive := fun z => g''.tgt (e₂ (e₁ x)) = z)
        (Equiv.trans_apply v₁ v₂ (g.tgt x)).symm h1
    exact Eq.subst (motive := fun z => g''.tgt z = (v₁.trans v₂) (g.tgt x))
      (Equiv.trans_apply e₁ e₂ x) hA
  · intro x
    have h1 : g''.spin (e₂ (e₁ x)) = g.spin x := Eq.trans (hsp₂ (e₁ x)) (hsp₁ x)
    exact Eq.subst (motive := fun z => g''.spin z = g.spin x)
      (Equiv.trans_apply e₁ e₂ x) h1
  · intro x
    have h1 : g''.inter (v₂ (v₁ x)) = g.inter x := Eq.trans (hi₂ (v₁ x)) (hi₁ x)
    exact Eq.subst (motive := fun z => g''.inter z = g.inter x)
      (Equiv.trans_apply v₁ v₂ x) h1

-- Reference: [Rovelli 2004] ch. 6 — diffeomorphism equivalence as a setoid on
-- spin networks (the quotient is the diffeomorphism-invariant state space).
/-- The **diffeomorphism setoid** on colored graphs: relabeling is an equivalence
relation. -/
instance ColoredGraph.relabelingSetoid {ιv ιe ιw : Type*} [DecidableEq ιv] [DecidableEq ιe] :
    Setoid (ColoredGraph ιv ιe ιw) :=
  ⟨ColoredGraph.Relabeling,
    ⟨ColoredGraph.relabeling_refl, fun h => ColoredGraph.relabeling_symm h,
      fun h h' => ColoredGraph.relabeling_trans h h'⟩⟩

-- Reference: [Rovelli 2004] ch. 6 — the area operator is diffeomorphism
-- invariant (a scalar on diffeomorphism-invariant states).
/-- **The area is relabeling-invariant** (diffeomorphism invariance of the
area operator, finite form). -/
theorem ColoredGraph.area_relabel {ιv ιe ιw : Type*} [DecidableEq ιv] [DecidableEq ιe]
    {g g' : ColoredGraph ιv ιe ιw} (A₀ : ℝ) (h : ColoredGraph.Relabeling g g') :
    g.area A₀ = g'.area A₀ := by
  obtain ⟨v, e, hv, he, hs, ht, hsp, hi⟩ := h
  change A₀ * ∑ x ∈ g.edges, Real.sqrt (spinJ (g.spin x) * (spinJ (g.spin x) + 1))
    = A₀ * ∑ x ∈ g'.edges, Real.sqrt (spinJ (g'.spin x) * (spinJ (g'.spin x) + 1))
  have hmap : g.edges.map e.toEmbedding = g'.edges :=
    Finset.ext fun x =>
      ⟨fun hx => by
          obtain ⟨y, hy, hey⟩ := Finset.mem_map.mp hx
          exact Eq.subst (motive := fun z => z ∈ g'.edges) hey ((he y).mpr hy),
        fun hx => Finset.mem_map.mpr ⟨e.symm x,
          (he (e.symm x)).mp (Eq.subst (motive := fun z => z ∈ g'.edges)
            (Equiv.apply_symm_apply e x).symm hx),
          Equiv.apply_symm_apply e x⟩⟩
  have s1 : ∑ x ∈ g.edges.map e.toEmbedding,
      Real.sqrt (spinJ (g'.spin x) * (spinJ (g'.spin x) + 1))
      = ∑ y ∈ g.edges,
          Real.sqrt (spinJ (g'.spin (e y)) * (spinJ (g'.spin (e y)) + 1)) :=
    Finset.sum_map g.edges e.toEmbedding
      (fun x => Real.sqrt (spinJ (g'.spin x) * (spinJ (g'.spin x) + 1)))
  have s2 : ∑ y ∈ g.edges,
      Real.sqrt (spinJ (g'.spin (e y)) * (spinJ (g'.spin (e y)) + 1))
      = ∑ y ∈ g.edges, Real.sqrt (spinJ (g.spin y) * (spinJ (g.spin y) + 1)) :=
    Finset.sum_congr rfl fun y _ =>
      Eq.subst (motive := fun s =>
        Real.sqrt (spinJ (g'.spin (e y)) * (spinJ (g'.spin (e y)) + 1))
          = Real.sqrt (spinJ s * (spinJ s + 1))) (hsp y) rfl
  have s3 : ∑ x ∈ g.edges.map e.toEmbedding,
      Real.sqrt (spinJ (g'.spin x) * (spinJ (g'.spin x) + 1))
      = ∑ x ∈ g'.edges, Real.sqrt (spinJ (g'.spin x) * (spinJ (g'.spin x) + 1)) :=
    Eq.subst (motive := fun s =>
      ∑ x ∈ g.edges.map e.toEmbedding,
        Real.sqrt (spinJ (g'.spin x) * (spinJ (g'.spin x) + 1))
        = ∑ x ∈ s, Real.sqrt (spinJ (g'.spin x) * (spinJ (g'.spin x) + 1))) hmap rfl
  have hsum : ∑ x ∈ g.edges, Real.sqrt (spinJ (g.spin x) * (spinJ (g.spin x) + 1))
      = ∑ x ∈ g'.edges, Real.sqrt (spinJ (g'.spin x) * (spinJ (g'.spin x) + 1)) :=
    Eq.trans (Eq.trans s1 s2).symm s3
  exact congrArg (fun z => A₀ * z) hsum

-- Reference: MI.0.1 (#67) — the information measure of a state; here the
-- total spin, the ℕ-valued information content of a spin network (the hook
-- onto which the motivic information layer attaches).
/-- The **information content of a spin network**: the total spin
`∑ e ∈ edges, n_e`, an element of the information monoid `ℕ`. -/
def SpinNetwork.info {ι : Type*} [DecidableEq ι] (sn : SpinNetwork ι) : ℕ :=
  ∑ e ∈ sn.edges, sn.spin e

-- Reference: [Rovelli 2004] ch. 6 — diffeomorphism invariance of the state;
-- the information content is relabeling-invariant.
/-- **The information content is relabeling-invariant**. -/
theorem ColoredGraph.info_relabel {ιv ιe ιw : Type*} [DecidableEq ιv] [DecidableEq ιe]
    {g g' : ColoredGraph ιv ιe ιw} (h : ColoredGraph.Relabeling g g') :
    g.toSpinNetwork.info = g'.toSpinNetwork.info := by
  obtain ⟨v, e, hv, he, hs, ht, hsp, hi⟩ := h
  change (∑ x ∈ g.edges, g.spin x) = ∑ x ∈ g'.edges, g'.spin x
  have hmap : g.edges.map e.toEmbedding = g'.edges :=
    Finset.ext fun x =>
      ⟨fun hx => by
          obtain ⟨y, hy, hey⟩ := Finset.mem_map.mp hx
          exact Eq.subst (motive := fun z => z ∈ g'.edges) hey ((he y).mpr hy),
        fun hx => Finset.mem_map.mpr ⟨e.symm x,
          (he (e.symm x)).mp (Eq.subst (motive := fun z => z ∈ g'.edges)
            (Equiv.apply_symm_apply e x).symm hx),
          Equiv.apply_symm_apply e x⟩⟩
  have s1 : ∑ x ∈ g.edges.map e.toEmbedding, g'.spin x
      = ∑ y ∈ g.edges, g'.spin (e y) := Finset.sum_map g.edges e.toEmbedding g'.spin
  have s2 : ∑ y ∈ g.edges, g'.spin (e y) = ∑ y ∈ g.edges, g.spin y :=
    Finset.sum_congr rfl fun y _ => hsp y
  have s3 : ∑ x ∈ g.edges.map e.toEmbedding, g'.spin x
      = ∑ x ∈ g'.edges, g'.spin x :=
    Eq.subst (motive := fun s => ∑ x ∈ g.edges.map e.toEmbedding, g'.spin x
      = ∑ x ∈ s, g'.spin x) hmap rfl
  exact Eq.trans (Eq.trans s1 s2).symm s3

-- Reference: [Rovelli–Smolin 1995] — discreteness of the spectrum, ℕ form:
-- the total spin is either zero or at least one quantum.
/-- **The information gap**: the total spin of a spin network is either `0`
or at least `1`. -/
theorem SpinNetwork.info_gap {ι : Type*} [DecidableEq ι] (sn : SpinNetwork ι) :
    sn.info = 0 ∨ 1 ≤ sn.info := by
  match Classical.em (∃ e ∈ sn.edges, 1 ≤ sn.spin e) with
  | Or.inl h =>
      obtain ⟨e, he, hsp⟩ := h
      exact Or.inr (le_trans hsp
        (Finset.single_le_sum (f := sn.spin) (fun i _ => Nat.zero_le (sn.spin i)) he))
  | Or.inr h =>
      exact Or.inl (Finset.sum_eq_zero fun e he =>
        Nat.lt_one_iff.mp (Nat.not_le.mp (fun hle => h ⟨e, he, hle⟩)))

-- Reference: MHI (#356) — the LQG kinematical layer as an MHI instance: bulk =
-- spin networks (discrete category), hologram = identity, info = ℕ with the
-- total-spin measure; the holographic equation holds by `rfl`.
/-- The **LQG kinematical MHI**: bulk and boundary are the discrete category of
spin networks over `ι`, the hologram is the identity, and the information
measure is the total spin. -/
def lqgKinematics (ι : Type) [DecidableEq ι] : MotivicHolographicInfo.{0, 0, 0, 0, 0} where
  bulk := Discrete (SpinNetwork ι)
  bulkUnit := Discrete.mk ⟨∅, fun _ => 0⟩
  boundary := Discrete (SpinNetwork ι)
  hologram := 𝟭 (Discrete (SpinNetwork ι))
  info := ℕ
  bulkInfo := fun x => x.as.info
  boundaryInfo := fun x => x.as.info
  holographicEq := fun _ => rfl
  boundaryLocality := (CategoryTheory.GrothendieckTopology.trivial _).toCoverage

-- Reference: [Rovelli–Smolin 1995]; #352 — the non-vacuity law of the LQG
-- instance: a nonzero gap in the information measure, proved from the
-- information gap.
/-- **The LQG instance has a discrete information measure**: there is a
nonzero gap `g` such that every bulk state has information `0` or `≥ g`. -/
theorem lqgKinematics_info_gap :
    ∃ g : ℕ, g ≠ 0 ∧ ∀ x : (lqgKinematics (Fin 1)).bulk,
      (lqgKinematics (Fin 1)).bulkInfo x = (0 : ℕ) ∨
        g ≤ ((lqgKinematics (Fin 1)).bulkInfo x : ℕ) :=
  ⟨1, Nat.one_ne_zero, fun x => SpinNetwork.info_gap x.as⟩

end BoringMath
