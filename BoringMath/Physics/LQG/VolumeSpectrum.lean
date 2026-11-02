/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringMath.Physics.LQG.SpinNetwork
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.Field.Basic

/-!
# The volume operator and the volume gap — PHYS.LQG.0 (#352, items 10–12)

The volume operator of LQG as a **structure with laws**: a real-valued function
on spin networks that is nonnegative, relabeling- (diffeomorphism-) invariant,
and **discrete** — its nonzero values are bounded below by a positive gap
(the volume gap of Rovelli–Smolin). The toy calibration `areaAsVolume`
(volume = area) proves all four laws outright, the discreteness resting on the
area gap of `AreaSpectrum.lean` and the exact vanishing of the `j = 0` edge
contribution. The full Rovelli–Smolin volume spectrum (intertwiners and 6j
symbols at each vertex) is the named extension, tracked in the lab ledger
LQG.1.1 (#27).

## References
* G. N. Rovelli, L. Smolin, "Discreteness of area and volume in quantum
  gravity", Phys. Rev. Lett. 74 (1995) 2318, gr-qc/9411007 — the volume
  operator and its discrete spectrum. REVIEW(citation): pin the equation.
* C. Rovelli, *Quantum Gravity*, CUP 2004, ch. 6 — the volume spectrum.
  REVIEW(citation): pin the section.
* Program register: BoringMath #352 (PHYS.LQG.0), items 10–12.
-/

namespace BoringMath

variable {ι : Type*} [DecidableEq ι]

-- Reference: [Rovelli–Smolin 1995] — `j = n/2`, so `j = 0` when `n = 0`.
/-- **The zero spin is zero**: `spinJ 0 = 0`. -/
theorem spinJ_zero : spinJ 0 = (0 : ℝ) := by
  change ((0 : ℕ) : ℝ) / 2 = 0
  exact Eq.trans (congrArg (fun z => z / 2) Nat.cast_zero) (zero_div 2)

-- Reference: [Rovelli–Smolin 1995] — the `j = 0` edge contributes exactly
-- zero area: `√(0 · (0 + 1)) = 0`.
/-- **The zero-spin edge term vanishes**: `√(spinJ 0 * (spinJ 0 + 1)) = 0`. -/
theorem spin_edgeTerm_zero : Real.sqrt (spinJ 0 * (spinJ 0 + 1)) = 0 :=
  Eq.trans (congrArg Real.sqrt
    (Eq.trans (congrArg (fun j => j * (spinJ 0 + 1)) spinJ_zero) (zero_mul _)))
    Real.sqrt_zero

-- Reference: [Rovelli–Smolin 1995] — a network all of whose spins are zero has
-- zero area.
/-- **Zero area when all spins vanish**: if every edge has spin `0`, the area
is `0`. -/
theorem SpinNetwork.area_eq_zero_of_all_spin_zero {A₀ : ℝ} {sn : SpinNetwork ι}
    (h : ∀ e ∈ sn.edges, sn.spin e = 0) : sn.area A₀ = 0 := by
  change A₀ * ∑ e ∈ sn.edges, Real.sqrt (spinJ (sn.spin e) * (spinJ (sn.spin e) + 1)) = 0
  exact Eq.trans (congrArg (fun z => A₀ * z) (Finset.sum_eq_zero fun e he =>
    Eq.subst (motive := fun n => Real.sqrt (spinJ n * (spinJ n + 1)) = 0) (h e he).symm
      spin_edgeTerm_zero)) (mul_zero A₀)

-- Reference: [Rovelli–Smolin 1995] — discreteness of the area spectrum in
-- dichotomy form: the area is either zero or at least the fundamental gap.
/-- **The area gap dichotomy**: the area of a spin network is either `0` or at
least the fundamental gap `A₀ √(3/4)`. -/
theorem SpinNetwork.area_gap_or_zero {A₀ : ℝ} (hA : 0 < A₀) (sn : SpinNetwork ι) :
    sn.area A₀ = 0 ∨ A₀ * Real.sqrt ((1 : ℝ) / 2 * ((1 : ℝ) / 2 + 1)) ≤ sn.area A₀ := by
  match Classical.em (∃ e ∈ sn.edges, 1 ≤ sn.spin e) with
  | Or.inl h => exact Or.inr (SpinNetwork.area_gap hA.le sn h)
  | Or.inr h =>
      exact Or.inl (sn.area_eq_zero_of_all_spin_zero fun e he =>
        Nat.lt_one_iff.mp (Nat.not_le.mp (fun hle => h ⟨e, he, hle⟩)))

-- Reference: [Rovelli–Smolin 1995]; [Rovelli 2004] ch. 6 — the volume operator
-- as a structure with its laws as explicit fields (never `axiom`): positivity,
-- diffeomorphism invariance, and discreteness (the volume gap) as a Prop field.
/-- A **volume operator** on spin networks over `ι`: a real-valued assignment
that is nonnegative, invariant under relabeling (the finite diffeomorphism
invariance), and discrete (a positive gap below every nonzero value). -/
structure VolumeOperator (ι : Type*) [DecidableEq ι] where
  /-- The volume of a spin network. -/
  volume : SpinNetwork ι → ℝ
  /-- Volumes are nonnegative. -/
  nonneg : ∀ sn, 0 ≤ volume sn
  /-- Diffeomorphism invariance: relabeling does not change the volume. -/
  relabel_invariant : ∀ {ιv ιw : Type} [DecidableEq ιv]
      {g g' : ColoredGraph ιv ι ιw},
    ColoredGraph.Relabeling g g' → volume g.toSpinNetwork = volume g'.toSpinNetwork
  /-- **Discreteness (the volume gap)**: some positive `gap` bounds every
  nonzero volume from below. -/
  discrete : ∃ gap : ℝ, 0 < gap ∧ ∀ sn : SpinNetwork ι, volume sn = 0 ∨ gap ≤ volume sn

-- Reference: toy calibration — volume = area proves all four laws of the
-- volume operator; the gap is the area gap.
/-- The **area-as-volume toy**: the area operator itself satisfies the volume
operator laws (a degenerate but non-vacuous calibration). -/
-- noncomputable: `SpinNetwork.area` is noncomputable; the spectrum is the content.
noncomputable def areaAsVolume (ι : Type*) [DecidableEq ι] (A₀ : ℝ) (hA : 0 < A₀) :
    VolumeOperator ι where
  volume := fun sn => sn.area A₀
  nonneg := fun _sn =>
    mul_nonneg hA.le (Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _)
  relabel_invariant := fun {ιv _ιw} [DecidableEq ιv] {g g'} h =>
    Eq.trans (ColoredGraph.area_toSpinNetwork g A₀).symm
      (Eq.trans (ColoredGraph.area_relabel A₀ h) (ColoredGraph.area_toSpinNetwork g' A₀))
  discrete :=
    ⟨A₀ * Real.sqrt ((1 : ℝ) / 2 * ((1 : ℝ) / 2 + 1)),
      mul_pos hA (Real.sqrt_pos.mpr (mul_pos (half_pos zero_lt_one)
        (add_pos (half_pos zero_lt_one) zero_lt_one))),
      fun sn => sn.area_gap_or_zero hA⟩

-- Reference: [Rovelli–Smolin 1995] — the volume gap of the toy instance is
-- exactly the area gap, with the gap positive.
/-- **The toy volume operator has a positive gap**: its discrete law holds
with gap `A₀ √(3/4) > 0`. -/
theorem areaAsVolume_gap_pos (A₀ : ℝ) (hA : 0 < A₀) :
    0 < A₀ * Real.sqrt ((1 : ℝ) / 2 * ((1 : ℝ) / 2 + 1)) :=
  mul_pos hA (Real.sqrt_pos.mpr (mul_pos (half_pos zero_lt_one)
    (add_pos (half_pos zero_lt_one) zero_lt_one)))

end BoringMath
