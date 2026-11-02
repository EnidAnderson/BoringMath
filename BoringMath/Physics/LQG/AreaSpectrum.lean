/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringMath.Foundations.Arithmetic

/-!
# The area spectrum of loop quantum gravity — the area-gap row (#352, item 2)

The formula-level row of `PHYS.LQG.0` (#352): a spin network as data (finite
edge set + spin labels; vertex intertwiners are the named extension), the
area `A₀ · Σ_e √(j_e (j_e + 1))` with `j_e = n_e/2` and fundamental area scale
`A₀ = 8πγℓ_P²`, and the **area gap** proved outright: any network with an edge
of spin `≥ 1` (i.e. `j ≥ 1/2`) has area at least `A₀ · √(3/4)` — the
discreteness of the area spectrum (finite combinatorics, no analysis).

All proofs are pure terms over the named lemmas of
`BoringMath.Foundations.Arithmetic` — no tactics.

## References
* G. N. Rovelli, L. Smolin, "Discreteness of area and volume in quantum
  gravity", Phys. Rev. Lett. 74 (1995) 2318, gr-qc/9411007 — the area
  operator and its spectrum. REVIEW(citation): pin the equation number.
* C. Rovelli, *Quantum Gravity*, CUP 2004, ch. 6 — the area spectrum
  `8πγℓ_P² Σ √(j(j+1))`. REVIEW(citation): pin the section.
* Program register: BoringMath #352 (PHYS.LQG.0), item 2 (formula-level row).
-/

namespace BoringMath

/-- The spin label as a real number: `j = n/2` for `n : ℕ` (the half-integers
`½ℕ`, encoded by naturals). -/
-- Reference: [Rovelli 2004] ch. 6 (spins are half-integers j = n/2). REVIEW(citation): pin.
-- noncomputable: ℝ division (`Real.instDivInvMonoid`) is noncomputable; the real spectrum is the content.
noncomputable def spinJ (n : ℕ) : ℝ := (n : ℝ) / 2

/-- The area contributed by one edge of spin `n`, with fundamental area
scale `A₀ = 8πγℓ_P²` taken as a parameter. -/
-- Reference: [Rovelli–Smolin 1995]; [Rovelli 2004] ch. 6 — the edge area
-- `A₀ √(j(j+1))` with `A₀ = 8πγℓ_P²`. REVIEW(citation): pin the equation.
-- noncomputable: `Real.sqrt` is noncomputable; the real area spectrum is the content.
noncomputable def edgeArea (A₀ : ℝ) (n : ℕ) : ℝ := A₀ * Real.sqrt (spinJ n * (spinJ n + 1))

-- Reference: [Rovelli–Smolin 1995] (spin networks: graph + edge spins +
-- vertex intertwiners); the intertwiners are the named extension, this module
-- carries the edge data only.
/-- A **spin network** as data: a finite edge set with a spin label per edge. -/
structure SpinNetwork (ι : Type*) [DecidableEq ι] where
  /-- The finite edge set. -/
  edges : Finset ι
  /-- The spin label `n_e` of each edge (`j_e = n_e/2`). -/
  spin : ι → ℕ

/-- The **area of a spin network**: `A₀` times the sum of the edge
contributions `√(j_e (j_e + 1))`. -/
-- Reference: [Rovelli–Smolin 1995]; [Rovelli 2004] ch. 6 — the total area
-- `A₀ Σ_e √(j_e(j_e+1))`. REVIEW(citation): pin the equation.
-- noncomputable: `Real.sqrt` is noncomputable; the real area spectrum is the content.
noncomputable def SpinNetwork.area {ι : Type*} [DecidableEq ι] (sn : SpinNetwork ι) (A₀ : ℝ) : ℝ :=
  A₀ * ∑ e ∈ sn.edges, Real.sqrt (spinJ (sn.spin e) * (spinJ (sn.spin e) + 1))

-- Reference: [Rovelli–Smolin 1995]; [Rovelli 2004] ch. 6 — the per-edge
-- contribution is monotone in the spin: an edge with `n ≥ 1` contributes at
-- least the `j = 1/2` amount `√(3/4)`.
/-- **The per-edge area gap**: an edge of spin `n ≥ 1` (i.e. `j ≥ 1/2`)
contributes at least `A₀ · √((1/2)(1/2 + 1)) = A₀ √(3/4)`. -/
theorem edgeArea_gap {A₀ : ℝ} (hA : 0 ≤ A₀) {n : ℕ} (hn : 1 ≤ n) :
    A₀ * Real.sqrt ((1 : ℝ) / 2 * ((1 : ℝ) / 2 + 1)) ≤ edgeArea A₀ n :=
  mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (mul_le_mul (half_le_half_cast hn)
      (add_le_add_left (half_le_half_cast hn) 1) half_add_one_nonneg
      (half_cast_nonneg n)))
    hA

-- Reference: [Rovelli–Smolin 1995] — discreteness of the area spectrum: the
-- total area is bounded below by the fundamental gap whenever some edge
-- carries a quantum of spin.
/-- **The area gap**: a spin network with an edge of spin `≥ 1` has area at
least the fundamental gap `A₀ · √(3/4)`. -/
theorem SpinNetwork.area_gap {ι : Type*} [DecidableEq ι] {A₀ : ℝ} (hA : 0 ≤ A₀)
    (sn : SpinNetwork ι) (h : ∃ e ∈ sn.edges, 1 ≤ sn.spin e) :
    A₀ * Real.sqrt ((1 : ℝ) / 2 * ((1 : ℝ) / 2 + 1)) ≤ sn.area A₀ :=
  let ⟨e, he, hsp⟩ := h
  le_trans (edgeArea_gap hA hsp)
    (mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (f := fun i => Real.sqrt (spinJ (sn.spin i) * (spinJ (sn.spin i) + 1))) (fun i _ => Real.sqrt_nonneg _) he)
      hA)

end BoringMath
