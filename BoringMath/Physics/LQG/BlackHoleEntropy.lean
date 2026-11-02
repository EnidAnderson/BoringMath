/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringMath.Physics.LQG.SpinNetwork
import Mathlib.Analysis.Real.Sqrt

/-!
# Black-hole entropy matching `S = A/4` in counting form — PHYS.LQG.2 (#471)

The lab ledger demand LQG.1.1 #27 (demand 8) asks for the Bekenstein–Hawking
saturation in counting form: some positive area scale `A₀` and some spin
network with positive information content satisfy `area = 4 · info`. This
module exhibits the witness honestly: a single edge carrying one quantum of
spin (`n = 1`, `j = 1/2`), with the area scale chosen as `A₀ = 4 / √(j(j+1))`,
so that `area A₀ = A₀ · √(j(j+1)) = 4 = 4 · info`. No asymptotics, no unproved
state counting — just the exact real-arithmetic identity.

The full state-counting per puncture (intertwiner dimensions at the horizon,
repDim products) remains the named extension under #474.

## References
* J. D. Bekenstein, "Black holes and entropy", Phys. Rev. D 7 (1973) 2333.
* S. W. Hawking, "Black hole explosions?", Nature 248 (1974) 30.
* A. Ashtekar, K. Krasnov, Phys. Rev. D 67 (2003) 104025 — the `S = A/4`
  matching in LQG, counting form. REVIEW(citation): pin the counting.
* Program register: BoringMath #471; lab ledger BoringLab #27 (LQG.1.1).
-/

namespace BoringMath

-- Reference: [Ashtekar–Krasnov 2003] — the horizon puncture as a single edge
-- with one quantum of spin `n = 1`.
/-- The **single-quantum witness network**: one edge (index `0 : Fin 1`)
carrying spin `1`. -/
def bhWitnessNetwork : SpinNetwork (Fin 1) := ⟨{0}, fun _ => 1⟩

-- Reference: projection law (STYLE §5): peeled into its own named lemma.
/-- **Projection law**: the witness edge carries spin `1`. -/
theorem bhWitnessNetwork_spin_zero : bhWitnessNetwork.spin 0 = 1 := rfl

-- Reference: [Ashtekar–Krasnov 2003] — the witness has information content `1`.
/-- **The witness network has info `1`**: `∑ e ∈ {0}, spin e = 1`. -/
theorem bhWitnessNetwork_info : bhWitnessNetwork.info = 1 :=
  Eq.trans (Finset.sum_singleton bhWitnessNetwork.spin 0) bhWitnessNetwork_spin_zero

-- Reference: [Rovelli 2004] ch. 6 — `j = n/2`, so `spinJ 1 = 1/2`.
/-- **The spin-`1` label is `j = 1/2`** (projection law, proved). -/
theorem spinJ_one : spinJ 1 = (1 : ℝ) / 2 :=
  congrArg (fun z => z / 2) Nat.cast_one

-- Reference: [Ashtekar–Krasnov 2003] — the counting-form saturation `S = A/4`.
/-- **Black-hole entropy matching in counting form**: there is a positive area
scale `A₀` and a spin network with positive information whose area equals
`4 · info` — the `S = A/4` saturation. Witness: the single-quantum network with
`A₀ = 4 / √(spinJ 1 · (spinJ 1 + 1))`, so `area = (4/S) · S = 4 = 4 · 1`
(exact, via `div_mul_cancel₀`; no asymptotics). -/
theorem bekenstein_hawking_counting :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∃ ι : Type, ∃ _ : DecidableEq ι,
      ∃ sn : SpinNetwork ι, 0 < sn.info ∧ sn.area A₀ = 4 * (sn.info : ℝ) := by
  have hhalf : 0 < spinJ 1 :=
    Eq.subst (motive := fun z => (0 : ℝ) < z) spinJ_one.symm (div_pos one_pos two_pos)
  have hterm : 0 < spinJ 1 * (spinJ 1 + 1) := mul_pos hhalf (add_pos hhalf one_pos)
  have hS : Real.sqrt (spinJ 1 * (spinJ 1 + 1)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hterm)
  have hsum : ∑ e ∈ bhWitnessNetwork.edges,
      Real.sqrt (spinJ (bhWitnessNetwork.spin e) * (spinJ (bhWitnessNetwork.spin e) + 1))
      = Real.sqrt (spinJ 1 * (spinJ 1 + 1)) :=
    Eq.trans (Finset.sum_singleton
        (fun e => Real.sqrt (spinJ (bhWitnessNetwork.spin e)
          * (spinJ (bhWitnessNetwork.spin e) + 1))) 0)
      (congrArg (fun n => Real.sqrt (spinJ n * (spinJ n + 1)))
        bhWitnessNetwork_spin_zero)
  have hcast : (bhWitnessNetwork.info : ℝ) = 1 :=
    Eq.trans (congrArg (Nat.cast (R := ℝ)) bhWitnessNetwork_info) Nat.cast_one
  refine ⟨4 / Real.sqrt (spinJ 1 * (spinJ 1 + 1)),
    div_pos (Nat.cast_pos.mpr (Nat.zero_lt_succ 3)) (Real.sqrt_pos.mpr hterm),
    Fin 1, inferInstance, bhWitnessNetwork,
    Eq.subst (motive := fun n => (0 : ℕ) < n) bhWitnessNetwork_info.symm Nat.one_pos, ?_⟩
  calc bhWitnessNetwork.area (4 / Real.sqrt (spinJ 1 * (spinJ 1 + 1)))
      = (4 / Real.sqrt (spinJ 1 * (spinJ 1 + 1)))
          * Real.sqrt (spinJ 1 * (spinJ 1 + 1)) :=
        congrArg (fun z => (4 / Real.sqrt (spinJ 1 * (spinJ 1 + 1))) * z) hsum
    _ = 4 := div_mul_cancel₀ 4 hS
    _ = 4 * (bhWitnessNetwork.info : ℝ) :=
        Eq.trans (mul_one 4).symm (congrArg (fun z => (4 : ℝ) * z) hcast.symm)

end BoringMath
