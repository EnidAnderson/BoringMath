/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringMath.Physics.LQG.SpinNetwork
import BoringMath.AlgebraicGeometry.AlgebraicCycle.Zero
import BoringMath.AlgebraicGeometry.ResidueField.Tower
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.RingTheory.Spectrum.Prime.Basic

/-!
# The puncture-cycle model of spin networks — PHYS.LQG.0 (#352, item 16; fills bridge ticket #369)

The cycle-level reading of a spin network: over the affine scheme of a field
`k`, a spin network is modeled by ONE puncture point-cycle at the closed point
of `Spec k`, carrying the total spin `info` as its coefficient. The **degree
(trace) of the puncture cycle is exactly the total spin**: `degree_single`
gives `r · residueDegree`, and `residueDegree_id` gives `residueDegree (𝟙) = 1`,
so `degree (𝟙) (puncture cycle) = info`. Hence every network with positive
total spin has a cycle model of nonzero degree — the MI.0.2 bridge row #369,
filled. The finer model (one puncture per edge, degrees = area eigenvalues via
the spin labels) is the named extension.

## References
* [Fulton] ch. 1 §1.4 (degree of a point cycle = r × residue degree);
  `AlgebraicCycle/Zero.lean` (`degree_single`), `ResidueField/Tower.lean`
  (`residueDegree_of_isIso`, `residueDegree_id`).
* [Rovelli–Smolin 1995] — punctures of spin network edges on a surface.
* Program register: BoringMath #352 item 16; lab MI.0.2 #66 ticket #369.
-/

namespace BoringMath

open AlgebraicGeometry
open CategoryTheory

variable (k : Type) [Field k]

-- Reference: the affine scheme of the field `k` (`Spec k`); noncomputable
-- because `Scheme.Spec` is noncomputable.
/-- The **puncture scheme**: `Spec k` for a field `k`. -/
noncomputable def punctureScheme (k : Type) [Field k] : Scheme :=
  Scheme.Spec.obj (Opposite.op (CommRingCat.of k))

-- Reference: in a field the zero ideal is prime, so `Spec k` has the closed
-- point `⊥`; the carrier of `Spec k` is `PrimeSpectrum k` definitionally.
/-- The **puncture point**: the closed point of `Spec k`. -/
def puncturePoint (k : Type) [Field k] : ↥(punctureScheme k) :=
  (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k)

open scoped Classical in
-- Reference: [Rovelli–Smolin 1995] + [Fulton] ch. 1 — the puncture cycle of a
-- spin network: one point cycle at the puncture point carrying the total spin.
/-- The **puncture cycle of a spin network**: the point cycle at the puncture
point with coefficient = total spin. -/
-- noncomputable: `locallyFinsuppWithin.single` is noncomputable (Classical).
noncomputable def spinNetworkCycle {ι : Type} [DecidableEq ι] (k : Type) [Field k]
    (sn : SpinNetwork ι) : AlgebraicCycle (punctureScheme k) ℤ :=
  Function.locallyFinsuppWithin.single (puncturePoint k) (sn.info : ℤ)

open scoped Classical in
-- Reference: support of a point cycle is the singleton (Zero.lean
-- `support_single_subset`), transported to the Finset coercion.
/-- **Support of the puncture cycle**: contained in the puncture-point
singleton. -/
theorem spinNetworkCycle_support_subset {ι : Type} [DecidableEq ι] (k : Type) [Field k]
    (sn : SpinNetwork ι) :
    (spinNetworkCycle k sn).support ⊆ ↑({puncturePoint k} : Finset ↥(punctureScheme k)) :=
  Eq.subst (motive := fun t => (spinNetworkCycle k sn).support ⊆ t)
    (Finset.coe_singleton (puncturePoint k)).symm AlgebraicCycle.support_single_subset

open scoped Classical in
-- Reference: [Fulton] ch. 1 §1.4 — `degree_single` + `residueDegree_id`: the
-- degree of the puncture cycle along the identity is the total spin.
/-- **The degree of the puncture cycle is the total spin**: `degree (𝟙)
(puncture cycle) = info`. -/
theorem spinNetworkCycle_degree {ι : Type} [DecidableEq ι] (k : Type) [Field k]
    (sn : SpinNetwork ι) :
    ∃ (s : Finset ↥(punctureScheme k)) (hs : (spinNetworkCycle k sn).support ⊆ ↑s),
      AlgebraicCycle.degree (𝟙 (punctureScheme k)) (spinNetworkCycle k sn) s hs
        = (sn.info : ℤ) := by
  refine ⟨{puncturePoint k}, spinNetworkCycle_support_subset k sn, ?_⟩
  exact Eq.trans
    (AlgebraicCycle.degree_single (𝟙 (punctureScheme k)) (puncturePoint k) (sn.info : ℤ)
      (spinNetworkCycle_support_subset k sn))
    (Eq.trans
      (congrArg (fun z : ℕ => (sn.info : ℤ) * (z : ℤ))
        (Scheme.Hom.residueDegree_id (puncturePoint k)))
      (mul_one _))

open scoped Classical in
-- Reference: #369 — the puncture-degree model: a network with positive total
-- spin has a cycle model of nonzero degree.
/-- **Nonzero puncture degree**: if `0 < sn.info`, the puncture cycle has
nonzero degree. -/
theorem spinNetworkCycle_degree_ne_zero {ι : Type} [DecidableEq ι] (k : Type) [Field k]
    (sn : SpinNetwork ι) (h : 0 < sn.info) :
    ∃ (s : Finset ↥(punctureScheme k)) (hs : (spinNetworkCycle k sn).support ⊆ ↑s),
      AlgebraicCycle.degree (𝟙 (punctureScheme k)) (spinNetworkCycle k sn) s hs ≠ 0 := by
  obtain ⟨s, hs, hdeg⟩ := spinNetworkCycle_degree k sn
  refine ⟨s, hs, fun h0 => ?_⟩
  exact Int.natCast_ne_zero.mpr (Nat.ne_of_gt h) (hdeg.symm.trans h0)

end BoringMath
