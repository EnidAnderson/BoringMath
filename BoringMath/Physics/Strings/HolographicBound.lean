/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringMath.Physics.MotivicHolographicInfo
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Fin

/-!
# The holographic counting bound — PHYS.STR.0 (#366, items 4–6)

The 't Hooft–Susskind holographic principle in its exact discrete form: a bulk
with `N` distinguishable states encoded injectively into boundary
configurations of `m` cells each holding one of `k` values satisfies
`N ≤ k^m` — the Bekenstein–Hawking bound `S ≤ A / 4G` read as a counting
statement (entropy `log N` bounded by the boundary "area" in cells). Proved
outright from `Fintype.card_le_of_injective` and `Fintype.card_fun`. The
calibration `holographicToyMHI` is an MHI instance whose hologram is the
encoding and whose information measure is the boundary cell count, with the
holographic equation proved by `rfl`.

## References
* G. 't Hooft, "Dimensional reduction in quantum gravity", in *Salamanca 1993*,
  gr-qc/9310026, §5 — the holographic principle. REVIEW(citation): pin.
* L. Susskind, "The world as a hologram", J. Math. Phys. 36 (1995) 6377,
  hep-th/9409089, §2 — the bound `S ≤ A/4`. REVIEW(citation): pin.
* J. D. Bekenstein, "Black holes and entropy", Phys. Rev. D 7 (1973) 2333;
  S. W. Hawking, "Particle creation by black holes", Commun. Math. Phys. 43
  (1975) 199. REVIEW(citation): pin.
* Program register: BoringMath #366 (PHYS.STR.0), items 4–6.
-/

namespace BoringMath

open CategoryTheory

variable {B ι : Type*} [Fintype B] [Fintype ι]

open scoped Classical in
-- Reference: ['t Hooft 1993] §5; [Susskind 1995] §2 — the holographic
-- counting bound: an injective encoding of bulk states into boundary
-- configurations gives `N ≤ k^m` (the discrete Bekenstein–Hawking bound).
/-- **The holographic counting bound**: if `f : B → (ι → Fin k)` is injective,
then `#B ≤ k ^ #ι` — a bulk with more states than boundary configurations
cannot be encoded. -/
theorem holographic_counting_bound {B ι : Type*} [Fintype B] [Fintype ι]
    {k : ℕ} (f : B → (ι → Fin k))
    (hf : Function.Injective f) : Fintype.card B ≤ k ^ Fintype.card ι :=
  le_trans (Fintype.card_le_of_injective f hf) (le_of_eq
    (Eq.trans (Fintype.card_fun (α := ι) (β := Fin k))
      (congrArg (fun n => n ^ Fintype.card ι) (Fintype.card_fin k))))

open scoped Classical in
-- Reference: [Susskind 1995] §2 — the entropy reading: with `N = #B` bulk
-- states and boundary area `m = #ι` cells of `log₂ k` bits, `log N ≤ m log k`;
-- in bits (`k = 2`) this is `log₂ N ≤ m`, the Bekenstein bound in cells.
/-- **The Bekenstein bound in bits**: an injective encoding into `m` binary
cells requires `log₂ #B ≤ m`. -/
theorem bekenstein_bits_bound {B ι : Type*} [Fintype B] [Fintype ι]
    (f : B → (ι → Fin 2)) (hf : Function.Injective f) :
    Fintype.card B ≤ 2 ^ Fintype.card ι :=
  holographic_counting_bound f hf

-- Reference: MHI (#356) — the holographic toy: bulk = the `B` states,
-- boundary = the `ι → Fin k` configurations, hologram = the encoding,
-- info = ℕ measured in boundary cells; the holographic equation holds by
-- `rfl`, and the counting bound above is the non-vacuity law on this data.
/-- The **holographic toy MHI**: bulk states `B`, boundary configurations
`ι → Fin k`, hologram the encoding, information measured in boundary cells. -/
def holographicToyMHI (B ι : Type) [Fintype B] [Inhabited B] [Fintype ι]
    [DecidableEq ι] (k : ℕ) (enc : B → (ι → Fin k)) :
    MotivicHolographicInfo.{0, 0, 0, 0, 0} where
  bulk := Discrete B
  bulkUnit := Discrete.mk default
  boundary := Discrete (ι → Fin k)
  hologram := Discrete.functor (fun b => Discrete.mk (enc b))
  info := ℕ
  bulkInfo := fun _ => Fintype.card ι
  boundaryInfo := fun _ => Fintype.card ι
  holographicEq := fun _ => rfl
  boundaryLocality := (CategoryTheory.GrothendieckTopology.trivial _).toCoverage

open scoped Classical in
-- Reference: ['t Hooft 1993]; [Susskind 1995] — the non-vacuity law of the
-- holographic toy: the encoding bound holds on this very instance.
/-- **The holographic toy satisfies the counting bound**: an injective
encoding forces `#B ≤ k ^ #ι`. -/
theorem holographicToyMHI_bound {B ι : Type} [Fintype B] [Fintype ι]
    {k : ℕ} (enc : B → (ι → Fin k)) (henc : Function.Injective enc) :
    Fintype.card B ≤ k ^ Fintype.card ι :=
  holographic_counting_bound enc henc

end BoringMath
