/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Field.Basic
import BoringMath.FormalPeriods.FreeMod
import BoringMath.FormalPeriods.FormalPeriods.FinSum
import BoringMath.FormalPeriods.FormalPeriods.FreeModHomModule
import BoringMath.FormalPeriods.FormalPeriods.Dual
import BoringMath.FormalPeriods.FormalPeriods.BaseChange

/-!
# The pairing of a `K`-dual with an `L`-vector

`pairL φ ω y = ∑ j, φ(ω eⱼ) * yⱼ` along `φ : K →+* L`, with its bilinearity
laws and the base-change compatibility `pairLBaseHom`.  Split out of
`BoringMath.FormalPeriods.FormalPeriods`.
-/

universe u

namespace BoringMath.FormalPeriods

variable {B K L : Type u} [Field B] [Field K] [Field L] [Algebra B K] [Algebra K L]
variable {m n : ℕ}

/-! ## The pairing of a `K`-dual with an `L`-vector -/

-- Reference: Hörmann, arXiv:2106.03803, Def 2.5 (`eval_∫` pairs `ω ∈ H_dR(M)∨`
-- with `∫_M(σ) ∈ H_dR(M) ⊗_K L`: `ω(∫_M σ) = ∑ j, φ(ω eⱼ) * (∫_M σ)ⱼ`);
-- Axler, LADR 4th ed., Ch. 2–3 (expansion in the standard basis).
/-- The pairing of a `K`-dual vector `ω : FreeModDual K n` with an `L`-vector
`y : FreeMod L n` along `φ : K →+* L`: `ω(y) = ∑ j, φ(ω eⱼ) * yⱼ`. -/
def pairL {K L : Type u} [Field K] [Field L] (φ : K →+* L) {n : ℕ}
    (ω : FreeModDual K n) (y : FreeMod L n) : L :=
  finSum n (fun j => φ (dualVal ω (Pi.single j (1 : K))) * y j)

-- Reference: Hörmann, arXiv:2106.03803, Def 2.5 (the pairing is linear in the
-- second argument); Axler, LADR 4th ed., Ch. 3; list lemmas.
/-- The pairing is additive in the second argument. -/
theorem pairLAddRight {K L : Type u} [Field K] [Field L] (φ : K →+* L) {n : ℕ}
    (ω : FreeModDual K n) (y z : FreeMod L n) :
    pairL φ ω (y + z) = pairL φ ω y + pairL φ ω z := by
  unfold pairL
  calc finSum n (fun j => φ (dualVal ω (Pi.single j (1 : K))) * (y + z) j)
      = finSum n (fun j => φ (dualVal ω (Pi.single j (1 : K))) * (y j + z j)) :=
          listSum_congr (List.finRange n) _ _ (fun j =>
            congrArg (fun t => _ * t) (Pi.add_apply y z j))
    _ = finSum n (fun j => (φ (dualVal ω (Pi.single j (1 : K))) * y j
          + φ (dualVal ω (Pi.single j (1 : K))) * z j)) :=
          listSum_congr (List.finRange n) _ _ (fun j => mul_add _ _ _)
    _ = finSum n (fun j => φ (dualVal ω (Pi.single j (1 : K))) * y j)
        + finSum n (fun j => φ (dualVal ω (Pi.single j (1 : K))) * z j) :=
          listSum_map_add (List.finRange n) _ _

-- Reference: Hörmann, arXiv:2106.03803, Def 2.5; Axler, LADR 4th ed., Ch. 3;
-- list lemmas (`listSum_congr`, `listSum_map_mul_left`, `mul_left_comm`).
/-- The pairing is `L`-linear in the second argument. -/
theorem pairLSmulRight {K L : Type u} [Field K] [Field L] (φ : K →+* L) {n : ℕ}
    (ω : FreeModDual K n) (c : L) (y : FreeMod L n) :
    pairL φ ω (c • y) = c * pairL φ ω y := by
  unfold pairL
  calc finSum n (fun j => φ (dualVal ω (Pi.single j (1 : K))) * (c • y) j)
      = finSum n (fun j => φ (dualVal ω (Pi.single j (1 : K))) * (c * y j)) :=
          listSum_congr (List.finRange n) _ _ (fun j =>
            congrArg (fun t => _ * t) (Eq.trans (Pi.smul_apply c y j) (smul_eq_mul c (y j))))
    _ = finSum n (fun j => c * (φ (dualVal ω (Pi.single j (1 : K))) * y j)) :=
          listSum_congr (List.finRange n) _ _ (fun j => mul_left_comm _ c _)
    _ = c * finSum n (fun j => φ (dualVal ω (Pi.single j (1 : K))) * y j) :=
          listSum_map_mul_left (List.finRange n) c _

-- Reference: Axler, LADR 4th ed., Ch. 3; list lemmas (`listSum_congr`,
-- `listSum_zero`, `Pi.zero_apply`, `mul_zero`).
/-- The pairing with the zero vector is zero. -/
theorem pairLZeroRight {K L : Type u} [Field K] [Field L] (φ : K →+* L) {n : ℕ}
    (ω : FreeModDual K n) : pairL φ ω 0 = 0 := by
  unfold pairL
  calc finSum n (fun j => φ (dualVal ω (Pi.single j (1 : K))) * (0 : FreeMod L n) j)
      = finSum n (fun j => φ (dualVal ω (Pi.single j (1 : K))) * (0 : L)) :=
          listSum_congr (List.finRange n) _ _ (fun j =>
            congrArg (fun t => _ * t) (Pi.zero_apply j))
    _ = finSum n (fun _ => (0 : L)) :=
          listSum_congr (List.finRange n) _ _ (fun j => mul_zero _)
    _ = 0 := listSum_zero (List.finRange n)

-- Reference: Axler, LADR 4th ed., Ch. 1 (linearity extends to finite sums);
-- proved by hand by `List` induction (`pairLListSum`).
/-- The pairing commutes with list sums in the second argument. -/
theorem pairLListSum {K L : Type u} [Field K] [Field L] (φ : K →+* L) {n : ℕ}
    (ω : FreeModDual K n) (k : ℕ) (g : Fin k → FreeMod L n) (l : List (Fin k)) :
    pairL φ ω ((l.map g).sum) = (l.map (fun i => pairL φ ω (g i))).sum := by
  induction l with
  | nil =>
      exact Eq.trans (congrArg (pairL φ ω) (listMapNilSum g))
        (Eq.trans (pairLZeroRight φ ω) (listMapNilSum (fun i => pairL φ ω (g i))).symm)
  | cons a l ih =>
      exact Eq.trans (congrArg (pairL φ ω) (listMapConsSum g a l))
        (Eq.trans (pairLAddRight φ ω (g a) ((l.map g).sum))
          (Eq.trans (congrArg (fun w => pairL φ ω (g a) + w) ih)
            (listMapConsSum (fun i => pairL φ ω (g i)) a l).symm))

-- Reference: Axler, LADR 4th ed., Ch. 1 (linearity extends to finite sums).
/-- The pairing commutes with finite sums in the second argument. -/
theorem pairLSumRight {K L : Type u} [Field K] [Field L] (φ : K →+* L) {n : ℕ}
    (ω : FreeModDual K n) (k : ℕ) (g : Fin k → FreeMod L n) :
    pairL φ ω (finSum k g) = finSum k (fun i => pairL φ ω (g i)) :=
  pairLListSum φ ω k g (List.finRange k)

-- Reference: Hörmann, arXiv:2106.03803, Def 2.5 (the pairing is linear in the
-- dual argument); Axler, LADR 4th ed., Ch. 3; list lemmas; mathlib (`map_add`,
-- `add_mul`).
/-- The pairing is additive in the dual argument. -/
theorem pairLAddLeft {K L : Type u} [Field K] [Field L] (φ : K →+* L) {n : ℕ}
    (ω₁ ω₂ : FreeModDual K n) (y : FreeMod L n) :
    pairL φ (ω₁ + ω₂) y = pairL φ ω₁ y + pairL φ ω₂ y := by
  unfold pairL
  calc finSum n (fun j => φ (dualVal (ω₁ + ω₂) (Pi.single j (1 : K))) * y j)
      = finSum n (fun j => φ (dualVal ω₁ (Pi.single j (1 : K))
          + dualVal ω₂ (Pi.single j (1 : K))) * y j) :=
          listSum_congr (List.finRange n) _ _ (fun j =>
            congrArg (fun t => φ t * y j) (dualValAdd ω₁ ω₂ _))
    _ = finSum n (fun j => (φ (dualVal ω₁ (Pi.single j (1 : K)))
          + φ (dualVal ω₂ (Pi.single j (1 : K)))) * y j) :=
          listSum_congr (List.finRange n) _ _ (fun j =>
            congrArg (fun t => t * y j) (map_add φ _ _))
    _ = finSum n (fun j => (φ (dualVal ω₁ (Pi.single j (1 : K))) * y j
          + φ (dualVal ω₂ (Pi.single j (1 : K))) * y j)) :=
          listSum_congr (List.finRange n) _ _ (fun j => add_mul _ _ _)
    _ = finSum n (fun j => φ (dualVal ω₁ (Pi.single j (1 : K))) * y j)
        + finSum n (fun j => φ (dualVal ω₂ (Pi.single j (1 : K))) * y j) :=
          listSum_map_add (List.finRange n) _ _

-- Reference: Hörmann, arXiv:2106.03803, Def 2.5; Axler, LADR 4th ed., Ch. 3;
-- list lemmas; mathlib (`map_mul`, `mul_assoc`).
/-- The pairing is `K`-linear in the dual argument. -/
theorem pairLSmulLeft {K L : Type u} [Field K] [Field L] (φ : K →+* L) {n : ℕ}
    (c : K) (ω : FreeModDual K n) (y : FreeMod L n) :
    pairL φ (c • ω) y = φ c * pairL φ ω y := by
  unfold pairL
  calc finSum n (fun j => φ (dualVal (c • ω) (Pi.single j (1 : K))) * y j)
      = finSum n (fun j => φ (c * dualVal ω (Pi.single j (1 : K))) * y j) :=
          listSum_congr (List.finRange n) _ _ (fun j =>
            congrArg (fun t => φ t * y j) (dualValSmul c ω _))
    _ = finSum n (fun j => (φ c * φ (dualVal ω (Pi.single j (1 : K)))) * y j) :=
          listSum_congr (List.finRange n) _ _ (fun j =>
            congrArg (fun t => t * y j) (map_mul φ c _))
    _ = finSum n (fun j => φ c * (φ (dualVal ω (Pi.single j (1 : K))) * y j)) :=
          listSum_congr (List.finRange n) _ _ (fun j => mul_assoc _ _ _)
    _ = φ c * finSum n (fun j => φ (dualVal ω (Pi.single j (1 : K))) * y j) :=
          listSum_map_mul_left (List.finRange n) (φ c) _

-- Reference: Axler, LADR 4th ed., Ch. 3; list lemmas (`listSum_congr`,
-- `listSum_zero`); mathlib (`map_zero`, `zero_mul`).
/-- The pairing with the zero dual vector is zero. -/
theorem pairLZeroLeft {K L : Type u} [Field K] [Field L] (φ : K →+* L) {n : ℕ}
    (y : FreeMod L n) : pairL φ (0 : FreeModDual K n) y = 0 := by
  unfold pairL
  calc finSum n (fun j => φ (dualVal (0 : FreeModDual K n) (Pi.single j (1 : K))) * y j)
      = finSum n (fun j => φ (0 : K) * y j) :=
          listSum_congr (List.finRange n) _ _ (fun j =>
            congrArg (fun t => φ t * y j) (dualValZero _))
    _ = finSum n (fun j => (0 : L) * y j) :=
          listSum_congr (List.finRange n) _ _ (fun j =>
            congrArg (fun t => t * y j) (map_zero φ))
    _ = finSum n (fun _ => (0 : L)) :=
          listSum_congr (List.finRange n) _ _ (fun j => zero_mul _)
    _ = 0 := listSum_zero (List.finRange n)

-- Reference: Hörmann, arXiv:2106.03803, Def 2.5 (`ω(∫_M σ)` pairs the `K`-dual
-- `ω` with the base-changed vector: `ω(φ y) = φ(ω y)`); Axler, LADR 4th ed.,
-- Ch. 2–3; list lemmas and `mapListSum`; mathlib (`map_mul`).
/-- The pairing of a dual vector with a base-changed vector:
`ω(φ y) = φ (ω y)`. -/
theorem pairLBase {K L : Type u} [Field K] [Field L] (φ : K →+* L) {n : ℕ}
    (ω : FreeModDual K n) (y : FreeMod K n) :
    pairL φ ω (baseChangeOf φ y) = φ (dualVal ω y) := by
  unfold pairL baseChangeOf
  calc finSum n (fun j => φ (dualVal ω (Pi.single j (1 : K))) * φ (y j))
      = finSum n (fun j => φ (dualVal ω (Pi.single j (1 : K)) * y j)) :=
          listSum_congr (List.finRange n) _ _ (fun j => (map_mul φ _ _).symm)
    _ = φ (finSum n (fun j => dualVal ω (Pi.single j (1 : K)) * y j)) :=
          (mapListSum φ (fun j => dualVal ω (Pi.single j (1 : K)) * y j) (List.finRange n)).symm
    _ = φ (finSum n (fun j => y j * dualVal ω (Pi.single j (1 : K)))) :=
          congrArg φ (listSum_congr (List.finRange n) _ _ (fun j => mul_comm _ _))
    _ = φ (dualVal ω y) := congrArg φ (dualValEqSum ω y).symm

-- Reference: definitional peel of `pairL` — primitive definitional lemma.
/-- Unfolding of the pairing. -/
theorem pairLEq {K L : Type u} [Field K] [Field L] (φ : K →+* L) {n : ℕ}
    (ω : FreeModDual K n) (y : FreeMod L n) :
    pairL φ ω y = finSum n (fun j => φ (dualVal ω (Pi.single j (1 : K))) * y j) := rfl

-- Reference: line 764 (pairLBaseHom: `rw [baseChangeHomOfDecomp φ f x]`).
/-- Peel: unfold the base-changed hom via its decomposition. -/
theorem pairLBaseHomDecomp {K L : Type u} [Field K] [Field L] (φ : K →+* L) {m n : ℕ}
    (f : FreeModHom K m n) (ω : FreeModDual K n) (x : FreeMod L m) :
    pairL φ ω ((baseChangeHomOf φ f).toFun x)
      = pairL φ ω (finSum m (fun i => x i • baseChangeOf φ (f.toFun (Pi.single i (1 : K))))) :=
  congrArg (pairL φ ω) (baseChangeHomOfDecomp φ f x)

-- Reference: Hörmann, arXiv:2106.03803, Def 2.3 (relation (2) uses `α∨(ω)`, and
-- the pairing satisfies `ω(φ α x) = α∨(ω)(φ x)` — the load-bearing identity for
-- eval_∫); Axler, LADR 4th ed., Ch. 2–3; list lemmas; mathlib (`mul_comm`).
/-- The key pairing identity: pairing `ω` with the base change of `f x`
equals pairing the dual `f∨(ω)` with `x`. -/
theorem pairLBaseHom {K L : Type u} [Field K] [Field L] (φ : K →+* L) {m n : ℕ}
    (f : FreeModHom K m n) (ω : FreeModDual K n) (x : FreeMod L m) :
    pairL φ ω ((baseChangeHomOf φ f).toFun x) = pairL φ (dualMap f ω) x := by
  calc pairL φ ω ((baseChangeHomOf φ f).toFun x)
      = pairL φ ω (finSum m (fun i => x i • baseChangeOf φ (f.toFun (Pi.single i (1 : K))))) :=
          pairLBaseHomDecomp φ f ω x
    _ = finSum m (fun i => pairL φ ω (x i • baseChangeOf φ (f.toFun (Pi.single i (1 : K))))) :=
          pairLSumRight φ ω m (fun i => x i • baseChangeOf φ (f.toFun (Pi.single i (1 : K))))
    _ = finSum m (fun i => (x i * pairL φ ω (baseChangeOf φ (f.toFun (Pi.single i (1 : K)))))) :=
          listSum_congr (List.finRange m) _ _ (fun i => pairLSmulRight φ ω (x i) _)
    _ = finSum m (fun i => (x i * φ (dualVal ω (f.toFun (Pi.single i (1 : K)))))) :=
          listSum_congr (List.finRange m) _ _ (fun i =>
            congrArg (fun t => x i * t) (pairLBase φ ω (f.toFun (Pi.single i (1 : K)))))
    _ = finSum m (fun i => (φ (dualVal (dualMap f ω) (Pi.single i (1 : K))) * x i)) :=
          listSum_congr (List.finRange m) _ _ (fun i =>
            Eq.trans (congrArg (fun t => x i * t)
              (congrArg φ (dualValDualMap f ω (Pi.single i (1 : K))))).symm (mul_comm _ _))
    _ = pairL φ (dualMap f ω) x := (pairLEq φ (dualMap f ω) x).symm


end BoringMath.FormalPeriods
