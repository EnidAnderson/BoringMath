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

/-!
# Base change along a ring homomorphism

`algBL B K L` (the composite `B → K → L`), base change of vectors
(`baseChangeOf`) and of homs in the standard bases (`baseChangeHomOf`), with
the commutation `φ (f x) = (φ f)(φ x)`.  Split out of
`BoringMath.FormalPeriods.FormalPeriods`.
-/

universe u

namespace BoringMath.FormalPeriods

variable {B K L : Type u} [Field B] [Field K] [Field L] [Algebra B K] [Algebra K L]
variable {m n : ℕ}

/-! ## Base change along a ring homomorphism -/

-- Reference: Hörmann, arXiv:2106.03803, 2.2 (`∫` is a natural isomorphism after
-- base change to `ℂ`; here to the abstract extension `L` of `K`, with `B → L`
-- the composite `B → K → L`); mathlib (`RingHom.comp`).
/-- The composite ring homomorphism `B → K → L` (Hörmann's `ℚ → K → ℂ`). -/
def algBL (B K L : Type u) [Field B] [Field K] [Field L] [Algebra B K] [Algebra K L] :
    B →+* L :=
  (algebraMap K L).comp (algebraMap B K)

-- Reference: Dummit–Foote, §10.4 / base change of modules (extension of
-- scalars: `x ↦ φ ∘ x` on coordinates); Axler, LADR 4th ed., Ch. 2.
/-- Base change of a basis-carrying vector along `φ : R →+* L`:
coordinates are mapped by `φ` (the basis is unchanged: `eᵢ ↦ eᵢ ⊗ 1`). -/
def baseChangeOf {R L : Type u} [Field R] [Field L] (φ : R →+* L) {m : ℕ}
    (x : FreeMod R m) : FreeMod L m := fun i => φ (x i)

-- Reference: line 463 (baseChangeOfAdd: `rw [Pi.add_apply, map_add, Pi.add_apply]`).
/-- Peel: base change is additive, pointwise. -/
theorem baseChangeOfAddPoint {R L : Type u} [Field R] [Field L] (φ : R →+* L) {m : ℕ}
    (x y : FreeMod R m) (i : Fin m) :
    (baseChangeOf φ (x + y)) i = (baseChangeOf φ x + baseChangeOf φ y) i :=
  Eq.trans (Eq.trans (congrArg (fun w : R => φ w) (Pi.add_apply x y i))
      (map_add φ (x i) (y i)))
    (Pi.add_apply (baseChangeOf φ x) (baseChangeOf φ y) i).symm

-- Reference: line 473 (baseChangeOfSmul: `rw [Pi.smul_apply, smul_eq_mul, map_mul, ...]`).
/-- Peel: base change is linear, pointwise. -/
theorem baseChangeOfSmulPoint {R L : Type u} [Field R] [Field L] (φ : R →+* L) {m : ℕ}
    (c : R) (x : FreeMod R m) (i : Fin m) :
    (baseChangeOf φ (c • x)) i = (φ c • baseChangeOf φ x) i :=
  Eq.trans (congrArg (fun w : R => φ w) (Pi.smul_apply c x i))
    (Eq.trans (congrArg φ (smul_eq_mul c (x i)))
      (Eq.trans (map_mul φ c (x i))
        (Eq.trans (Pi.smul_apply (φ c) (baseChangeOf φ x) i)
          (smul_eq_mul (φ c) ((baseChangeOf φ x) i))).symm))

-- Reference: line 482 (baseChangeOfZero: `rw [Pi.zero_apply, map_zero, Pi.zero_apply]`).
/-- Peel: base change kills zero, pointwise. -/
theorem baseChangeOfZeroPoint {R L : Type u} [Field R] [Field L] (φ : R →+* L) {m : ℕ}
    (i : Fin m) : (baseChangeOf φ (0 : FreeMod R m)) i = ((0 : FreeMod L m)) i :=
  Eq.trans (congrArg (fun w : R => φ w) (Pi.zero_apply i))
    (Eq.trans (map_zero φ) (Pi.zero_apply (M := fun _ => L) i).symm)

-- Reference: base change is a ring-homomorphism on coordinates; mathlib
-- (`Pi.add_apply`, `map_add`).
/-- Base change is additive. -/
theorem baseChangeOfAdd {R L : Type u} [Field R] [Field L] (φ : R →+* L) {m : ℕ}
    (x y : FreeMod R m) : baseChangeOf φ (x + y) = baseChangeOf φ x + baseChangeOf φ y := by
  funext i
  exact baseChangeOfAddPoint φ x y i

-- Reference: base change is a ring-homomorphism on coordinates; mathlib
-- (`Pi.smul_apply`, `smul_eq_mul`, `map_mul`).
/-- Base change is `R`-linear: `φ (c • x) = φ c • φ x`. -/
theorem baseChangeOfSmul {R L : Type u} [Field R] [Field L] (φ : R →+* L) {m : ℕ} (c : R)
    (x : FreeMod R m) : baseChangeOf φ (c • x) = φ c • baseChangeOf φ x := by
  funext i
  exact baseChangeOfSmulPoint φ c x i

-- Reference: base change kills zero; mathlib (`Pi.zero_apply`, `map_zero`).
/-- Base change sends `0` to `0`. -/
theorem baseChangeOfZero {R L : Type u} [Field R] [Field L] (φ : R →+* L) {m : ℕ} :
    baseChangeOf φ (0 : FreeMod R m) = (0 : FreeMod L m) := by
  funext i
  exact baseChangeOfZeroPoint φ i

-- Reference: Axler, LADR 4th ed., Ch. 3 (a linear map in bases is its matrix
-- `x ↦ ∑ i, x i • f eᵢ`, with entries mapped by `φ`).
/-- The base change of a hom, as a function on coordinates:
`(φ f)(x)ⱼ = ∑ i, x i * φ ((f eᵢ) j)`. -/
def baseChangeHomOfFun {R L : Type u} [Field R] [Field L] (φ : R →+* L) {m n : ℕ}
    (f : FreeModHom R m n) (x : FreeMod L m) (j : Fin n) : L :=
  finSum m (fun i => x i * φ ((f.toFun (Pi.single i (1 : R))) j))

-- Reference: Axler, LADR 4th ed., Ch. 3; list lemmas (`listSum_congr`,
-- `listSum_map_add`, `Pi.add_apply`, `add_mul`).
/-- The base-changed hom is additive in the vector argument. -/
theorem baseChangeHomOfFunAdd {R L : Type u} [Field R] [Field L] (φ : R →+* L) {m n : ℕ}
    (f : FreeModHom R m n) (x y : FreeMod L m) (j : Fin n) :
    baseChangeHomOfFun φ f (x + y) j
      = baseChangeHomOfFun φ f x j + baseChangeHomOfFun φ f y j := by
  unfold baseChangeHomOfFun
  calc finSum m (fun i => (x + y) i * φ ((f.toFun (Pi.single i (1 : R))) j))
      = finSum m (fun i => (x i + y i) * φ ((f.toFun (Pi.single i (1 : R))) j)) :=
          listSum_congr (List.finRange m) _ _ (fun i =>
            congrArg (fun t => t * φ ((f.toFun (Pi.single i (1 : R))) j)) (Pi.add_apply x y i))
    _ = finSum m (fun i => (x i * φ ((f.toFun (Pi.single i (1 : R))) j)
          + y i * φ ((f.toFun (Pi.single i (1 : R))) j))) :=
          listSum_congr (List.finRange m) _ _ (fun i => add_mul (x i) (y i) _)
    _ = finSum m (fun i => x i * φ ((f.toFun (Pi.single i (1 : R))) j))
        + finSum m (fun i => y i * φ ((f.toFun (Pi.single i (1 : R))) j)) :=
          listSum_map_add (List.finRange m) _ _

-- Reference: Axler, LADR 4th ed., Ch. 3; list lemmas (`listSum_congr`,
-- `listSum_map_mul_left`, `Pi.smul_apply`, `smul_eq_mul`, `mul_assoc`).
/-- The base-changed hom is linear in the vector argument. -/
theorem baseChangeHomOfFunSmul {R L : Type u} [Field R] [Field L] (φ : R →+* L) {m n : ℕ}
    (f : FreeModHom R m n) (c : L) (x : FreeMod L m) (j : Fin n) :
    baseChangeHomOfFun φ f (c • x) j = c • baseChangeHomOfFun φ f x j := by
  unfold baseChangeHomOfFun
  calc finSum m (fun i => (c • x) i * φ ((f.toFun (Pi.single i (1 : R))) j))
      = finSum m (fun i => (c * x i) * φ ((f.toFun (Pi.single i (1 : R))) j)) :=
          listSum_congr (List.finRange m) _ _ (fun i =>
            congrArg (fun t => t * φ ((f.toFun (Pi.single i (1 : R))) j))
              (Eq.trans (Pi.smul_apply c x i) (smul_eq_mul c (x i))))
    _ = finSum m (fun i => c * (x i * φ ((f.toFun (Pi.single i (1 : R))) j))) :=
          listSum_congr (List.finRange m) _ _ (fun i => mul_assoc c (x i) _)
    _ = c * finSum m (fun i => x i * φ ((f.toFun (Pi.single i (1 : R))) j)) :=
          listSum_map_mul_left (List.finRange m) c _

-- Reference: base change of a linear map in bases (the matrix entries are
-- mapped by `φ`); Dummit–Foote, §10.4 (extension of scalars of a linear map).
/-- Base change of a morphism of basis-carrying free modules along
`φ : R →+* L`: in the standard bases, the matrix entries are mapped by `φ`. -/
def baseChangeHomOf {R L : Type u} [Field R] [Field L] (φ : R →+* L) {m n : ℕ}
    (f : FreeModHom R m n) : FreeModHom L m n where
  toFun := fun x j => baseChangeHomOfFun φ f x j
  map_add' := fun x y => by
    funext j
    exact baseChangeHomOfFunAdd φ f x y j
  map_smul' := fun c x => by
    funext j
    exact baseChangeHomOfFunSmul φ f c x j

-- Reference: definitional peel of `baseChangeHomOf` — primitive definitional lemma.
/-- Pointwise unfolding of the base change of a hom. -/
theorem baseChangeHomOfToFunApply {R L : Type u} [Field R] [Field L] (φ : R →+* L) {m n : ℕ}
    (f : FreeModHom R m n) (x : FreeMod L m) (j : Fin n) :
    (baseChangeHomOf φ f).toFun x j = baseChangeHomOfFun φ f x j := rfl

-- Reference: definitional peel of `baseChangeHomOfFun` — primitive definitional lemma.
/-- Unfolding of the base-changed hom on coordinates. -/
theorem baseChangeHomOfFunEq {R L : Type u} [Field R] [Field L] (φ : R →+* L) {m n : ℕ}
    (f : FreeModHom R m n) (x : FreeMod L m) (j : Fin n) :
    baseChangeHomOfFun φ f x j
      = finSum m (fun i => x i * φ ((f.toFun (Pi.single i (1 : R))) j)) := rfl

-- Reference: Axler, LADR 4th ed., Ch. 2–3 (matrix expansion
-- `f x = ∑ i, x i • f eᵢ`); list lemmas (`listSum_congr`, `listSum_apply`,
-- `Pi.smul_apply`, `smul_eq_mul`).
/-- Base change of a hom decomposes: `(φ f)(x) = ∑ i, x i • φ (f eᵢ)`. -/
theorem baseChangeHomOfDecomp {R L : Type u} [Field R] [Field L] (φ : R →+* L) {m n : ℕ}
    (f : FreeModHom R m n) (x : FreeMod L m) :
    (baseChangeHomOf φ f).toFun x
      = finSum m (fun i => x i • baseChangeOf φ (f.toFun (Pi.single i (1 : R)))) := by
  funext j
  calc (baseChangeHomOf φ f).toFun x j
      = baseChangeHomOfFun φ f x j := baseChangeHomOfToFunApply φ f x j
    _ = finSum m (fun i => x i * φ ((f.toFun (Pi.single i (1 : R))) j)) :=
          baseChangeHomOfFunEq φ f x j
    _ = finSum m (fun i => (x i • baseChangeOf φ (f.toFun (Pi.single i (1 : R)))) j) :=
          listSum_congr (List.finRange m) _ _ (fun i =>
            (Eq.trans (Pi.smul_apply (x i) (baseChangeOf φ (f.toFun (Pi.single i (1 : R)))) j)
              (smul_eq_mul (x i) ((baseChangeOf φ (f.toFun (Pi.single i (1 : R)))) j))).symm)
    _ = (finSum m (fun i => x i • baseChangeOf φ (f.toFun (Pi.single i (1 : R))))) j :=
          (listSum_apply (List.finRange m)
            (fun i => x i • baseChangeOf φ (f.toFun (Pi.single i (1 : R)))) j).symm

-- Reference: Axler, LADR 4th ed., Ch. 2–3 (matrix times vector:
-- `φ (f x) = (φ f)(φ x)` — base change commutes with linear maps);
-- Hörmann, arXiv:2106.03803, 2.2 (naturality of `∫` after base change); list
-- lemmas and `mapListSum`.
/-- Base change of a hom applied to a base-changed vector equals the base
change of the value: `φ (f x) = (φ f)(φ x)`. -/
theorem baseChangeHomOfApply {R L : Type u} [Field R] [Field L] (φ : R →+* L) {m n : ℕ}
    (f : FreeModHom R m n) (x : FreeMod R m) :
    baseChangeOf φ (f.toFun x) = (baseChangeHomOf φ f).toFun (baseChangeOf φ x) := by
  funext j
  have h1 : f.toFun x = finSum m (fun i => x i • f.toFun (Pi.single i (1 : R))) :=
    Eq.trans (congrArg f.toFun (freeModEqSumSingle x))
      (Eq.trans (freeModHomMapSum f m (fun i => x i • Pi.single i (1 : R)))
        (listSum_congr (List.finRange m) _ _
          (fun i => f.map_smul' (x i) (Pi.single i (1 : R)))))
  calc φ ((f.toFun x) j)
      = φ ((finSum m (fun i => x i • f.toFun (Pi.single i (1 : R)))) j) :=
          congrArg (fun v : FreeMod R n => φ (v j)) h1
    _ = φ (finSum m (fun i => (x i • f.toFun (Pi.single i (1 : R))) j)) :=
          congrArg φ (listSum_apply (List.finRange m)
            (fun i => x i • f.toFun (Pi.single i (1 : R))) j)
    _ = finSum m (fun i => φ ((x i • f.toFun (Pi.single i (1 : R))) j)) :=
          mapListSum φ (fun i => (x i • f.toFun (Pi.single i (1 : R))) j) (List.finRange m)
    _ = finSum m (fun i => φ (x i * (f.toFun (Pi.single i (1 : R))) j)) :=
          listSum_congr (List.finRange m) _ _ (fun i => congrArg φ
            (Eq.trans (Pi.smul_apply (x i) (f.toFun (Pi.single i (1 : R))) j)
              (smul_eq_mul (x i) ((f.toFun (Pi.single i (1 : R))) j))))
    _ = finSum m (fun i => (φ (x i) * φ ((f.toFun (Pi.single i (1 : R))) j))) :=
          listSum_congr (List.finRange m) _ _ (fun i => map_mul φ (x i) _)
    _ = finSum m (fun i => (baseChangeOf φ x) i * φ ((f.toFun (Pi.single i (1 : R))) j)) :=
          Eq.refl _


end BoringMath.FormalPeriods
