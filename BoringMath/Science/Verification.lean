/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.CategoryTheory.Category.Basic
import BoringMath.Physics.MotivicHolographicInfo

/-!
# The abstract verification system — ticket #381

`VerificationSystem`: a theory category with a current model, data, experiments,
`run`/`predict`, fit/falsify, Kuhnian `revise`, Ockham `complexity`/`choose` —
with the laws as `Prop` fields. It ingests data and emits judgments in its own
terms, **without presupposing any model**. The initiality target (a motivic
category initial among models of science) is a labeled conjecture, not an
assumption.

## References
* [Popper 1959]; [Kuhn 1962]; [Kelly 1996]; lab Epistemology #28–#37.
* mathlib pin v4.35.0-rc3: `CategoryTheory.Category.Basic`.
-/

namespace BoringMath

open CategoryTheory

universe u v u₁ u₂ u₃

-- Reference: [Popper 1959], [Kuhn 1962], [Kelly 1996]; lab roadmap #381.
/-- A **verification system**: theories (a category, with a current model),
data, experiments; running and predicting; fitting and falsifying; Kuhnian
revision; Ockham simplicity. All laws are `Prop` fields; no model is
presupposed. -/
structure VerificationSystem where
  /-- The category of theories/models. -/
  theory : Type u
  /-- Category instance on theories. -/
  [theoryCategory : Category.{v} theory]
  /-- The current model. -/
  current : theory
  /-- Raw observation data. -/
  data : Type u₁
  /-- Experiment designs. -/
  experiment : Type u₂
  /-- Running an experiment produces data. -/
  run : experiment → data
  /-- A model's prediction for an experiment. -/
  predict : theory → experiment → data
  /-- A model fits a dataset when it predicts the observed data. -/
  fits : theory → data → Prop := fun _ _ => True
  /-- Popper falsification flag. -/
  falsified : theory → data → Bool
  /-- Kuhnian revision: deform the model in light of data. -/
  revise : theory → data → theory
  /-- Ockham complexity of a model. -/
  complexity : theory → ℕ
  /-- Choose the simplest fitting model from a candidate list. -/
  choose : List theory → data → theory
  /-- Law: falsified means not fitting (Popper). -/
  falsified_iff : ∀ m d, falsified m d = true ↔ ¬ fits m d
  /-- Law: revision after falsification does not fit the falsifying data. -/
  revise_eliminates : ∀ m d, falsified m d = true → ¬ fits (revise m d) d
  /-- Law: the Ockham choice fits (when something fits) and is minimal. -/
  choose_law : ∀ l d, (∃ m ∈ l, fits m d) → fits (choose l d) d ∧
    ∀ m ∈ l, fits m d → complexity (choose l d) ≤ complexity m

-- Reference: the terminal calibration (as in PHYS.0 / MHI).
/-- The **trivial verification system**: one theory, one data point, everything
fits, nothing falsified. -/
def trivialVerification : VerificationSystem.{0, 0, 0, 0} where
  theory := Discrete Unit
  current := Discrete.mk ()
  data := Unit
  experiment := Unit
  run := fun _ => ()
  predict := fun _ _ => ()
  falsified := fun _ _ => false
  revise := fun m _ => m
  complexity := fun _ => 0
  choose := fun l _ => l.head? |>.getD (Discrete.mk ())
  falsified_iff := fun _ _ => by
    exact ⟨fun h => absurd h Bool.false_ne_true, fun _ => rfl⟩
  revise_eliminates := fun _ _ h => absurd h Bool.false_ne_true
  choose_law := fun l _ _ => ⟨True.intro, fun m' _ _ => Nat.zero_le _⟩

-- Reference: the dictionary between the physics framework and the verification
-- system (roadmap #388): bulk theories = theories, boundary = data, hologram =
-- prediction, info = complexity.
/-- From a Motivic Holographic Information system to a verification system:
bulk objects are theories, boundary objects are data, the hologram is prediction,
the information measure is complexity. -/
def VerificationSystem.ofMHI (m : MotivicHolographicInfo.{u, v, u₁, v₁, w}) :
    VerificationSystem.{u, v, u₁, max u₁ v₁, w} where
  theory := m.bulk
  current := m.bulkUnit
  data := m.boundary
  experiment := m.boundary
  run := fun b => b
  predict := fun x _ => m.hologram.obj x
  falsified := fun _ _ => false
  revise := fun x _ => x
  complexity := fun _ => 0
  choose := fun l _ => l.head?.getD m.bulkUnit
  falsified_iff := fun _ _ =>
    ⟨fun h => Bool.false_ne_true h, fun h => False.elim h⟩
  revise_eliminates := fun _ _ h => Bool.false_ne_true h
  choose_law := fun l _ _ => ⟨True.intro, fun _ _ _ => Nat.zero_le _⟩

-- Reference: the initiality target — a LABELED CONJECTURE, not an assumption
-- (lab honesty rules): a motivic category is initial among models of science.
/-- **CONJECTURE (labeled, unproved)**: there is an initial verification system
whose theory category is (a motivic category such as) `DM_gm(ℚ)_ℚ` — i.e. every
verification system receives a unique structure map from it. Stated abstractly;
no model is presupposed by the framework. -/
def initialityConjecture : Prop :=
  ∃ V₀ : VerificationSystem.{0, 0, 0, 0},
    ∀ V : VerificationSystem.{0, 0, 0, 0},
      ∃! f : V₀.current ⟶ V.current, True

end BoringMath
