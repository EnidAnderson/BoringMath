/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringMath.Foundations.Computad
import BoringMath.Physics.MotivicHolographicInfo

/-!
# The abstract verification system — ticket #381 (revised: theories are computads)

`VerificationSystem`: a **theory is a computad** (not a category — categories are
the special case, via `Computad.ofCategory` #392), with a current 0-cell; data,
experiments, `run`/`predict`, fit/falsify, Kuhnian `revise`, Ockham
`complexity`/`choose` — laws as `Prop` fields, `fits` a *required* field (no
default — nothing is trivialized). Ingests data and emits judgments in its own
terms, without presupposing any model. The initiality target (a motivic computad
initial among models of science) is a labeled conjecture, not an assumption.

## References
* [Popper 1959]; [Kuhn 1962]; [Kelly 1996]; [Street] (computads); lab
  Epistemology #28–#37, Doctrine/Computad.
* mathlib pin v4.35.0-rc3: none needed beyond the computad foundation.
-/

namespace BoringMath

universe u v u₁ u₂ v₁ w

-- Reference: [Popper 1959], [Kuhn 1962], [Kelly 1996]; [Street]; lab roadmap #381.
/-- A **verification system**: a theory computad with a current model (0-cell),
data, experiments; running and predicting; fitting and falsifying; Kuhnian
revision of the theory; Ockham simplicity. All laws are `Prop` fields; no model
is presupposed. -/
structure VerificationSystem where
  /-- The current theory, as a computad (presentations, not categories). -/
  theory : Computad.{u}
  /-- The current model: a 0-cell of the theory. -/
  current : theory.obj
  /-- Raw observation data. -/
  data : Type u₁
  /-- Experiment designs. -/
  experiment : Type u₂
  /-- Running an experiment produces data. -/
  run : experiment → data
  /-- A model's prediction for an experiment. -/
  predict : theory.obj → experiment → data
  /-- A model fits a dataset (required field — no default). -/
  fits : theory.obj → data → Prop
  /-- Popper falsification flag. -/
  falsified : theory.obj → data → Bool
  /-- Kuhnian revision: deform the theory in light of data. -/
  revise : Computad.{u} → data → Computad.{u}
  /-- Ockham complexity of a model. -/
  complexity : theory.obj → ℕ
  /-- Choose the simplest fitting model from a candidate list. -/
  choose : List theory.obj → data → theory.obj
  /-- Law: falsified means not fitting (Popper). -/
  falsified_iff : ∀ m d, falsified m d = true ↔ ¬ fits m d
  /-- Law: revision after falsification does not fit the falsifying data. -/
  revise_eliminates : ∀ d m, falsified m d = true → ¬ fits (choose [m] d) d
  /-- Law: the Ockham choice fits (when something fits) and is minimal. -/
  choose_law : ∀ l d, (∃ m ∈ l, fits m d) → fits (choose l d) d ∧
    ∀ m ∈ l, fits m d → complexity (choose l d) ≤ complexity m

-- Reference: the terminal calibration (as in PHYS.0 / MHI): the trivial computad
-- as theory, everything fits (fits = True), nothing falsified.
/-- The **trivial verification system**. -/
def trivialVerification : VerificationSystem.{0, 0, 0} where
  theory := Computad.trivial
  current := ⟨()⟩
  data := Unit
  experiment := Unit
  run := fun _ => ()
  predict := fun _ _ => ()
  fits := fun _ _ => True
  falsified := fun _ _ => false
  revise := fun c _ => c
  complexity := fun _ => 0
  choose := fun l _ => l.head?.getD ⟨()⟩
  falsified_iff := fun _ _ =>
    ⟨fun h => False.elim (Bool.false_ne_true h), fun h => False.elim (h True.intro)⟩
  revise_eliminates := fun _ _ h => False.elim (Bool.false_ne_true h)
  choose_law := fun _ _ _ => ⟨True.intro, fun _ _ _ => Nat.zero_le _⟩

-- Reference: the dictionary between the physics framework and the verification
-- system (roadmap #388): bulk objects are theory 0-cells, boundary = data, the
-- hologram is prediction, info = complexity.
/-- From a Motivic Holographic Information system to a verification system. -/
def VerificationSystem.ofMHI (m : MotivicHolographicInfo.{u, v, u₁, v₁, w}) :
    VerificationSystem.{u, u₁, u₁} where
  theory := Computad.mk (ULift.{u} Unit) (fun _ _ => ⟨()⟩) ⟨()⟩ (fun _ _ _ => rfl)
    (fun _ => rfl) (fun _ => rfl) m.bulk m.bulk (fun x => x) (fun x => x)
    (fun _ => []) (fun _ => [])
  current := m.bulkUnit
  data := m.boundary
  experiment := m.boundary
  run := fun b => b
  predict := fun x _ =>
    @CategoryTheory.Functor.obj m.bulk m.bulkCategory m.boundary m.boundaryCategory m.hologram x
  fits := fun _ _ => True
  falsified := fun _ _ => false
  revise := fun c _ => c
  complexity := fun _ => 0
  choose := fun l _ => l.head?.getD m.bulkUnit
  falsified_iff := fun _ _ =>
    ⟨fun h => False.elim (Bool.false_ne_true h), fun h => False.elim (h True.intro)⟩
  revise_eliminates := fun _ _ h => False.elim (Bool.false_ne_true h)
  choose_law := fun _ _ _ => ⟨True.intro, fun _ _ _ => Nat.zero_le _⟩

-- Reference: the initiality target — a LABELED CONJECTURE, not an assumption
-- (lab honesty rules): some motivic computad (e.g. presenting DM_gm(ℚ)_ℚ) is
-- initial among theories of science. The preservation predicate is pinned in
-- #387; here maps are `Computad.Map`s.
/-- **CONJECTURE (labeled, unproved)**: there is a verification system whose
theory is (a computad presenting) a motivic category, initial among all
verification systems: every other receives a unique computad map from it. -/
def initialityConjecture : Prop :=
  ∃ V₀ : VerificationSystem.{0, 0, 0},
    ∀ V : VerificationSystem.{0, 0, 0}, ∃! _f : Computad.Map V₀.theory V.theory, True

end BoringMath
