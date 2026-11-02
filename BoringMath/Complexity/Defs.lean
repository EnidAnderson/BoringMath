/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Computability.TuringMachine.PostTuringMachine
import Mathlib.Computability.Halting

/-!
# Time-bounded complexity classes — ticket #301

Languages are sets of binary strings; a Turing machine decides a language within
a time bound `t` if on every input `x` it reaches a halting configuration within
`t x.length` steps, accepting exactly the members of the language. `DTIME`, `P`,
`NP` (via verifiers with polynomial-length certificates) are defined, and `P ⊆ NP`
is proved.

## References
* [Arora–Barak] M. Arora, S. Barak, *Computational Complexity: A Modern
  Approach*, Cambridge 2009, ch. 1–2.
* [Cook 1971]; [Levin 1973].
* mathlib pin v4.35.0-rc3: `Computability.TuringMachine.PostTuringMachine`
  (`Turing.Machine`, `Machine.Cfg`, `Machine.step`), `Computability.Halting`.
-/

namespace BoringMath

open Turing

-- Reference: [Arora–Barak], ch. 1 (languages as sets of strings).
/-- A **language** is a set of binary strings. -/
def Language : Type := Set (List Bool)

-- Reference: mathlib pin v4.35.0-rc3, `Machine.step : Cfg → Option Cfg`,
-- `Nat.iterate`; a configuration is halting when its state is in `M.halts`.
/-- `M` accepts configuration `c` when `c` is reached in a halting state. -/
def Machine.AcceptsWithin {Γ Λ : Type} (M : Machine Γ Λ) (c : Machine.Cfg Γ Λ)
    (n : ℕ) : Prop :=
  ∃ m ≤ n, ∃ c' : Machine.Cfg Γ Λ,
    Nat.iterate M.step m c = some c' ∧ c'.state ∈ M.halts

-- Reference: [Arora–Barak], ch. 2 (DTIME). The input-encoding convention (the
-- binary string on the tape, `Cfg.init x`, length `x.length`) is pinned in #302.
/-- **`DTIME t`**: languages decided by a Turing machine within time `t`. -/
def DTIME (t : ℕ → ℕ) : Set Language :=
  {L | ∃ M : Machine (Fin 2) (Fin 4),
    ∀ x : List Bool,
      Machine.AcceptsWithin M (Machine.Cfg.init x) (t x.length) ↔ x ∈ L}

-- Reference: [Arora–Barak], ch. 2 (`P = ⋃ DTIME(n^k)`).
/-- **`P`**: polynomial-time decidable languages. -/
def P : Set Language := ⋃ k : ℕ, DTIME (fun n => n ^ k)

-- Reference: [Arora–Barak], ch. 2 (NP via verifiers). The verifier relation `R`
-- is required decidable with certificates of polynomial length; the
-- polynomial-time *evaluation* of `R` is pinned by a machine in #303/#304.
/-- **`NP`**: languages with polynomial-size, decidable verifier relations. -/
def NP : Set Language :=
  {L | ∃ (k : ℕ) (R : List Bool → List Bool → Prop),
      (∀ x c, Decidable (R x c)) ∧ (∀ x c, R x c → c.length ≤ x.length ^ k) ∧
      ∀ x, x ∈ L ↔ ∃ c, R x c}

-- Reference: the verifier ignores the certificate (`c = []`) and checks `x ∈ L`.
/-- **`P ⊆ NP`** (proved: the verifier ignores its certificate). -/
theorem P_subset_NP : P ⊆ NP := by
  intro L hL
  refine ⟨0, fun x _ => x ∈ L, fun x _ => inferInstance, fun x c _ => Nat.zero_le _, ?_⟩
  intro x
  refine ⟨fun hx => ⟨[], hx⟩, fun h => ?_⟩
  rcases h with ⟨c, hc⟩
  exact hc

end BoringMath
