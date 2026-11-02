/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Init
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Fin.Basic
import BoringMath.FormalPeriods.RowReduction.RowOps
import BoringMath.FormalPeriods.RowReduction.PivotSearch

/-!
# The normal-form predicates (P.2.1, part 4)

Part 4 of `BoringMath.FormalPeriods.RowReduction`: zero rows, leading
columns, the reduced row-echelon predicate `IsRref`, and the loop
invariant `RrefState` with its initial and exit facts.
-/

universe u

namespace BoringMath

variable {K : Type u} [Field K] {m n : ℕ}
variable [DecidableEq K]

/-! ## The normal-form predicates -/

-- Reference: Mines–Richman–Ruitenburg 2008, Pt. II Ch. 6.
/-- Row `a` of `A` is zero. -/
def matRowZero (A : FreeMatrix K m n) (a : Fin m) : Prop := ∀ c : Fin n, A a c = 0

-- Reference: Mines–Richman–Ruitenburg 2008, Pt. II Ch. 6 (leading entry).
/-- The leading (first nonzero) column of row `a`; `n` if the row is zero. -/
def matLeadingCol (A : FreeMatrix K m n) (a : Fin m) : ℕ :=
  match findPivotRow (fun c => if A a c ≠ 0 then true else false) n 0 with
  | some c => c.val
  | none => n

-- Reference: Mines–Richman–Ruitenburg 2008, Pt. II Ch. 6.
/-- A zero row has leading column `n` (past the last column). -/
theorem matLeadingCol_eq_of_rowZero (A : FreeMatrix K m n) (a : Fin m) (h : matRowZero A a) :
    matLeadingCol A a = n := by
  have hnone : findPivotRow (fun c => if A a c ≠ 0 then true else false) n 0 = none :=
    findPivotRow_eq_none_of (fun c => ite_eq_right (fun hne => hne (h c)))
  -- unfold matLeadingCol: explicit constant; Former rw [hnone]: congrArg with
  -- the named rule `hnone`; the unique `findPivotRow …` scrutinee is abstracted
  -- by the match motive, and `match none …` reduces to `n` definitionally.
  unfold matLeadingCol
  exact congrArg (fun v => match v with | some c' => c'.val | none => n) hnone

-- Reference: Mines–Richman–Ruitenburg 2008, Pt. II Ch. 6 (reduced
-- row-echelon form over a discrete field).
/-- `A` is in reduced row-echelon form: zero rows sit at the bottom; every
nonzero row has leading entry `1`; leading columns strictly increase down
the matrix; each pivot column is zero in every other row. -/
def IsRref (A : FreeMatrix K m n) : Prop :=
  (∀ a b : Fin m, a < b → matRowZero A a → matRowZero A b) ∧
  (∀ a : Fin m, ∀ c : Fin n, matLeadingCol A a = c.val → A a c = 1) ∧
  (∀ a b : Fin m, a < b → ¬ matRowZero A b → matLeadingCol A a < matLeadingCol A b) ∧
  (∀ a b : Fin m, a ≠ b → ∀ c : Fin n, matLeadingCol A a = c.val → A b c = 0)

-- Reference: the loop invariant of Mines–Richman–Ruitenburg 2008, Pt. II
-- Ch. 6: at state `(r, j, A)` the columns `< j` are already reduced, carried
-- by the rows `< r`; the rows `≥ r` vanish on columns `< j`.
/-- The invariant of the elimination loop at state `(r, j, A)`. -/
def RrefState (r j : ℕ) (A : FreeMatrix K m n) : Prop :=
  (∀ a : Fin m, r ≤ a.val → ∀ c : Fin n, c.val < j → A a c = 0) ∧
  (∀ a : Fin m, a.val < r → ¬ matRowZero A a) ∧
  (∀ a : Fin m, a.val < r → matLeadingCol A a < j) ∧
  (∀ a : Fin m, a.val < r → ∀ c : Fin n, matLeadingCol A a = c.val → A a c = 1) ∧
  (∀ a b : Fin m, a.val < r → b.val < r → a < b → matLeadingCol A a < matLeadingCol A b) ∧
  (∀ a : Fin m, a.val < r → ∀ b : Fin m, a ≠ b → ∀ c : Fin n,
    matLeadingCol A a = c.val → A b c = 0)

-- Reference: the initial state of the loop is vacuous.
/-- The invariant holds initially: no rows below `0`, no columns left of `0`. -/
theorem rrefState_zero (A : FreeMatrix K m n) : RrefState 0 0 A :=
  ⟨fun _ _ c hc => absurd hc (Nat.not_lt_zero c.val),
   fun a ha => absurd ha (Nat.not_lt_zero a.val),
   fun a ha => absurd ha (Nat.not_lt_zero a.val),
   fun a ha _ _ => absurd ha (Nat.not_lt_zero a.val),
   fun a _ ha _ _ => absurd ha (Nat.not_lt_zero a.val),
   fun a ha _ _ _ => absurd ha (Nat.not_lt_zero a.val)⟩

-- Reference: Mines–Richman–Ruitenburg 2008, Pt. II Ch. 6 (the exit case:
-- once all columns are processed, the invariant is exactly `IsRref`).
/-- When all columns have been processed (`n ≤ j`), the loop invariant is
exactly the normal-form predicate. -/
theorem rrefState_isRref_of_done {r j : ℕ} {A : FreeMatrix K m n} (h : n ≤ j)
    (hs : RrefState r j A) :
    IsRref A := by
  rcases hs with ⟨hR1, hR2, hR3, hR4, hR5, hR6⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b hab hza c
    rcases Nat.lt_or_ge a.val r with ha | ha
    · exact absurd hza (hR2 a ha)
    · exact hR1 b (Nat.le_trans ha (Nat.le_of_lt hab)) c
        (Nat.lt_of_lt_of_le c.isLt h)
  · intro a c hlc
    rcases Nat.lt_or_ge a.val r with ha | ha
    · exact hR4 a ha c hlc
    · have hza : matRowZero A a :=
        fun c => hR1 a ha c (Nat.lt_of_lt_of_le c.isLt h)
      have hn := matLeadingCol_eq_of_rowZero A a hza
      -- Former rw [hn] at hlc: Eq.subst with the named rule `hn` acting on
      -- `hlc`; fully instantiated; the unique `matLeadingCol A a` is the LHS of
      -- `hlc` (motive `fun v => v = c.val`); gives `n = c.val`.
      have hlc' : n = c.val := Eq.subst (motive := fun v => v = c.val) hn hlc
      exact absurd c.isLt (Nat.not_lt.mpr (Nat.le_of_eq hlc'))
  · intro a b hab hnb
    rcases Nat.lt_or_ge b.val r with hb | hb
    · exact hR5 a b (Nat.lt_trans hab hb) hb hab
    · exact absurd (fun c => hR1 b hb c (Nat.lt_of_lt_of_le c.isLt h)) hnb
  · intro a b hne c hlc
    rcases Nat.lt_or_ge a.val r with ha | ha
    · exact hR6 a ha b hne c hlc
    · have hza : matRowZero A a :=
        fun c => hR1 a ha c (Nat.lt_of_lt_of_le c.isLt h)
      have hn := matLeadingCol_eq_of_rowZero A a hza
      -- Former rw [hn] at hlc: Eq.subst with the named rule `hn` acting on
      -- `hlc`; fully instantiated; the unique `matLeadingCol A a` is the LHS of
      -- `hlc` (motive `fun v => v = c.val`); gives `n = c.val`.
      have hlc' : n = c.val := Eq.subst (motive := fun v => v = c.val) hn hlc
      exact absurd c.isLt (Nat.not_lt.mpr (Nat.le_of_eq hlc'))

