/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Init
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Field.Rat
import Mathlib.Data.Fin.Basic
import BoringMath.FormalPeriods.AxiomLint

/-!
# Row reduction: Gaussian elimination over a discrete field

Ticket P.2.1 (leaf of P.2, issues #94/#108). An explicit, total
Gaussian-elimination procedure on matrices in `FreeMod` coordinates
(`FreeMatrix K m n = Fin m → Fin n → K`), producing the reduced
row-echelon normal form (RREF). Termination is by an explicit decreasing
measure (`colMeasure`): each recursive call consumes exactly one column,
so `n + 1` units of fuel suffice (`rrefAux` is structurally recursive on
the fuel). Correctness lemmas state that the output satisfies the
normal-form predicates (`IsRref`: zero rows at the bottom, pivot entries
`1`, strictly increasing pivot columns, pivot columns cleared elsewhere).

Everything on the core path is computable and choice-free (verified by
`#lint_axioms` at the end of this file), so the procedure is
`decide`-evaluable in the computational sense — the *term* computes —
demonstrated by `#eval` on a concrete 3×3 matrix over `ℚ`
(the `decide` *tactic* is banned by style; the computation itself is not).

Program context: this elimination layer supplies the decidability behind
the finite-dimensional quotient computations in Hörmann's formal-period
filtration (Def. 3.1, Remark 3.3).

Note on inversion: at the pin v4.35.0-rc3 the `⁻¹` instance path from
`Field K` (`CommGroupWithZero.toDivisionCommMonoid`) reaches
`Classical.choice` (verified by `#print axioms`), so the elimination takes
the inversion as explicit data: `invK : K → K` with its defining property
`hinv : ∀ a ≠ 0, invK a * a = 1` (computability discipline, STYLE §2.3).
For `K = ℚ` the smoke test uses `fun a => a⁻¹`.

## References
* R. Mines, F. Richman, W. Ruitenburg, *A Course in Constructive Algebra*,
  Springer Universitext, 2008, Pt. II Ch. 6 "Matrices and vector spaces"
  (and Pt. V Ch. 1 "Diagonalizing matrices") — constructive Gaussian
  elimination over discrete fields; TOC verified via SpringerLink.
* F. Hörmann, *A note on formal periods*, arXiv:2106.03803, Def. 3.1 and
  Remark 3.3 (verified against the arXiv HTML): `P^k(M)` is the quotient of
  `H_B(M) ⊗_ℚ H_dR(M)^∨` by the relations `∑ σᵢ ⊗ ωᵢ` coming from exact
  sequences `0 → N' → M^m → N → 0` with `m ≤ k`, and `P^k(M) = P^∞(M)` for
  `k = dim H_B(M)` — the stabilization this elimination layer computes.
-/

universe u

namespace BoringMath

variable {K : Type u} [Field K] {m n : ℕ}
variable (invK : K → K)

/-! ## Matrices and elementary row operations -/

-- Reference: Mines–Richman–Ruitenburg 2008, Pt. II Ch. 6 (a matrix over a
-- discrete field is an array of rows; TOC verified via SpringerLink).
/-- A matrix in `FreeMod` coordinates: the array form of a linear map
`FreeMod K n → FreeMod K m` in the standard basis; `A i` is row `i`. -/
abbrev FreeMatrix (K : Type u) [Field K] (m n : ℕ) := Fin m → Fin n → K

-- Reference: Mines–Richman–Ruitenburg 2008, Pt. II Ch. 6 (elementary row
-- operations over a discrete field).
/-- Swap rows `r` and `i` of `A`. -/
def matRowSwap (A : FreeMatrix K m n) (r i : Fin m) : FreeMatrix K m n :=
  fun a c => if a = r then A i c else if a = i then A r c else A a c

-- Reference: Mines–Richman–Ruitenburg 2008, Pt. II Ch. 6.
/-- Scale row `r` of `A` by the scalar `s`. -/
def matRowScale (A : FreeMatrix K m n) (r : Fin m) (s : K) : FreeMatrix K m n :=
  fun a c => if a = r then s * A a c else A a c

-- Reference: Mines–Richman–Ruitenburg 2008, Pt. II Ch. 6.
/-- Subtract `A a j` times the pivot row `r` from row `a`: the elementary
elimination step at the pivot `(r, j)`. -/
def matRowElim (A : FreeMatrix K m n) (r : Fin m) (j : Fin n) : FreeMatrix K m n :=
  fun a c => if a = r then A a c else A a c - A a j * A r c

-- Reference: definitional peel of `matRowSwap` (eta/ite reduction).
/-- Pointwise unfolding of `matRowSwap`. -/
theorem matRowSwap_apply (A : FreeMatrix K m n) (r i a : Fin m) (c : Fin n) :
    matRowSwap A r i a c = (if a = r then A i c else if a = i then A r c else A a c) :=
  rfl

-- Reference: definitional peel of `matRowSwap_apply` at `a = r`.
/-- `matRowSwap` sends the row `r` to the old row `i`. -/
theorem matRowSwap_left (A : FreeMatrix K m n) (r i : Fin m) (c : Fin n) :
    matRowSwap A r i r c = A i c :=
  ite_eq_left rfl

-- Reference: definitional peel of `matRowSwap_apply` at `a = i`, `i ≠ r`.
/-- `matRowSwap` sends the row `i` to the old row `r` (when `i ≠ r`). -/
theorem matRowSwap_right (A : FreeMatrix K m n) (r i : Fin m) (h : i ≠ r) (c : Fin n) :
    matRowSwap A r i i c = A r c :=
  (ite_eq_right h).trans (ite_eq_left rfl)

-- Reference: definitional peel of `matRowSwap_apply` at `a ∉ {r, i}`.
/-- `matRowSwap` fixes every other row. -/
theorem matRowSwap_other (A : FreeMatrix K m n) (r i a : Fin m) (hr : a ≠ r) (hi : a ≠ i)
    (c : Fin n) :
    matRowSwap A r i a c = A a c :=
  (ite_eq_right hr).trans (ite_eq_right hi)

-- Reference: definitional peel of `matRowSwap_apply` at `i = r`.
/-- Swapping a row with itself is the identity. -/
theorem matRowSwap_diag (A : FreeMatrix K m n) (r a : Fin m) (c : Fin n) :
    matRowSwap A r r a c = A a c := by
  cases (inferInstance : Decidable (a = r)) with
  | isTrue h =>
      -- rw [h]: rule `a = r`, fully instantiated; rewrites the unique `a` in the goal.
      rw [h]
      exact ite_eq_left rfl
  | isFalse h => exact (ite_eq_right h).trans (ite_eq_right h)

-- Reference: definitional peel of `matRowScale` at `a = r`.
/-- `matRowScale` scales the row `r`. -/
theorem matRowScale_self (A : FreeMatrix K m n) (r : Fin m) (s : K) (c : Fin n) :
    matRowScale A r s r c = s * A r c :=
  ite_eq_left rfl

-- Reference: definitional peel of `matRowScale` at `a ≠ r`.
/-- `matRowScale` fixes every other row. -/
theorem matRowScale_other (A : FreeMatrix K m n) (r a : Fin m) (h : a ≠ r) (s : K)
    (c : Fin n) :
    matRowScale A r s a c = A a c :=
  ite_eq_right h

-- Reference: definitional peel of `matRowElim` at `a = r`.
/-- `matRowElim` fixes the pivot row. -/
theorem matRowElim_self (A : FreeMatrix K m n) (r : Fin m) (j c : Fin n) :
    matRowElim A r j r c = A r c :=
  ite_eq_left rfl

-- Reference: definitional peel of `matRowElim` at `a ≠ r`.
/-- `matRowElim` subtracts `A a j` times the pivot row from row `a`. -/
theorem matRowElim_other (A : FreeMatrix K m n) (r a : Fin m) (h : a ≠ r) (j c : Fin n) :
    matRowElim A r j a c = A a c - A a j * A r c :=
  ite_eq_right h

-- Reference: Mines–Richman–Ruitenburg 2008, Pt. II Ch. 6 (clearing the
-- pivot column); Axler, *Linear Algebra Done Right*, 4th ed., Ch. 1.
/-- The elimination step clears the pivot column in every other row when
the pivot entry is `1`. -/
theorem matRowElim_pivot_zero (A : FreeMatrix K m n) (r a : Fin m) (h : a ≠ r) (j : Fin n)
    (hp : A r j = 1) :
    matRowElim A r j a j = 0 := by
  -- rw [matRowElim_other A r a h j j]: fully instantiated, unique occurrence.
  rw [matRowElim_other A r a h j j]
  -- rw [hp, mul_one, sub_self]: `A r j` occurs once; then `x * 1 = x`, `x - x = 0`.
  rw [hp, mul_one, sub_self]

-- Reference: Mines–Richman–Ruitenburg 2008, Pt. II Ch. 6 (normalizing the
-- pivot to `1` over a field).
/-- After swapping the pivot row into place and scaling by the inverse of
the pivot entry, the pivot entry is `1`. -/
theorem rrefStep_pivot_one (hinv : ∀ a : K, a ≠ 0 → invK a * a = 1)
    (A : FreeMatrix K m n) (r i : Fin m) (c : Fin n) (h : A i c ≠ 0) :
    matRowScale (matRowSwap A r i) r (invK (A i c)) r c = 1 := by
  -- rw [matRowScale_self]: fully instantiated, unique occurrence.
  rw [matRowScale_self]
  -- rw [matRowSwap_left]: unique occurrence of `matRowSwap A r i r c`.
  rw [matRowSwap_left]
  exact hinv (A i c) h
variable [DecidableEq K]

/-! ## The pivot search -/

-- Reference: Mines–Richman–Ruitenburg 2008, Pt. II Ch. 6 (choosing a pivot
-- row in a discrete field is a finite, explicit search).
/-- Search the rows `lo, lo+1, …, lo+t-1` (stopping at the row count `m`)
for the first row with `p i = true`; structural recursion on the fuel
`t`, hence total and computable. -/
def findPivotRow {m : ℕ} (p : Fin m → Bool) : ℕ → ℕ → Option (Fin m)
  | 0, _ => none
  | t+1, lo =>
      if h : lo < m then
        if p ⟨lo, h⟩ then some ⟨lo, h⟩ else findPivotRow p t (lo+1)
      else none

-- Reference: definitional peel of `findPivotRow` at fuel `0`.
/-- With no fuel left, the search finds nothing. -/
theorem findPivotRow_zero {m : ℕ} (p : Fin m → Bool) (lo : ℕ) :
    findPivotRow p 0 lo = none :=
  rfl

-- Reference: definitional peel of `findPivotRow` at fuel `t+1`.
/-- One search step: test row `lo`, then continue from `lo+1`. -/
theorem findPivotRow_succ {m : ℕ} (p : Fin m → Bool) (t lo : ℕ) :
    findPivotRow p (t+1) lo =
      (if h : lo < m then
        (if p ⟨lo, h⟩ then some ⟨lo, h⟩ else findPivotRow p t (lo+1))
      else none) :=
  rfl

-- Reference: Mines–Richman–Ruitenburg 2008, Pt. II Ch. 6 (soundness of the
-- pivot search).
/-- If the search returns a row, it is in the searched range and satisfies
the predicate. -/
theorem findPivotRow_some_spec {m : ℕ} {p : Fin m → Bool} {t lo : ℕ} {i : Fin m}
    (h : findPivotRow p t lo = some i) :
    lo ≤ i.val ∧ i.val < lo + t ∧ p i = true := by
  induction t generalizing lo with
  | zero =>
      -- rw [findPivotRow_zero] at h: fully instantiated, unique occurrence in `h`.
      rw [findPivotRow_zero] at h
      cases h
  | succ t ih =>
      -- rw [findPivotRow_succ] at h: fully instantiated, unique occurrence in `h`.
      rw [findPivotRow_succ] at h
      rcases Nat.lt_or_ge lo m with hlt | hge
      · -- rw [dite_eq_left hlt] at h: `lo < m` holds; single `dite` occurrence in `h`.
        rw [dite_eq_left hlt] at h
        cases (inferInstance : Decidable (p ⟨lo, hlt⟩ = true)) with
        | isTrue hp =>
          -- rw [ite_eq_left hp] at h: `p ⟨lo, hlt⟩ = true`; single `ite` occurrence.
          rw [ite_eq_left hp] at h
          injection h with hval
          subst hval
          exact ⟨Nat.le_refl lo, Nat.lt_add_of_pos_right (Nat.succ_pos t), hp⟩
        | isFalse hp =>
          -- rw [ite_eq_right hp] at h: `p ⟨lo, hlt⟩ ≠ true`; single occurrence.
          rw [ite_eq_right hp] at h
          have ihh := ih (lo := lo+1) h
          -- `lo+1+t = lo+(t+1)`: both sides count the searched rows.
          have h2 : lo+1+t = lo+(t+1) := Nat.add_right_comm lo 1 t
          -- rw [h2] at ihh: fully instantiated, unique occurrence.
          rw [h2] at ihh
          exact ⟨Nat.le_trans (Nat.le_succ lo) ihh.1, ihh.2.1, ihh.2.2⟩
      · -- rw [dite_eq_right ...] at h: `m ≤ lo`; single occurrence.
        rw [dite_eq_right (Nat.not_lt.mpr hge)] at h
        cases h

-- Reference: Mines–Richman–Ruitenburg 2008, Pt. II Ch. 6 (completeness of
-- the pivot search).
/-- If the search returns nothing, no row in the searched range satisfies
the predicate. -/
theorem findPivotRow_none_spec {m : ℕ} {p : Fin m → Bool} {t lo : ℕ}
    (h : findPivotRow p t lo = none) (i : Fin m) (hle : lo ≤ i.val)
    (hib : i.val < lo + t) :
    p i = false := by
  induction t generalizing lo with
  | zero => exact absurd (Nat.lt_of_le_of_lt hle hib) (Nat.lt_irrefl lo)
  | succ t ih =>
      -- rw [findPivotRow_succ] at h: fully instantiated, unique occurrence in `h`.
      rw [findPivotRow_succ] at h
      rcases Nat.lt_or_ge lo m with hlt | hge
      · -- rw [dite_eq_left hlt] at h: single occurrence.
        rw [dite_eq_left hlt] at h
        cases (inferInstance : Decidable (p ⟨lo, hlt⟩ = true)) with
        | isTrue hp =>
          -- rw [ite_eq_left hp] at h: single occurrence; `some _ = none` is absurd.
          rw [ite_eq_left hp] at h
          cases h
        | isFalse hp =>
          -- rw [ite_eq_right hp] at h: `p ⟨lo, hlt⟩ ≠ true`; single occurrence.
          rw [ite_eq_right hp] at h
          rcases Nat.lt_trichotomy i.val lo with hlt3 | heq | hlt3
          · exact absurd (Nat.lt_of_le_of_lt hle hlt3) (Nat.lt_irrefl lo)
          · -- `i.val = lo`, hence `i = ⟨lo, hlt⟩`.
            have hi : i = ⟨lo, hlt⟩ := Fin.eq_of_val_eq heq
            -- rw [hi]: rule `i = ⟨lo, hlt⟩`, fully instantiated; unique `i` in goal.
            rw [hi]
            exact Bool.eq_false_iff.mpr hp
          · have h2 : lo+(t+1) = (lo+1)+t := Nat.add_right_comm lo t 1
            -- rw [h2] at hib: fully instantiated, unique occurrence.
            rw [h2] at hib
            exact ih (lo := lo+1) h (Nat.succ_le_of_lt hlt3) hib
      · -- `m ≤ lo`; then `i.val < m ≤ lo ≤ i.val` is absurd.
        rw [dite_eq_right (Nat.not_lt.mpr hge)] at h
        exact absurd
          (Nat.lt_of_le_of_lt hle (Nat.lt_of_lt_of_le i.isLt hge))
          (Nat.lt_irrefl lo)

-- Reference: Mines–Richman–Ruitenburg 2008, Pt. II Ch. 6.
/-- If no row satisfies the predicate, the search finds nothing. -/
theorem findPivotRow_eq_none_of {m : ℕ} {p : Fin m → Bool} {t lo : ℕ}
    (h : ∀ i : Fin m, p i = false) :
    findPivotRow p t lo = none := by
  induction t generalizing lo with
  | zero => exact findPivotRow_zero p lo
  | succ t ih =>
      -- rw [findPivotRow_succ]: fully instantiated, unique occurrence.
      rw [findPivotRow_succ]
      rcases Nat.lt_or_ge lo m with hlt | hge
      · -- rw [dite_eq_left hlt]: single occurrence.
        rw [dite_eq_left hlt]
        have hp := h ⟨lo, hlt⟩
        -- rw [hp, ite_eq_right Bool.false_ne_true]: `p ⟨lo, hlt⟩` occurs once.
        rw [hp, ite_eq_right Bool.false_ne_true]
        exact ih (lo := lo+1)
      · -- rw [dite_eq_right ...]: single occurrence; closes by `none = none`.
        rw [dite_eq_right (Nat.not_lt.mpr hge)]

/-! ## The elimination loop and its termination measure -/

-- Reference: Mines–Richman–Ruitenburg 2008, Pt. II Ch. 6 (the measure for
-- termination of Gaussian elimination: columns remaining).
/-- The termination measure of the elimination loop: the number of columns
strictly right of the current column `j`. Each recursive call decreases it
by exactly one (`colMeasure_step`), so `n + 1` units of fuel suffice. -/
def colMeasure (n j : ℕ) : ℕ := n - j

-- Reference: core `Nat.sub_succ_lt_self`; the measure peel.
/-- One loop step decreases the measure. -/
theorem colMeasure_step {n j : ℕ} (h : j < n) :
    colMeasure n (j+1) < colMeasure n j :=
  Nat.sub_succ_lt_self n j h

-- Reference: Mines–Richman–Ruitenburg 2008, Pt. II Ch. 6 (Gaussian
-- elimination, left to right by columns).
/-- One pass of Gaussian elimination, structurally recursive on the fuel
`fuel`: at state `(r, j, A)`, with `r` the next free row and `j` the
current column, find a pivot in column `j` at or below row `r`; if there
is one, swap it into row `r`, scale the pivot to `1`, clear the column,
and continue at `(r+1, j+1)`; otherwise just advance to column `j+1`.
Each recursive call consumes one column (`colMeasure_step`), so fuel
`n+1` always suffices. -/
def rrefAux (invK : K → K) : ℕ → ℕ → ℕ → FreeMatrix K m n → FreeMatrix K m n
  | 0, _, _, A => A
  | fuel+1, r, j, A =>
      if hj : j < n then
        if hr : r < m then
          match findPivotRow
              (fun i => Nat.ble r i.val && (if A i ⟨j, hj⟩ ≠ 0 then true else false)) m r with
          | none => rrefAux invK fuel r (j+1) A
          | some i =>
              rrefAux invK fuel (r+1) (j+1)
                (matRowElim
                  (matRowScale (matRowSwap A ⟨r, hr⟩ i) ⟨r, hr⟩ (invK (A i ⟨j, hj⟩)))
                  ⟨r, hr⟩ ⟨j, hj⟩)
        else rrefAux invK fuel r (j+1) A
      else A

-- Reference: definitional peel of `rrefAux` at fuel `0`.
/-- With no fuel left, the loop stops. -/
theorem rrefAux_fuel_zero (A : FreeMatrix K m n) (r j : ℕ) :
    rrefAux invK 0 r j A = A :=
  rfl

-- Reference: definitional peel of `rrefAux` at fuel `fuel+1`.
/-- One unrolling of the elimination loop. -/
theorem rrefAux_fuel_succ (A : FreeMatrix K m n) (fuel r j : ℕ) :
    rrefAux invK (fuel+1) r j A =
      (if hj : j < n then
        if hr : r < m then
          match findPivotRow
              (fun i => Nat.ble r i.val && (if A i ⟨j, hj⟩ ≠ 0 then true else false)) m r with
          | none => rrefAux invK fuel r (j+1) A
          | some i =>
              rrefAux invK fuel (r+1) (j+1)
                (matRowElim
                  (matRowScale (matRowSwap A ⟨r, hr⟩ i) ⟨r, hr⟩ (invK (A i ⟨j, hj⟩)))
                  ⟨r, hr⟩ ⟨j, hj⟩)
        else rrefAux invK fuel r (j+1) A
      else A) :=
  rfl

-- Reference: Mines–Richman–Ruitenburg 2008, Pt. II Ch. 6.
/-- Once the column index has passed the last column, the loop returns the
matrix unchanged. -/
theorem rrefAux_of_column_done (A : FreeMatrix K m n) (fuel r j : ℕ) (h : n ≤ j) :
    rrefAux invK fuel r j A = A := by
  induction fuel with
  | zero => exact rrefAux_fuel_zero invK A r j
  | succ fuel ih =>
      -- `rrefAux invK (fuel+1) r j A` is definitionally the `dite` below.
      change (if hj : j < n then _ else A) = A
      exact dite_eq_right (Nat.not_lt.mpr h)

-- Reference: Mines–Richman–Ruitenburg 2008, Pt. II Ch. 6.
/-- Gaussian elimination: the reduced row-echelon normal form of `A`,
computed with `n+1` units of fuel (enough by `colMeasure_step`). -/
def rref (invK : K → K) (A : FreeMatrix K m n) : FreeMatrix K m n :=
  rrefAux invK (n+1) 0 0 A

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
  -- unfold matLeadingCol: explicit constant; rw [hnone]: unique occurrence,
  -- and `match none …` then reduces to `n = n`.
  unfold matLeadingCol
  rw [hnone]

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
      -- rw [hn] at hlc: fully instantiated, unique occurrence; gives `n = c.val`.
      rw [hn] at hlc
      exact absurd c.isLt (Nat.not_lt.mpr (Nat.le_of_eq hlc))
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
      -- rw [hn] at hlc: fully instantiated, unique occurrence; gives `n = c.val`.
      rw [hn] at hlc
      exact absurd c.isLt (Nat.not_lt.mpr (Nat.le_of_eq hlc))

/-! ## Peels for the invariant induction -/

-- Reference: definitional peel of the `≠ 0` test used in the pivot search.
/-- A nonzero element tests `true`. -/
theorem pivotBool_true {x : K} (h : x ≠ 0) :
    (if x ≠ 0 then true else false) = true :=
  ite_eq_left h

-- Reference: definitional peel of the `≠ 0` test used in the pivot search.
/-- A zero element tests `false`. -/
theorem pivotBool_false {x : K} (h : x = 0) :
    (if x ≠ 0 then true else false) = false :=
  ite_eq_right (fun hne => hne h)

-- Reference: Mines–Richman–Ruitenburg 2008, Pt. II Ch. 6 (reading the test).
/-- If the test is `true`, the element is nonzero. -/
theorem ne_zero_of_pivotBool {x : K} (h : (if x ≠ 0 then true else false) = true) :
    x ≠ 0 := by
  cases (inferInstance : Decidable (x ≠ 0)) with
  | isTrue h' => exact h'
  | isFalse h' =>
      have h2 : (if x ≠ 0 then true else false) = false := ite_eq_right h'
      -- rw [h2] at h: fully instantiated, unique occurrence; gives `false = true`.
      rw [h2] at h
      exact absurd h Bool.false_ne_true

-- Reference: Mines–Richman–Ruitenburg 2008, Pt. II Ch. 6 (reading the test).
/-- If the test is `false`, the element is zero. -/
theorem eq_zero_of_pivotBool {x : K} (h : (if x ≠ 0 then true else false) = false) :
    x = 0 := by
  cases (inferInstance : Decidable (x ≠ 0)) with
  | isTrue h' =>
      have h2 : (if x ≠ 0 then true else false) = true := ite_eq_left h'
      -- rw [h2] at h: fully instantiated, unique occurrence; gives `true = false`.
      rw [h2] at h
      exact absurd h.symm Bool.false_ne_true
  | isFalse h' =>
      cases (inferInstance : Decidable (x = 0)) with
      | isTrue h0 => exact h0
      | isFalse h2 => exact absurd h2 h'

-- Reference: Mines–Richman–Ruitenburg 2008, Pt. II Ch. 6 (soundness of the
-- pivot search, specialized to the loop's column predicate).
/-- A found pivot row is at or below `r` and has a nonzero entry in column
`j`. -/
theorem rrefAux_pivot_some {A : FreeMatrix K m n} {r j : ℕ} {hj : j < n} {i : Fin m}
    (h : findPivotRow
        (fun i => Nat.ble r i.val && (if A i ⟨j, hj⟩ ≠ 0 then true else false)) m r
        = some i) :
    r ≤ i.val ∧ A i ⟨j, hj⟩ ≠ 0 := by
  have hspec := findPivotRow_some_spec h
  have hboth := Bool.and_eq_true_iff.mp hspec.2.2
  exact ⟨Eq.mp (Nat.ble_eq (x := r) (y := i.val)) hboth.1, ne_zero_of_pivotBool hboth.2⟩

-- Reference: Mines–Richman–Ruitenburg 2008, Pt. II Ch. 6 (completeness of the
-- pivot search, specialized to the loop's column predicate).
/-- If no pivot is found in column `j`, that column is zero at or below
row `r`. -/
theorem rrefAux_pivot_none {A : FreeMatrix K m n} {r j : ℕ} {hj : j < n}
    (h : findPivotRow
        (fun i => Nat.ble r i.val && (if A i ⟨j, hj⟩ ≠ 0 then true else false)) m r = none)
    (a : Fin m) (hle : r ≤ a.val) :
    A a ⟨j, hj⟩ = 0 := by
  have hspec := findPivotRow_none_spec h a hle
    (Nat.lt_of_lt_of_le a.isLt (Nat.le_add_left m r))
  rcases Bool.and_eq_false_iff.mp hspec with hb | ht
  · have hb' : Nat.ble r a.val = true := Eq.mpr (Nat.ble_eq (x := r) (y := a.val)) hle
    -- rw [hb] at hb': fully instantiated, unique occurrence; gives `false = true`.
    rw [hb] at hb'
    exact absurd hb' Bool.false_ne_true
  · exact eq_zero_of_pivotBool ht

-- Reference: Mines–Richman–Ruitenburg 2008, Pt. II Ch. 6 (skipping an
-- all-zero column preserves the invariant).
/-- If column `j` is zero at or below row `r`, advancing to column `j+1`
preserves the loop invariant. -/
theorem rrefState_step_none {r j : ℕ} {A : FreeMatrix K m n} (hj : j < n)
    (hs : RrefState r j A) (hcol : ∀ a : Fin m, r ≤ a.val → A a ⟨j, hj⟩ = 0) :
    RrefState r (j+1) A := by
  rcases hs with ⟨hR1, hR2, hR3, hR4, hR5, hR6⟩
  refine ⟨?_, hR2, ?_, hR4, hR5, hR6⟩
  · intro a ha c hc
    rcases Nat.lt_or_ge c.val j with hc' | hc'
    · exact hR1 a ha c hc'
    · have hval : c.val = j := Nat.le_antisymm (Nat.le_of_lt_succ hc) hc'
      have hceq : c = ⟨j, hj⟩ := Fin.eq_of_val_eq hval
      -- rw [hceq]: rule `c = ⟨j, hj⟩`, fully instantiated; unique `c` in the goal.
      rw [hceq]
      exact hcol a ha
  · intro a ha
    exact Nat.lt_of_lt_of_le (hR3 a ha) (Nat.le_succ j)

-- Reference: Mines–Richman–Ruitenburg 2008, Pt. II Ch. 6 (the pivot search
-- returns the first row of the searched range where the predicate holds).
/-- If the predicate holds at `i` and fails at every earlier row of the
searched range, the search returns `i`. -/
theorem findPivotRow_eq_some_of_first {m : ℕ} {p : Fin m → Bool} {t lo : ℕ} {i : Fin m}
    (hle : lo ≤ i.val) (hib : i.val < lo + t) (hp : p i = true)
    (hfirst : ∀ i' : Fin m, lo ≤ i'.val → i'.val < i.val → p i' = false) :
    findPivotRow p t lo = some i := by
  induction t generalizing lo with
  | zero => exact absurd (Nat.lt_of_le_of_lt hle hib) (Nat.lt_irrefl lo)
  | succ t ih =>
      -- rw [findPivotRow_succ]: fully instantiated, unique occurrence in the goal.
      rw [findPivotRow_succ]
      rcases Nat.lt_or_ge lo m with hlt | hge
      · -- rw [dite_eq_left hlt]: `lo < m` holds; single `dite` occurrence.
        rw [dite_eq_left hlt]
        cases (inferInstance : Decidable (p ⟨lo, hlt⟩ = true)) with
        | isTrue hp0 =>
            -- rw [ite_eq_left hp0]: single `ite` occurrence; the hit is at `lo`.
            rw [ite_eq_left hp0]
            rcases Nat.lt_or_ge lo i.val with hlt2 | hge2
            · exfalso
              have hf := hfirst ⟨lo, hlt⟩ (Nat.le_refl lo) hlt2
              -- rw [hp0] at hf: fully instantiated, unique occurrence; `true = false`.
              rw [hp0] at hf
              exact absurd hf.symm Bool.false_ne_true
            · -- `lo = i.val`, hence `⟨lo, hlt⟩ = i`.
              have heq : (⟨lo, hlt⟩ : Fin m) = i :=
                Fin.eq_of_val_eq (Nat.le_antisymm hle hge2)
              -- rw [heq]: rule `⟨lo, hlt⟩ = i`, fully instantiated; unique occurrence.
              rw [heq]
        | isFalse hp0 =>
            -- rw [ite_eq_right hp0]: single `ite` occurrence; recurse from `lo+1`.
            rw [ite_eq_right hp0]
            rcases Nat.lt_or_ge lo i.val with hlt2 | hge2
            · refine ih (lo := lo+1) ?_ ?_ ?_
              · exact Nat.succ_le_of_lt hlt2
              · have h2 : lo+(t+1) = (lo+1)+t := Nat.add_right_comm lo t 1
                -- rw [h2] at hib: fully instantiated, unique occurrence.
                rw [h2] at hib
                exact hib
              · intro i' hle' hlt'
                exact hfirst i' (Nat.le_trans (Nat.le_succ lo) hle') hlt'
            · exfalso
              have heq : (⟨lo, hlt⟩ : Fin m) = i :=
                Fin.eq_of_val_eq (Nat.le_antisymm hle hge2)
              -- rw [heq] at hp0: rule `⟨lo, hlt⟩ = i`; unique occurrence in `hp0`.
              rw [heq] at hp0
              exact hp0 hp
      · -- `m ≤ lo`: then `i.val < m ≤ lo ≤ i.val` is absurd.
        rw [dite_eq_right (Nat.not_lt.mpr hge)]
        exact absurd (Nat.lt_of_le_of_lt hle (Nat.lt_of_lt_of_le i.isLt hge))
          (Nat.lt_irrefl lo)

-- Reference: Mines–Richman–Ruitenburg 2008, Pt. II Ch. 6 (the search reads
-- only the prefix of the range that it examines).
/-- If `p` and `q` agree on the rows of the searched range below `b`, and the
search for `p` hits `i` below `b` within its fuel, the search for `q` hits
the same `i`. -/
theorem findPivotRow_congr_before {m : ℕ} {p q : Fin m → Bool} {t lo b : ℕ}
    (h : ∀ i' : Fin m, lo ≤ i'.val → i'.val < b → p i' = q i')
    {i : Fin m} (hi : findPivotRow p t lo = some i) (hib : i.val < b)
    (hbt : b ≤ lo + t) :
    findPivotRow q t lo = some i := by
  induction t generalizing lo with
  | zero =>
      -- rw [findPivotRow_zero] at hi: fully instantiated; `none = some i` is absurd.
      rw [findPivotRow_zero] at hi
      cases hi
  | succ t ih =>
      have hspec := findPivotRow_some_spec hi
      -- rw [findPivotRow_succ] at hi ⊢: fully instantiated, unique occurrences.
      rw [findPivotRow_succ] at hi ⊢
      rcases Nat.lt_or_ge lo m with hlt | hge
      · -- rw [dite_eq_left hlt] at hi ⊢: `lo < m`; single `dite` occurrences.
        rw [dite_eq_left hlt] at hi ⊢
        have hlob : lo < b := Nat.lt_of_le_of_lt hspec.1 hib
        cases (inferInstance : Decidable (p ⟨lo, hlt⟩ = true)) with
        | isTrue hp0 =>
            -- rw [ite_eq_left hp0] at hi: single `ite` occurrence in `hi`.
            rw [ite_eq_left hp0] at hi
            injection hi with hval
            subst hval
            have hq : q ⟨lo, hlt⟩ = true := by
              -- rw [← h ⟨lo, hlt⟩ (Nat.le_refl lo) hlob]: `q ⟨lo, hlt⟩` occurs once.
              rw [← h ⟨lo, hlt⟩ (Nat.le_refl lo) hlob]
              exact hp0
            -- rw [ite_eq_left hq]: single `ite` occurrence in the goal.
            rw [ite_eq_left hq]
        | isFalse hp0 =>
            -- rw [ite_eq_right hp0] at hi: single `ite` occurrence in `hi`.
            rw [ite_eq_right hp0] at hi
            -- rw [← h ⟨lo, hlt⟩ (Nat.le_refl lo) hlob]: `q ⟨lo, hlt⟩` occurs once.
            rw [← h ⟨lo, hlt⟩ (Nat.le_refl lo) hlob]
            -- rw [ite_eq_right hp0]: single `ite` occurrence in the goal.
            rw [ite_eq_right hp0]
            have h2 : lo+(t+1) = (lo+1)+t := Nat.add_right_comm lo t 1
            -- rw [h2] at hbt: fully instantiated, unique occurrence.
            rw [h2] at hbt
            have h' : ∀ i' : Fin m, (lo+1) ≤ i'.val → i'.val < b → p i' = q i' :=
              fun i' hle' hlt' => h i' (Nat.le_trans (Nat.le_succ lo) hle') hlt'
            exact ih h' hi hbt
      · -- `m ≤ lo`: the search for `p` finds nothing, contradicting `hi`.
        rw [dite_eq_right (Nat.not_lt.mpr hge)] at hi
        cases hi

-- Reference: definitional peel of `matLeadingCol` at a `some` search result.
/-- If the leading-column search of row `a` finds column `c`, the leading
column is `c.val`. -/
theorem matLeadingCol_eq_some {A : FreeMatrix K m n} {a : Fin m} {c : Fin n}
    (h : findPivotRow (fun c => if A a c ≠ 0 then true else false) n 0 = some c) :
    matLeadingCol A a = c.val := by
  -- unfold matLeadingCol: explicit constant; rw [h]: unique occurrence, and
  -- `match some c …` then reduces to `c.val = c.val`.
  unfold matLeadingCol
  rw [h]

-- Reference: definitional peel of `matLeadingCol` at a `none` search result.
/-- If the leading-column search of row `a` finds nothing, the row is zero
and the leading column is `n`. -/
theorem matLeadingCol_eq_none {A : FreeMatrix K m n} {a : Fin m}
    (h : findPivotRow (fun c => if A a c ≠ 0 then true else false) n 0 = none) :
    matLeadingCol A a = n := by
  -- unfold matLeadingCol: explicit constant; rw [h]: unique occurrence, and
  -- `match none …` then reduces to `n = n`.
  unfold matLeadingCol
  rw [h]

-- Reference: Mines–Richman–Ruitenburg 2008, Pt. II Ch. 6 (a leading column
-- inside a prefix is found by the search).
/-- If the leading column of row `a` lies below `j ≤ n`, the leading-column
search returns the corresponding column. -/
theorem matLeadingCol_some_of_lt {A : FreeMatrix K m n} {a : Fin m} {j : ℕ}
    (hj : j ≤ n) (h : matLeadingCol A a < j) :
    ∃ c : Fin n, findPivotRow (fun c => if A a c ≠ 0 then true else false) n 0 = some c ∧
      c.val = matLeadingCol A a := by
  cases hp : findPivotRow (fun c => if A a c ≠ 0 then true else false) n 0 with
  | none =>
      have hn : matLeadingCol A a = n := matLeadingCol_eq_none hp
      -- rw [hn] at h: fully instantiated, unique occurrence; gives `n < j`.
      rw [hn] at h
      exact absurd h (Nat.not_lt.mpr hj)
  | some c => exact ⟨c, Eq.refl _, (matLeadingCol_eq_some hp).symm⟩

-- Reference: Mines–Richman–Ruitenburg 2008, Pt. II Ch. 6 (the leading column
-- is determined by the prefix of columns below it).
/-- If `A` and `B` agree on row `a` at every column below `j`, and the leading
column of `A a` is below `j ≤ n`, then `B a` has the same leading column. -/
theorem matLeadingCol_eq_of_agree_before {A B : FreeMatrix K m n} {a : Fin m} {j : ℕ}
    (hj : j ≤ n) (h : ∀ c : Fin n, c.val < j → A a c = B a c)
    (hk : matLeadingCol A a < j) :
    matLeadingCol B a = matLeadingCol A a := by
  obtain ⟨c, hc, hcv⟩ := matLeadingCol_some_of_lt hj hk
  have hcvj : c.val < j := by
    -- rw [hcv]: `c.val` occurs once in the goal.
    rw [hcv]
    exact hk
  have hcong : ∀ i : Fin n, 0 ≤ i.val → i.val < j →
      (if A a i ≠ 0 then true else false) = (if B a i ≠ 0 then true else false) := by
    intro i _ hi
    have heqi := h i hi
    -- rw [heqi]: `A a i` occurs once in the goal; the sides become identical.
    rw [heqi]
  have hbt : j ≤ 0 + n := by
    -- rw [Nat.zero_add]: `0 + n` occurs once in the goal.
    rw [Nat.zero_add]
    exact hj
  have hhit := findPivotRow_congr_before hcong hc hcvj hbt
  -- rw [matLeadingCol_eq_some hhit]: unique occurrence of `matLeadingCol B a`.
  rw [matLeadingCol_eq_some hhit]
  -- rw [matLeadingCol_eq_some hc]: unique occurrence of `matLeadingCol A a`.
  rw [matLeadingCol_eq_some hc]

-- Reference: Mines–Richman–Ruitenburg 2008, Pt. II Ch. 6 (a row vanishing
-- before column `j` and nonzero at `j` has leading column `j`).
/-- If row `a` vanishes at every column below `j < n` and is nonzero at
column `j`, its leading column is `j`. -/
theorem matLeadingCol_eq_of_zero_before {A : FreeMatrix K m n} {a : Fin m} {j : ℕ}
    (hj : j < n) (hzero : ∀ c : Fin n, c.val < j → A a c = 0)
    (hne : A a ⟨j, hj⟩ ≠ 0) :
    matLeadingCol A a = j := by
  have hp : (fun c => if A a c ≠ 0 then true else false) ⟨j, hj⟩ = true :=
    pivotBool_true hne
  have hfirst : ∀ i' : Fin n, 0 ≤ i'.val → i'.val < j →
      (fun c => if A a c ≠ 0 then true else false) i' = false := by
    intro i' _ hi'
    exact pivotBool_false (hzero i' hi')
  have hib : (⟨j, hj⟩ : Fin n).val < 0 + n := by
    -- rw [Nat.zero_add]: `0 + n` occurs once in the goal.
    rw [Nat.zero_add]
    exact hj
  have hsearch : findPivotRow (fun c => if A a c ≠ 0 then true else false) n 0
      = some ⟨j, hj⟩ :=
    findPivotRow_eq_some_of_first (Nat.zero_le j) hib hp hfirst
  have hs := matLeadingCol_eq_some hsearch
  -- rw [hs]: unique occurrence of `matLeadingCol A a`; then `↑⟨j, hj⟩ = j`.
  rw [hs]

-- Reference: definitional peel of the swap-then-scale at the pivot row.
omit [DecidableEq K] in
/-- Scaling the swapped-in pivot row at the pivot row multiplies the old row
`i` entry by `s`. -/
theorem rrefStep_swap_scale_self (A : FreeMatrix K m n) (r' i : Fin m) (s : K)
    (c' : Fin n) :
    matRowScale (matRowSwap A r' i) r' s r' c' = s * A i c' := by
  -- rw [matRowScale_self …]: fully instantiated, unique occurrence of the scale.
  rw [matRowScale_self (matRowSwap A r' i) r' s c']
  -- rw [matRowSwap_left …]: fully instantiated, unique occurrence of the swap.
  rw [matRowSwap_left A r' i c']

-- Reference: Mines–Richman–Ruitenburg 2008, Pt. II Ch. 6; peel of the
-- composed pivot step at the new pivot row, before the pivot column.
omit [DecidableEq K] in
/-- After the pivot step, the new pivot row vanishes at every column before
the pivot column (the swapped-in row vanished there). -/
theorem rrefStepMat_pivot_row_before (A : FreeMatrix K m n) (r' i : Fin m) (s : K)
    (c c' : Fin n) (hzero : A i c' = 0) :
    matRowElim (matRowScale (matRowSwap A r' i) r' s) r' c r' c' = 0 := by
  -- rw [matRowElim_self …]: the elimination fixes the pivot row.
  rw [matRowElim_self (matRowScale (matRowSwap A r' i) r' s) r' c c']
  -- rw [rrefStep_swap_scale_self …]: swap+scale at the pivot row.
  rw [rrefStep_swap_scale_self A r' i s c']
  -- rw [hzero, mul_zero]: `A i c' = 0`, then `s * 0 = 0`.
  rw [hzero, mul_zero]

-- Reference: Mines–Richman–Ruitenburg 2008, Pt. II Ch. 6 (normalizing the
-- pivot to `1`); peel of the composed pivot step at the pivot entry.
omit [DecidableEq K] in
/-- After the pivot step, the pivot entry is `1`. -/
theorem rrefStepMat_pivot_row_at (hinv : ∀ a : K, a ≠ 0 → invK a * a = 1)
    (A : FreeMatrix K m n) (r' i : Fin m) (c : Fin n) (hne : A i c ≠ 0) :
    matRowElim (matRowScale (matRowSwap A r' i) r' (invK (A i c))) r' c r' c = 1 := by
  -- rw [matRowElim_self …]: the elimination fixes the pivot row.
  rw [matRowElim_self (matRowScale (matRowSwap A r' i) r' (invK (A i c))) r' c c]
  exact rrefStep_pivot_one invK hinv A r' i c hne

-- Reference: Mines–Richman–Ruitenburg 2008, Pt. II Ch. 6 (the pivot step
-- fixes every other row on the columns before the pivot column).
omit [DecidableEq K] in
/-- After the pivot step, every row other than the pivot row agrees with the
original matrix at every column before the pivot column. -/
theorem rrefStepMat_off_pivot_before (A : FreeMatrix K m n) (r' i a : Fin m) (s : K)
    (c c' : Fin n) (ha : a ≠ r') (hzero : A i c' = 0) (hzeror : A r' c' = 0) :
    matRowElim (matRowScale (matRowSwap A r' i) r' s) r' c a c' = A a c' := by
  -- rw [matRowElim_other …]: the elimination at an off-pivot row.
  rw [matRowElim_other (matRowScale (matRowSwap A r' i) r' s) r' a ha c c']
  -- rw [rrefStep_swap_scale_self …, hzero, mul_zero, mul_zero, sub_zero]: the
  -- pivot row entry at `c'` is `s * 0 = 0`, so the subtraction removes nothing.
  rw [rrefStep_swap_scale_self A r' i s c', hzero, mul_zero, mul_zero, sub_zero]
  -- rw [matRowScale_other …]: the scale fixes the off-pivot row.
  rw [matRowScale_other (matRowSwap A r' i) r' a ha s c']
  cases (inferInstance : Decidable (a = i)) with
  | isTrue h =>
      -- rw [h] at ha ⊢: rule `a = i`, fully instantiated; unique occurrences.
      rw [h] at ha ⊢
      -- rw [matRowSwap_right …]: the swap sends row `i` to the old row `r'`.
      rw [matRowSwap_right A r' i ha c']
      -- rw [hzeror, hzero]: both entries are `0`.
      rw [hzeror, hzero]
  | isFalse haI =>
      -- rw [matRowSwap_other …]: the swap fixes row `a`.
      rw [matRowSwap_other A r' i a ha haI]

-- Reference: Mines–Richman–Ruitenburg 2008, Pt. II Ch. 6 (the pivot step
-- preserves the invariant); Hörmann arXiv:2106.03803 Remark 3.3 (program
-- context).
/-- One pivot step — swap the pivot row `i` into row `r`, scale the pivot to
`1`, clear column `j` — takes `RrefState r j A` to `RrefState (r+1) (j+1) A3`. -/
theorem rrefState_step_pivot (hinv : ∀ a : K, a ≠ 0 → invK a * a = 1) {r j : ℕ}
    {A : FreeMatrix K m n} (hs : RrefState r j A) (hr : r < m) (hj : j < n) (i : Fin m)
    (hle : r ≤ i.val) (hne : A i ⟨j, hj⟩ ≠ 0) :
    RrefState (r+1) (j+1)
      (matRowElim
        (matRowScale (matRowSwap A ⟨r, hr⟩ i) ⟨r, hr⟩ (invK (A i ⟨j, hj⟩)))
        ⟨r, hr⟩ ⟨j, hj⟩) := by
  rcases hs with ⟨hR1, hR2, hR3, hR4, hR5, hR6⟩
  -- Name the three intermediate matrices: `A1` = swap, `A2` = scale, `A3` = elim.
  generalize hA1 : matRowSwap A ⟨r, hr⟩ i = A1
  generalize hA2 : matRowScale A1 ⟨r, hr⟩ (invK (A i ⟨j, hj⟩)) = A2
  generalize hA3 : matRowElim A2 ⟨r, hr⟩ ⟨j, hj⟩ = A3
  have hp1 : A2 ⟨r, hr⟩ ⟨j, hj⟩ = 1 := by
    -- rw [← hA2, ← hA1]: unfold the generalizations; unique occurrences of `A2`, `A1`.
    rw [← hA2, ← hA1]
    exact rrefStep_pivot_one invK hinv A ⟨r, hr⟩ i ⟨j, hj⟩ hne
  have hA3rc : A3 ⟨r, hr⟩ ⟨j, hj⟩ = 1 := by
    -- rw [← hA3, ← hA2, ← hA1]: unfold; unique occurrences of `A3`, `A2`, `A1`.
    rw [← hA3, ← hA2, ← hA1]
    exact rrefStepMat_pivot_row_at invK hinv A ⟨r, hr⟩ i ⟨j, hj⟩ hne
  have hA3r_before : ∀ c' : Fin n, c'.val < j → A3 ⟨r, hr⟩ c' = 0 := by
    intro c' hc'
    -- rw [← hA3, ← hA2, ← hA1]: unfold; unique occurrences.
    rw [← hA3, ← hA2, ← hA1]
    exact rrefStepMat_pivot_row_before A ⟨r, hr⟩ i (invK (A i ⟨j, hj⟩)) ⟨j, hj⟩ c'
      (hR1 i hle c' hc')
  have hA3off_at : ∀ a : Fin m, a ≠ ⟨r, hr⟩ → A3 a ⟨j, hj⟩ = 0 := by
    intro a ha
    -- rw [← hA3]: unique occurrence of `A3` in the goal.
    rw [← hA3]
    exact matRowElim_pivot_zero A2 ⟨r, hr⟩ a ha ⟨j, hj⟩ hp1
  have hA3off_before : ∀ a : Fin m, a ≠ ⟨r, hr⟩ → ∀ c' : Fin n, c'.val < j →
      A3 a c' = A a c' := by
    intro a ha c' hc'
    -- rw [← hA3, ← hA2, ← hA1]: unfold; unique occurrences.
    rw [← hA3, ← hA2, ← hA1]
    exact rrefStepMat_off_pivot_before A ⟨r, hr⟩ i a (invK (A i ⟨j, hj⟩)) ⟨j, hj⟩ c' ha
      (hR1 i hle c' hc') (hR1 ⟨r, hr⟩ (Nat.le_refl r) c' hc')
  have hne_of_lt : ∀ a : Fin m, a.val < r → a ≠ ⟨r, hr⟩ := by
    intro a ha h
    -- rw [h] at ha: rule `a = ⟨r, hr⟩`, fully instantiated; unique occurrence.
    rw [h] at ha
    exact absurd ha (Nat.lt_irrefl r)
  have hne_of_ge : ∀ a : Fin m, r+1 ≤ a.val → a ≠ ⟨r, hr⟩ := by
    intro a ha h
    -- rw [h] at ha: rule `a = ⟨r, hr⟩`, fully instantiated; unique occurrence.
    rw [h] at ha
    exact absurd ha (Nat.not_succ_le_self r)
  have hlc_r' : matLeadingCol A3 ⟨r, hr⟩ = j := by
    have hne3 : A3 ⟨r, hr⟩ ⟨j, hj⟩ ≠ 0 := by
      intro h
      -- rw [hA3rc] at h: fully instantiated, unique occurrence; gives `1 = 0`.
      rw [hA3rc] at h
      exact absurd h one_ne_zero
    exact matLeadingCol_eq_of_zero_before hj hA3r_before hne3
  have hlc_old : ∀ a : Fin m, a.val < r → matLeadingCol A3 a = matLeadingCol A a := by
    intro a hlt
    exact matLeadingCol_eq_of_agree_before (Nat.le_of_lt hj)
      (fun c' hc' => (hA3off_before a (hne_of_lt a hlt) c' hc').symm) (hR3 a hlt)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Rows at or below `r+1` vanish on columns `< j+1`.
    intro a ha c' hc'
    rcases Nat.lt_or_ge c'.val j with hlt | hge
    · -- rw [hA3off_before …]: `A3 a c'` occurs once in the goal.
      rw [hA3off_before a (hne_of_ge a ha) c' hlt]
      exact hR1 a (Nat.le_trans (Nat.le_succ r) ha) c' hlt
    · have hval : c'.val = j := Nat.le_antisymm (Nat.le_of_lt_succ hc') hge
      have hceq : c' = ⟨j, hj⟩ := Fin.eq_of_val_eq hval
      -- rw [hceq]: rule `c' = ⟨j, hj⟩`, fully instantiated; unique occurrence.
      rw [hceq]
      exact hA3off_at a (hne_of_ge a ha)
  · -- Rows `< r+1` are nonzero: old pivot rows keep their `1`, the new
    -- pivot row has `A3 ⟨r, hr⟩ ⟨j, hj⟩ = 1`.
    intro a ha
    rcases Nat.lt_or_ge a.val r with hlt | hge
    · have hk := hR3 a hlt
      have hkn : matLeadingCol A a < n := Nat.lt_trans hk hj
      have h1 : A a ⟨matLeadingCol A a, hkn⟩ = 1 :=
        hR4 a hlt ⟨matLeadingCol A a, hkn⟩ (Fin.val_mk hkn).symm
      intro hzero
      have h0 := hzero ⟨matLeadingCol A a, hkn⟩
      -- rw [hA3off_before …] at h0: `A3 a ⟨…⟩` occurs once in `h0`.
      rw [hA3off_before a (hne_of_lt a hlt) ⟨matLeadingCol A a, hkn⟩ hk] at h0
      -- rw [h1] at h0: `A a ⟨…⟩` occurs once in `h0`; gives `1 = 0`.
      rw [h1] at h0
      exact absurd h0 one_ne_zero
    · have haveq : a = ⟨r, hr⟩ :=
        Fin.eq_of_val_eq (Nat.le_antisymm (Nat.le_of_lt_succ ha) hge)
      -- rw [haveq]: rule `a = ⟨r, hr⟩`, fully instantiated; unique occurrence.
      rw [haveq]
      intro hzero
      have h0 := hzero ⟨j, hj⟩
      -- rw [hA3rc] at h0: fully instantiated, unique occurrence; gives `1 = 0`.
      rw [hA3rc] at h0
      exact absurd h0 one_ne_zero
  · -- Leading columns of rows `< r+1` are `< j+1`.
    intro a ha
    rcases Nat.lt_or_ge a.val r with hlt | hge
    · -- rw [hlc_old a hlt]: unique occurrence of `matLeadingCol A3 a`.
      rw [hlc_old a hlt]
      exact Nat.lt_trans (hR3 a hlt) (Nat.lt_succ_self j)
    · have haveq : a = ⟨r, hr⟩ :=
        Fin.eq_of_val_eq (Nat.le_antisymm (Nat.le_of_lt_succ ha) hge)
      -- rw [haveq, hlc_r']: unique occurrences in the goal.
      rw [haveq, hlc_r']
      exact Nat.lt_succ_self j
  · -- Pivot entries of rows `< r+1` are `1`.
    intro a ha c' hlc
    rcases Nat.lt_or_ge a.val r with hlt | hge
    · -- rw [hlc_old a hlt] at hlc: unique occurrence in `hlc`.
      rw [hlc_old a hlt] at hlc
      have hc'j : c'.val < j := by
        -- rw [← hlc]: `c'.val` occurs once in the goal.
        rw [← hlc]
        exact hR3 a hlt
      -- rw [hA3off_before …]: `A3 a c'` occurs once in the goal.
      rw [hA3off_before a (hne_of_lt a hlt) c' hc'j]
      exact hR4 a hlt c' hlc
    · have haveq : a = ⟨r, hr⟩ :=
        Fin.eq_of_val_eq (Nat.le_antisymm (Nat.le_of_lt_succ ha) hge)
      -- rw [haveq, hlc_r'] at hlc: unique occurrences; gives `j = c'.val`.
      rw [haveq, hlc_r'] at hlc
      have hceq : c' = ⟨j, hj⟩ := Fin.eq_of_val_eq hlc.symm
      -- rw [haveq, hceq]: unique occurrences in the goal.
      rw [haveq, hceq]
      exact hA3rc
  · -- Leading columns strictly increase on rows `< r+1`.
    intro a b ha hb hab
    rcases Nat.lt_or_ge a.val r with halt | hage
    · rcases Nat.lt_or_ge b.val r with hblt | hbge
      · -- rw [hlc_old …]: unique occurrences in the goal.
        rw [hlc_old a halt, hlc_old b hblt]
        exact hR5 a b halt hblt hab
      · have hbq : b = ⟨r, hr⟩ :=
          Fin.eq_of_val_eq (Nat.le_antisymm (Nat.le_of_lt_succ hb) hbge)
        -- rw [hlc_old a halt, hbq, hlc_r']: unique occurrences in the goal.
        rw [hlc_old a halt, hbq, hlc_r']
        exact hR3 a halt
    · have haq : a = ⟨r, hr⟩ :=
        Fin.eq_of_val_eq (Nat.le_antisymm (Nat.le_of_lt_succ ha) hage)
      -- rw [haq] at hab: rule `a = ⟨r, hr⟩`; unique occurrence in `hab`.
      rw [haq] at hab
      exact absurd (Nat.lt_of_lt_of_le hab (Nat.le_of_lt_succ hb)) (Nat.lt_irrefl r)
  · -- Pivot columns are cleared in every other row.
    intro a ha b hne' c' hlc
    rcases Nat.lt_or_ge a.val r with halt | hage
    · -- rw [hlc_old a halt] at hlc: unique occurrence in `hlc`.
      rw [hlc_old a halt] at hlc
      have hc'j : c'.val < j := by
        -- rw [← hlc]: `c'.val` occurs once in the goal.
        rw [← hlc]
        exact hR3 a halt
      rcases Nat.lt_or_ge b.val r with hblt | hbge
      · -- rw [hA3off_before …]: `A3 b c'` occurs once in the goal.
        rw [hA3off_before b (hne_of_lt b hblt) c' hc'j]
        exact hR6 a halt b hne' c' hlc
      · rcases Nat.lt_or_ge b.val (r+1) with hblt1 | hbge1
        · have hbq : b = ⟨r, hr⟩ :=
            Fin.eq_of_val_eq (Nat.le_antisymm (Nat.le_of_lt_succ hblt1) hbge)
          -- rw [hbq]: rule `b = ⟨r, hr⟩`; unique occurrence in the goal.
          rw [hbq]
          exact hA3r_before c' hc'j
        · -- rw [hA3off_before …]: `A3 b c'` occurs once in the goal.
          rw [hA3off_before b (hne_of_ge b hbge1) c' hc'j]
          exact hR1 b (Nat.le_trans (Nat.le_succ r) hbge1) c' hc'j
    · have haq : a = ⟨r, hr⟩ :=
        Fin.eq_of_val_eq (Nat.le_antisymm (Nat.le_of_lt_succ ha) hage)
      -- rw [haq, hlc_r'] at hlc: unique occurrences; gives `j = c'.val`.
      rw [haq, hlc_r'] at hlc
      have hceq : c' = ⟨j, hj⟩ := Fin.eq_of_val_eq hlc.symm
      -- rw [hceq]: rule `c' = ⟨j, hj⟩`; unique occurrence in the goal.
      rw [hceq]
      exact hA3off_at b (fun h => hne' (haq.trans h.symm))

-- Reference: Mines–Richman–Ruitenburg 2008, Pt. II Ch. 6 (the induction on
-- the loop); Hörmann arXiv:2106.03803 Remark 3.3 (program context).
/-- The main invariant induction of the elimination loop: from a state
`(r, j, A)` satisfying `RrefState`, with enough fuel, the loop output is
in reduced row-echelon form. -/
theorem rrefAux_state (hinv : ∀ a : K, a ≠ 0 → invK a * a = 1) {fuel r j : ℕ}
    {A : FreeMatrix K m n} (hs : RrefState r j A)
    (hr : r ≤ m) (hfuel : n ≤ j + fuel) :
    IsRref (rrefAux invK fuel r j A) := by
  induction fuel generalizing r j A with
  | zero => exact rrefState_isRref_of_done hfuel hs
  | succ fuel ih =>
      -- rw [rrefAux_fuel_succ]: fully instantiated, unique occurrence in the goal.
      rw [rrefAux_fuel_succ]
      rcases Nat.lt_or_ge j n with hj | hj
      · -- rw [dite_eq_left hj]: `j < n` holds; single `dite` occurrence.
        rw [dite_eq_left hj]
        rcases Nat.lt_or_ge r m with hrm | hrm
        · -- rw [dite_eq_left hrm]: `r < m` holds; single `dite` occurrence.
          rw [dite_eq_left hrm]
          cases hfp : findPivotRow
              (fun i => Nat.ble r i.val && (if A i ⟨j, hj⟩ ≠ 0 then true else false)) m r with
          | none =>
              have hcol : ∀ a : Fin m, r ≤ a.val → A a ⟨j, hj⟩ = 0 :=
                fun a ha => rrefAux_pivot_none hfp a ha
              have h2 : j+(fuel+1) = j+1+fuel := Nat.add_right_comm j fuel 1
              -- rw [h2] at hfuel: fully instantiated, unique occurrence.
              rw [h2] at hfuel
              exact ih (rrefState_step_none hj hs hcol) hr hfuel
          | some i =>
              have hpi := rrefAux_pivot_some hfp
              have h2 : j+(fuel+1) = j+1+fuel := Nat.add_right_comm j fuel 1
              -- rw [h2] at hfuel: fully instantiated, unique occurrence.
              rw [h2] at hfuel
              exact ih (rrefState_step_pivot invK hinv hs hrm hj i hpi.1 hpi.2)
                (Nat.succ_le_of_lt hrm) hfuel
        · -- `m ≤ r`: no row is at or below `r`, so column `j` is vacuously zero there.
          rw [dite_eq_right (Nat.not_lt.mpr hrm)]
          have hcol : ∀ a : Fin m, r ≤ a.val → A a ⟨j, hj⟩ = 0 :=
            fun a ha => absurd
              (Nat.lt_of_le_of_lt ha (Nat.lt_of_lt_of_le a.isLt hrm)) (Nat.lt_irrefl r)
          have h2 : j+(fuel+1) = j+1+fuel := Nat.add_right_comm j fuel 1
          -- rw [h2] at hfuel: fully instantiated, unique occurrence.
          rw [h2] at hfuel
          exact ih (rrefState_step_none hj hs hcol) hr hfuel
      · -- `n ≤ j`: all columns processed; the loop returns `A` unchanged.
        rw [dite_eq_right (Nat.not_lt.mpr hj)]
        exact rrefState_isRref_of_done hj hs


-- Reference: Mines–Richman–Ruitenburg 2008, Pt. II Ch. 6; issue #108
-- (correctness of the elimination procedure).
/-- Correctness of Gaussian elimination: the output is in reduced
row-echelon form. -/
theorem rref_isRref (hinv : ∀ a : K, a ≠ 0 → invK a * a = 1) (A : FreeMatrix K m n) :
    IsRref (rref invK A) :=
  rrefAux_state invK hinv (rrefState_zero A) (Nat.zero_le m)
    ((Nat.le_succ n).trans (Nat.le_of_eq (Nat.zero_add (n+1)).symm))

/-! ## Smoke test on a concrete 3×3 matrix over `ℚ` -/

-- Reference: smoke test for the P.2.1 acceptance criterion (issue #108).
/-- A concrete 3×3 matrix over `ℚ`: rows `(2,4,6)`, `(1,3,5)`, `(0,1,4)`. -/
def smokeMat : Fin 3 → Fin 3 → ℚ := fun i j =>
  match i.val, j.val with
  | 0, 0 => (2 : ℚ) | 0, 1 => (4 : ℚ) | 0, 2 => (6 : ℚ)
  | 1, 0 => (1 : ℚ) | 1, 1 => (3 : ℚ) | 1, 2 => (5 : ℚ)
  | 2, 0 => (0 : ℚ) | 2, 1 => (1 : ℚ) | 2, 2 => (4 : ℚ)
  | _, _ => (0 : ℚ)

-- Reference: display helper for the smoke test (issue #108).
/-- The rows of a matrix as lists, for `#eval`/`rfl` display. -/
def matToLists (A : FreeMatrix K m n) : List (List K) :=
  (List.finRange m).map (fun i => (List.finRange n).map (fun j => A i j))

#eval matToLists smokeMat
#eval matToLists (rref (K := ℚ) (fun a => a⁻¹) smokeMat)

-- Reference: smoke test for the P.2.1 acceptance criterion (issue #108):
-- `decide`-evaluable means the term computes. The `decide` *tactic* is
-- banned by style, so the computation is demonstrated by the two `#eval`
-- displays above: the input `[[2, 4, 6], [1, 3, 5], [0, 1, 4]]` and its
-- reduced row-echelon normal form `[[1, 0, 0], [0, 1, 0], [0, 0, 1]]`.
-- (A kernel `rfl` cannot fire on `ℚ` arithmetic only because Lean core
-- marks `Rat.mul`/`Rat.inv` `@[irreducible]` — not because of this module.)

/-! ## Axiom lint -/

#lint_axioms BoringMath.FreeMatrix
#lint_axioms BoringMath.matRowSwap
#lint_axioms BoringMath.matRowScale
#lint_axioms BoringMath.matRowElim
#lint_axioms BoringMath.matRowSwap_apply
#lint_axioms BoringMath.matRowSwap_left
#lint_axioms BoringMath.matRowSwap_right
#lint_axioms BoringMath.matRowSwap_other
#lint_axioms BoringMath.matRowSwap_diag
#lint_axioms BoringMath.matRowScale_self
#lint_axioms BoringMath.matRowScale_other
#lint_axioms BoringMath.matRowElim_self
#lint_axioms BoringMath.matRowElim_other
#lint_axioms BoringMath.matRowElim_pivot_zero
#lint_axioms BoringMath.rrefStep_pivot_one
#lint_axioms BoringMath.findPivotRow
#lint_axioms BoringMath.findPivotRow_zero
#lint_axioms BoringMath.findPivotRow_succ
#lint_axioms BoringMath.findPivotRow_some_spec
#lint_axioms BoringMath.findPivotRow_none_spec
#lint_axioms BoringMath.findPivotRow_eq_none_of
#lint_axioms BoringMath.colMeasure
#lint_axioms BoringMath.colMeasure_step
#lint_axioms BoringMath.rrefAux
#lint_axioms BoringMath.rrefAux_fuel_zero
#lint_axioms BoringMath.rrefAux_fuel_succ
#lint_axioms BoringMath.rrefAux_of_column_done
#lint_axioms BoringMath.rref
#lint_axioms BoringMath.matRowZero
#lint_axioms BoringMath.matLeadingCol
#lint_axioms BoringMath.matLeadingCol_eq_of_rowZero
#lint_axioms BoringMath.IsRref
#lint_axioms BoringMath.RrefState
#lint_axioms BoringMath.rrefState_zero
#lint_axioms BoringMath.rrefState_isRref_of_done
#lint_axioms BoringMath.pivotBool_true
#lint_axioms BoringMath.pivotBool_false
#lint_axioms BoringMath.ne_zero_of_pivotBool
#lint_axioms BoringMath.eq_zero_of_pivotBool
#lint_axioms BoringMath.rrefAux_pivot_some
#lint_axioms BoringMath.rrefAux_pivot_none
#lint_axioms BoringMath.rrefState_step_none
#lint_axioms BoringMath.findPivotRow_eq_some_of_first
#lint_axioms BoringMath.findPivotRow_congr_before
#lint_axioms BoringMath.matLeadingCol_eq_some
#lint_axioms BoringMath.matLeadingCol_eq_none
#lint_axioms BoringMath.matLeadingCol_some_of_lt
#lint_axioms BoringMath.matLeadingCol_eq_of_agree_before
#lint_axioms BoringMath.matLeadingCol_eq_of_zero_before
#lint_axioms BoringMath.rrefStep_swap_scale_self
#lint_axioms BoringMath.rrefStepMat_pivot_row_before
#lint_axioms BoringMath.rrefStepMat_pivot_row_at
#lint_axioms BoringMath.rrefStepMat_off_pivot_before
#lint_axioms BoringMath.rrefState_step_pivot
#lint_axioms BoringMath.rrefAux_state
#lint_axioms BoringMath.rref_isRref
#lint_axioms BoringMath.smokeMat
#lint_axioms BoringMath.matToLists

end BoringMath
