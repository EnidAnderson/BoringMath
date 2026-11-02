/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Init
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Fin.Basic
import BoringMath.FormalPeriods.FreeMod
import BoringMath.FormalPeriods.RowReduction
/-!
# Pivot search and leading-column peels (P.2.3, part 3)

Piece 3 of `BoringMath.FormalPeriods.DecidableSubspace`: congruence and
first-pivot lemmas for `findPivotRow`, bounds and characterizations of
`matLeadingCol`, and the zero-row consequences.
-/
universe u
namespace BoringMath
variable {K : Type u} [Field K] {m n k p : ℕ}
variable [DecidableEq K]
/-! ## Pivot-search and leading-column peels -/
-- Reference: MRR 1988, Pt. II Ch. 6 (the pivot search is a congruence on the
-- predicate); successor step of the induction on the fuel.
/-- The successor step of the pivot-search congruence. -/
theorem findPivotRow_congr_succ {q : ℕ} {p r : Fin q → Bool} (h : ∀ i, p i = r i)
    (t lo : ℕ) (ih : ∀ lo, findPivotRow p t lo = findPivotRow r t lo) :
    findPivotRow p (t + 1) lo = findPivotRow r (t + 1) lo := by
  rcases Nat.lt_or_ge lo q with hlt | hge
  · exact ((findPivotRow_succ p t lo).trans (dite_eq_left hlt)).trans
      ((congrArg (fun b => if b then some ⟨lo, hlt⟩ else findPivotRow p t (lo + 1))
          (h ⟨lo, hlt⟩)).trans
      ((congrArg (fun z => if r ⟨lo, hlt⟩ then some ⟨lo, hlt⟩ else z) (ih (lo + 1))).trans
      ((dite_eq_left hlt).symm.trans (findPivotRow_succ r t lo))))
  · exact ((findPivotRow_succ p t lo).trans (dite_eq_right (Nat.not_lt.mpr hge))).trans
      (((findPivotRow_succ r t lo).trans (dite_eq_right (Nat.not_lt.mpr hge))).symm)
-- Reference: MRR 1988, Pt. II Ch. 6 (the pivot search only reads the
-- predicate; equal predicates give equal searches).
/-- The pivot search is a congruence on the predicate. -/
theorem findPivotRow_congr {q : ℕ} {p r : Fin q → Bool} (h : ∀ i, p i = r i) (t lo : ℕ) :
    findPivotRow p t lo = findPivotRow r t lo :=
  Nat.rec (motive := fun t => ∀ lo, findPivotRow p t lo = findPivotRow r t lo)
    (fun lo => (findPivotRow_zero p lo).trans (findPivotRow_zero r lo).symm)
    (fun t ih lo => findPivotRow_congr_succ h t lo ih) t lo
-- Reference: MRR 1988, Pt. II Ch. 6 (the search returns the FIRST hit);
-- successor step of the induction on the fuel.
/-- The successor step of the first-hit lemma. -/
theorem findPivotRow_some_first_succ {q : ℕ} {p : Fin q → Bool} {t lo : ℕ} {i i' : Fin q}
    (ih : ∀ lo', findPivotRow p t lo' = some i → lo' ≤ i'.val → p i' = false)
    (h : findPivotRow p (t + 1) lo = some i) (hle : lo ≤ i'.val) (hlt : i'.val < i.val) :
    p i' = false := by
  have h1 : (if h : lo < q then (if p ⟨lo, h⟩ then some ⟨lo, h⟩ else
      findPivotRow p t (lo + 1)) else none) = some i := Eq.subst (motive := fun z => z = some i) (findPivotRow_succ p t lo) h
  rcases Nat.lt_or_ge lo q with hltm | hgem
  · have h2 : (if p ⟨lo, hltm⟩ then some ⟨lo, hltm⟩ else findPivotRow p t (lo + 1))
      = some i := Eq.mp (congrArg (· = some i) (dite_eq_left hltm)) h1
    cases (inferInstance : Decidable (p ⟨lo, hltm⟩ = true)) with
    | isTrue hp =>
        have h3 : some ⟨lo, hltm⟩ = some i := Eq.mp (congrArg (· = some i) (ite_eq_left hp)) h2
        injection h3 with hval
        subst hval
        exact absurd hlt (Nat.not_lt.mpr hle)
    | isFalse hp =>
        have h4 : findPivotRow p t (lo + 1) = some i := Eq.mp (congrArg (· = some i) (ite_eq_right hp)) h2
        rcases Nat.lt_or_ge lo i'.val with hlt' | hge'
        · exact ih (lo + 1) h4 (Nat.succ_le_of_lt hlt')
        · have heq : i' = ⟨lo, hltm⟩ := Fin.eq_of_val_eq (Nat.le_antisymm hge' hle)
          exact Eq.mpr (congrArg (fun z => p z = false) heq) (Bool.eq_false_iff.mpr hp)
  · have h5 : none = some i := Eq.mp (congrArg (· = some i) (dite_eq_right (Nat.not_lt.mpr hgem))) h1
    cases h5
-- Reference: MRR 1988, Pt. II Ch. 6 (the search returns the FIRST row of the
-- range where the predicate holds).
-- Reference: MRR 1988, Pt. II Ch. 6 (the search returns the FIRST hit); the
-- zero-fuel case.
/-- With no fuel left, the search finds nothing, contradicting the hit. -/
theorem findPivotRow_some_first_zero {q : ℕ} {p : Fin q → Bool} {lo : ℕ} {i : Fin q}
    (h : findPivotRow p 0 lo = some i) (i' : Fin q) (hle : lo ≤ i'.val)
    (hlt : i'.val < i.val) : p i' = false := by
  have h0 : none = some i :=
    Eq.subst (motive := fun z => z = some i) (findPivotRow_zero p lo) h
  cases h0

theorem findPivotRow_some_first {q : ℕ} {p : Fin q → Bool} {t lo : ℕ} {i : Fin q}
    (h : findPivotRow p t lo = some i) (i' : Fin q) (hle : lo ≤ i'.val)
    (hlt : i'.val < i.val) :
    p i' = false := by
  induction t generalizing lo with
  | zero => exact findPivotRow_some_first_zero h i' hle hlt
  | succ t ih => exact findPivotRow_some_first_succ (i' := i') (fun lo' h' hle' => ih h' hle') h hle hlt
-- Reference: MRR 1988, Pt. II Ch. 6 (the leading column depends only on the
-- row entries).
/-- Rows with equal entries have equal leading columns. -/
theorem matLeadingCol_congr {p q : ℕ} {A : FreeMatrix K p n} {B : FreeMatrix K q n}
    {a : Fin p} {b : Fin q}
    (h : ∀ c, A a c = B b c) :
    matLeadingCol A a = matLeadingCol B b := by
  unfold matLeadingCol
  exact congrArg (fun o => match o with | some c => c.val | none => n)
    (findPivotRow_congr (fun c => congrArg (fun x => if x ≠ 0 then true else false) (h c)) n 0)
-- Reference: MRR 1988, Pt. II Ch. 6 (a leading column is at most `n`).
-- Reference: MRR 1988, Pt. II Ch. 6 (a leading column is at most `n`); the
-- `none` case.
/-- If the leading-column search of row `a` finds nothing, the leading column
is `n`, hence `≤ n`. -/
theorem matLeadingCol_le_none {A : FreeMatrix K m n} {a : Fin m}
    (hs : findPivotRow (fun c => if A a c ≠ 0 then true else false) n 0 = none) :
    matLeadingCol A a ≤ n :=
  Eq.mpr (congrArg (· ≤ n) (matLeadingCol_eq_none hs)) (Nat.le_refl n)
-- Reference: MRR 1988, Pt. II Ch. 6 (a leading column is at most `n`); the
-- `some` case.
/-- If the leading-column search of row `a` finds `c`, the leading column is
`c.val < n`. -/
theorem matLeadingCol_le_some {A : FreeMatrix K m n} {a : Fin m} {c : Fin n}
    (hs : findPivotRow (fun c => if A a c ≠ 0 then true else false) n 0 = some c) :
    matLeadingCol A a ≤ n :=
  Eq.mpr (congrArg (· ≤ n) (matLeadingCol_eq_some hs)) (Nat.le_of_lt c.isLt)
-- Reference: MRR 1988, Pt. II Ch. 6 (a leading column is at most `n`).
/-- The leading column of a row is at most `n`. -/
theorem matLeadingCol_le (A : FreeMatrix K m n) (a : Fin m) : matLeadingCol A a ≤ n := by
  cases hs : findPivotRow (fun c => if A a c ≠ 0 then true else false) n 0 with
  | none => exact matLeadingCol_le_none hs
  | some c => exact matLeadingCol_le_some hs
-- Reference: MRR 1988, Pt. II Ch. 6 (a zero row makes the pivot search fail).
/-- A zero row has no pivot: the search returns `none`. -/
theorem findPivotRow_eq_none_of_rowZero {B : FreeMatrix K m n} {a : Fin m}
    (h : matRowZero B a) :
    findPivotRow (fun c => if B a c ≠ 0 then true else false) n 0 = none :=
  findPivotRow_eq_none_of (fun c => ite_eq_right (fun hne => hne (h c)))
-- Reference: MRR 1988, Pt. II Ch. 6 (if the pivot search fails, the row is
-- zero).
/-- If the pivot search of a row returns `none`, the row is zero. -/
theorem rowZero_of_findPivotRow_eq_none {B : FreeMatrix K m n} {a : Fin m}
    (h : findPivotRow (fun c => if B a c ≠ 0 then true else false) n 0 = none) :
    matRowZero B a :=
  fun c => eq_zero_of_pivotBool (findPivotRow_none_spec h c (Nat.zero_le c.val)
    (Eq.subst (Nat.zero_add n).symm c.isLt))
-- Reference: MRR 1988, Pt. II Ch. 6 (a row with leading column `n` is zero).
-- Reference: MRR 1988, Pt. II Ch. 6 (a row with leading column `n` is zero);
-- the `none` case.
/-- If the leading-column search of row `a` finds nothing, the row is zero. -/
theorem matRowZero_of_matLeadingCol_eq_none {A : FreeMatrix K m n} {a : Fin m}
    (hs : findPivotRow (fun c => if A a c ≠ 0 then true else false) n 0 = none) :
    matRowZero A a :=
  rowZero_of_findPivotRow_eq_none hs
-- Reference: MRR 1988, Pt. II Ch. 6 (a row with leading column `n` is zero);
-- the `some` case.
/-- If the leading-column search of row `a` finds `c`, then `c.val = n` is
absurd. -/
theorem matRowZero_of_matLeadingCol_eq_some {A : FreeMatrix K m n} {a : Fin m} {c : Fin n}
    (hs : findPivotRow (fun c => if A a c ≠ 0 then true else false) n 0 = some c)
    (h : matLeadingCol A a = n) : matRowZero A a :=
  absurd (Eq.mp (congrArg (· = n) (matLeadingCol_eq_some hs)) h) (Nat.ne_of_lt c.isLt)
-- Reference: MRR 1988, Pt. II Ch. 6 (a row with leading column `n` is zero).
/-- If the leading column of row `a` is `n`, the row is zero. -/
theorem matRowZero_of_matLeadingCol_eq {A : FreeMatrix K m n} {a : Fin m}
    (h : matLeadingCol A a = n) : matRowZero A a := by
  cases hs : findPivotRow (fun c => if A a c ≠ 0 then true else false) n 0 with
  | none => exact matRowZero_of_matLeadingCol_eq_none hs
  | some c => exact matRowZero_of_matLeadingCol_eq_some hs h
-- Reference: MRR 1988, Pt. II Ch. 6 (columns left of the leading column are
-- zero).
-- Reference: MRR 1988, Pt. II Ch. 6 (columns left of the leading column are
-- zero); the `none` case.
/-- If the leading-column search of row `a` finds nothing, every entry is
zero. -/
theorem entry_eq_zero_of_lt_matLeadingCol_none {A : FreeMatrix K m n} {a : Fin m}
    {c : Fin n}
    (hs : findPivotRow (fun c => if A a c ≠ 0 then true else false) n 0 = none) :
    A a c = 0 :=
  eq_zero_of_pivotBool (findPivotRow_none_spec hs c (Nat.zero_le c.val)
    (Eq.subst (Nat.zero_add n).symm c.isLt))
-- Reference: MRR 1988, Pt. II Ch. 6 (columns left of the leading column are
-- zero); the `some` case.
/-- If the search finds `c'`, columns left of `c'.val` are zero. -/
theorem entry_eq_zero_of_lt_matLeadingCol_some {A : FreeMatrix K m n} {a : Fin m}
    {c : Fin n} {c' : Fin n}
    (hs : findPivotRow (fun c => if A a c ≠ 0 then true else false) n 0 = some c')
    (h : c.val < matLeadingCol A a) : A a c = 0 :=
  eq_zero_of_pivotBool (findPivotRow_some_first hs c (Nat.zero_le c.val)
    (Eq.mp (congrArg (c.val < ·) (matLeadingCol_eq_some hs)) h))
-- Reference: MRR 1988, Pt. II Ch. 6 (columns left of the leading column are
-- zero).
/-- Entries strictly left of the leading column of a row are zero. -/
theorem entry_eq_zero_of_lt_matLeadingCol {A : FreeMatrix K m n} {a : Fin m} {c : Fin n}
    (h : c.val < matLeadingCol A a) : A a c = 0 := by
  cases hs : findPivotRow (fun c => if A a c ≠ 0 then true else false) n 0 with
  | none => exact entry_eq_zero_of_lt_matLeadingCol_none hs
  | some c' => exact entry_eq_zero_of_lt_matLeadingCol_some hs h
-- Reference: MRR 1988, Pt. II Ch. 6 (leading column of the first row is the
-- minimum over all rows); successor-row case.
/-- The leading column of row `0` is at most that of any successor row. -/
theorem matLeadingCol_zero_le_succ {A : FreeMatrix K (k + 1) n} (hA : IsRref A) (j : Fin k) :
    matLeadingCol A 0 ≤ matLeadingCol A (Fin.succ j) := by
  rcases hA with ⟨_, _, h3, _⟩
  cases hs : findPivotRow (fun c => if A (Fin.succ j) c ≠ 0 then true else false) n 0 with
  | none => exact Eq.mpr (congrArg (matLeadingCol A 0 ≤ ·) (matLeadingCol_eq_none hs)) (matLeadingCol_le A 0)
  | some c =>
      have hnb : ¬ matRowZero A (Fin.succ j) := fun hz =>
        ne_zero_of_pivotBool (findPivotRow_some_spec hs).2.2 (hz c)
      have hlt : matLeadingCol A 0 < matLeadingCol A (Fin.succ j) :=
        h3 0 (Fin.succ j) (Fin.succ_pos j) hnb
      exact Eq.mpr (congrArg (matLeadingCol A 0 ≤ ·) (matLeadingCol_eq_some hs))
        (Nat.le_of_lt (Eq.mp (congrArg (matLeadingCol A 0 < ·) (matLeadingCol_eq_some hs)) hlt))
-- Reference: MRR 1988, Pt. II Ch. 6 (leading column of the first row is the
-- minimum over all rows).
-- Reference: MRR 1988, Pt. II Ch. 6 (leading column of the first row is the
-- minimum over all rows); the `b = 0` case.
/-- If `b = 0`, the inequality is reflexive. -/
theorem matLeadingCol_zero_le_zero {A : FreeMatrix K (k + 1) n} (b : Fin (k + 1))
    (hb : b = 0) : matLeadingCol A 0 ≤ matLeadingCol A b :=
  Eq.mpr (congrArg (fun z => matLeadingCol A 0 ≤ matLeadingCol A z) hb) (Nat.le_refl _)
-- Reference: MRR 1988, Pt. II Ch. 6 (leading column of the first row is the
-- minimum over all rows).
/-- The leading column of row `0` is the minimum of the leading columns. -/
theorem matLeadingCol_zero_le {A : FreeMatrix K (k + 1) n} (hA : IsRref A) (b : Fin (k + 1)) :
    matLeadingCol A 0 ≤ matLeadingCol A b := by
  rcases Fin.eq_zero_or_eq_succ b with hb | ⟨j, hb⟩
  · exact matLeadingCol_zero_le_zero b hb
  · exact Eq.mpr (congrArg (fun z => matLeadingCol A 0 ≤ z) (congrArg (matLeadingCol A) hb))
      (matLeadingCol_zero_le_succ hA j)
end BoringMath
