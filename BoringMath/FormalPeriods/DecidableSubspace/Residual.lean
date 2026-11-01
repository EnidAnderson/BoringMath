/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Init
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import BoringMath.FormalPeriods.DecidableSubspace.Sums
import BoringMath.FormalPeriods.DecidableSubspace.RowSpan
import BoringMath.FormalPeriods.DecidableSubspace.Pivots
import BoringMath.FormalPeriods.DecidableSubspace.Rank
import BoringMath.FormalPeriods.DecidableSubspace.RowOps
import BoringMath.FormalPeriods.FreeMod
import BoringMath.FormalPeriods.RowReduction
/-!
# Leading column of a vector and the residual criterion (P.2.3, part 7)

Piece 7 of `BoringMath.FormalPeriods.DecidableSubspace`: `vecLeadingCol`, the
coefficient and residual functions `rrefCoeff`/`rrefResidual`, and the
criterion `inRowSpan R v ↔ rrefResidual R v = 0` for an RREF matrix `R`.
-/
universe u
namespace BoringMath
open BigOperators
variable {K : Type u} [Field K] {m n k p : ℕ}
variable [DecidableEq K]
/-! ## Leading column of a vector and the residual criterion -/
-- Reference: MRR 1988, Pt. II Ch. 6 (the leading column of a vector: the
-- first nonzero coordinate).
/-- The leading (first nonzero) column of a vector; `n` if the vector is
zero. -/
def vecLeadingCol (w : FreeMod K n) : ℕ :=
  match findPivotRow (fun c => if w c ≠ 0 then true else false) n 0 with
  | some c => c.val
  | none => n
-- Reference: definitional peel of `vecLeadingCol` at a `some` search result.
/-- If the search of `w` finds column `c`, the leading column is `c.val`. -/
theorem vecLeadingCol_eq_some {w : FreeMod K n} {c : Fin n}
    (h : findPivotRow (fun c => if w c ≠ 0 then true else false) n 0 = some c) :
    vecLeadingCol w = c.val := by
  unfold vecLeadingCol
  exact congrArg (fun o => match o with | some c => c.val | none => n) h
-- Reference: definitional peel of `vecLeadingCol` at a `none` search result.
/-- If the search of `w` finds nothing, the leading column is `n`. -/
theorem vecLeadingCol_eq_none {w : FreeMod K n}
    (h : findPivotRow (fun c => if w c ≠ 0 then true else false) n 0 = none) :
    vecLeadingCol w = n := by
  unfold vecLeadingCol
  exact congrArg (fun o => match o with | some c => c.val | none => n) h
-- Reference: MRR 1988, Pt. II Ch. 6 (a vector vanishing before column `j < n`
-- and nonzero at `j` has leading column `j`).
/-- A vector vanishing before `j < n` and nonzero at `j` has leading column
`j`. -/
theorem vecLeadingCol_eq_of_zero_before {w : FreeMod K n} {j : ℕ} (hj : j < n)
    (hzero : ∀ c : Fin n, c.val < j → w c = 0) (hne : w ⟨j, hj⟩ ≠ 0) :
    vecLeadingCol w = j :=
  (vecLeadingCol_eq_some (findPivotRow_eq_some_of_first (Nat.zero_le j)
    (Eq.subst (Nat.zero_add n).symm hj) (pivotBool_true hne)
    (fun i' _ hi' => pivotBool_false (hzero i' hi')))).trans (Fin.val_mk hj)
-- Reference: MRR 1988, Pt. II Ch. 6 (a nonzero vector has a leading column
-- inside the range).
-- Reference: MRR 1988, Pt. II Ch. 6 (a nonzero vector has a leading column
-- inside the range); the `none` case.
/-- If the search of `w` finds nothing, `w` is zero, contradicting `w ≠ 0`. -/
theorem vecLeadingCol_lt_none {w : FreeMod K n} (hw : w ≠ 0)
    (hs : findPivotRow (fun c => if w c ≠ 0 then true else false) n 0 = none) :
    vecLeadingCol w < n :=
  absurd (funext (fun c => eq_zero_of_pivotBool
    (findPivotRow_none_spec hs c (Nat.zero_le c.val)
      (Eq.subst (Nat.zero_add n).symm c.isLt)))) hw
-- Reference: MRR 1988, Pt. II Ch. 6 (a nonzero vector has a leading column
-- inside the range); the `some` case.
/-- If the search of `w` finds `c`, the leading column is `c.val < n`. -/
theorem vecLeadingCol_lt_some {w : FreeMod K n} {c : Fin n}
    (hs : findPivotRow (fun c => if w c ≠ 0 then true else false) n 0 = some c) :
    vecLeadingCol w < n :=
  Eq.mpr (congrArg (· < n) (vecLeadingCol_eq_some hs)) c.isLt
-- Reference: MRR 1988, Pt. II Ch. 6 (a nonzero vector has a leading column
-- inside the range).
/-- A nonzero vector has leading column `< n`. -/
theorem vecLeadingCol_lt {w : FreeMod K n} (hw : w ≠ 0) : vecLeadingCol w < n := by
  cases hs : findPivotRow (fun c => if w c ≠ 0 then true else false) n 0 with
  | none => exact vecLeadingCol_lt_none hw hs
  | some c => exact vecLeadingCol_lt_some hs
-- Reference: MRR 1988, Pt. II Ch. 6 (the entry at the leading column is
-- nonzero).
-- Reference: MRR 1988, Pt. II Ch. 6 (the entry at the leading column is
-- nonzero); the `none` case.
/-- If the search of `w` finds nothing, `w` is zero, contradicting `w ≠ 0`. -/
theorem vecLeadingCol_ne_zero_none {w : FreeMod K n} (hw : w ≠ 0)
    (hs : findPivotRow (fun c => if w c ≠ 0 then true else false) n 0 = none) :
    w ⟨vecLeadingCol w, vecLeadingCol_lt hw⟩ ≠ 0 :=
  absurd (funext (fun c => eq_zero_of_pivotBool
    (findPivotRow_none_spec hs c (Nat.zero_le c.val)
      (Eq.subst (Nat.zero_add n).symm c.isLt)))) hw
-- Reference: MRR 1988, Pt. II Ch. 6 (the entry at the leading column is
-- nonzero); the `some` case.
/-- If the search of `w` finds `c`, the leading column is `c.val` and `w c ≠ 0`. -/
theorem vecLeadingCol_ne_zero_some {w : FreeMod K n} (hw : w ≠ 0) {c : Fin n}
    (hs : findPivotRow (fun c => if w c ≠ 0 then true else false) n 0 = some c) :
    w ⟨vecLeadingCol w, vecLeadingCol_lt hw⟩ ≠ 0 :=
  let hlt := vecLeadingCol_lt hw
  let hne : w c ≠ 0 := ne_zero_of_pivotBool (findPivotRow_some_spec hs).2.2
  let heq : (⟨vecLeadingCol w, hlt⟩ : Fin n) = c :=
    Fin.eq_of_val_eq (vecLeadingCol_eq_some hs)
  Eq.mpr (congrArg (fun z => w z ≠ 0) heq) hne
-- Reference: MRR 1988, Pt. II Ch. 6 (the entry at the leading column is
-- nonzero).
/-- A nonzero vector is nonzero at its leading column. -/
theorem vecLeadingCol_ne_zero {w : FreeMod K n} (hw : w ≠ 0) :
    w ⟨vecLeadingCol w, vecLeadingCol_lt hw⟩ ≠ 0 := by
  cases hs : findPivotRow (fun c => if w c ≠ 0 then true else false) n 0 with
  | none => exact vecLeadingCol_ne_zero_none hw hs
  | some c => exact vecLeadingCol_ne_zero_some hw hs
-- Reference: MRR 1988, Pt. II Ch. 6 (columns left of the leading column of a
-- vector are zero).
-- Reference: MRR 1988, Pt. II Ch. 6 (columns left of the leading column of a
-- vector are zero); the `none` case.
/-- If the search of `w` finds nothing, every entry is zero. -/
theorem vecLeadingCol_vanish_before_none {w : FreeMod K n} {c : Fin n}
    (hs : findPivotRow (fun c => if w c ≠ 0 then true else false) n 0 = none) :
    w c = 0 :=
  eq_zero_of_pivotBool (findPivotRow_none_spec hs c (Nat.zero_le c.val)
    (Eq.subst (Nat.zero_add n).symm c.isLt))
-- Reference: MRR 1988, Pt. II Ch. 6 (columns left of the leading column of a
-- vector are zero); the `some` case.
/-- If the search of `w` finds `c'`, columns left of `c'.val` are zero. -/
theorem vecLeadingCol_vanish_before_some {w : FreeMod K n} {c c' : Fin n}
    (hs : findPivotRow (fun c => if w c ≠ 0 then true else false) n 0 = some c')
    (h : c.val < vecLeadingCol w) : w c = 0 :=
  eq_zero_of_pivotBool (findPivotRow_some_first hs c (Nat.zero_le c.val)
    (Eq.mp (congrArg (c.val < ·) (vecLeadingCol_eq_some hs)) h))
-- Reference: MRR 1988, Pt. II Ch. 6 (columns left of the leading column of a
-- vector are zero).
/-- A vector vanishes strictly left of its leading column. -/
theorem vecLeadingCol_vanish_before {w : FreeMod K n} {c : Fin n}
    (h : c.val < vecLeadingCol w) : w c = 0 := by
  cases hs : findPivotRow (fun c => if w c ≠ 0 then true else false) n 0 with
  | none => exact vecLeadingCol_vanish_before_none hs
  | some c' => exact vecLeadingCol_vanish_before_some hs h
-- Reference: MRR 1988, Pt. II Ch. 6 (a nonzero vector vanishing up to column
-- `j` has leading column strictly right of `j`).
/-- If `w ≠ 0` vanishes at all columns `≤ j`, then `j < vecLeadingCol w`. -/
theorem vecLeadingCol_lt_of_vanish {w : FreeMod K n} {j : ℕ} (hw : w ≠ 0)
    (hvan : ∀ c : Fin n, c.val ≤ j → w c = 0) : j < vecLeadingCol w := by
  rcases Nat.lt_or_ge j (vecLeadingCol w) with h | h
  · exact h
  · have hlt := vecLeadingCol_lt hw
    have hne := vecLeadingCol_ne_zero hw
    exact absurd (hvan ⟨vecLeadingCol w, hlt⟩ h) hne
-- Reference: MRR 1988, Pt. II Ch. 6 (evaluating a combination at a pivot
-- column reads off one coefficient).
/-- At the pivot column of row `b` of an RREF matrix, the combination
`∑ a ∈ finFinset _, d a * R a` equals `d b`. -/
theorem rref_sum_at_pivot {R : FreeMatrix K m n} (hR : IsRref R) {d : Fin m → K} {b : Fin m}
    {c : Fin n} (hlc : matLeadingCol R b = c.val) :
    (∑ a ∈ finFinset _, d a * R a c) = d b :=
  let ⟨_, h2, _, h4⟩ := hR
  let h1 : R b c = 1 := h2 b c hlc
  (sum_finFinset_eq_single (f := fun a => d a * R a c)
    (fun a hab => (congrArg (d a * ·) (h4 b a hab.symm c hlc)).trans (mul_zero _))).trans
    ((congrArg (d b * ·) h1).trans (mul_one _))
-- Reference: MRR 1988, Pt. II Ch. 6 (the coefficient of a combination at a
-- pivot row, read as data).
/-- The coefficient of row `a` in a combination, read at a pivot row. -/
def rrefCoeff (R : FreeMatrix K m n) (v : FreeMod K n) (a : Fin m) : K :=
  if h : matLeadingCol R a < n then v ⟨matLeadingCol R a, h⟩ else 0
-- Reference: MRR 1988, Pt. II Ch. 6 (the residual of `v` against the pivot
-- rows of an RREF matrix `R`).
/-- The residual of `v` against the pivot rows of `R`: at each column,
subtract the pivot-row coefficients times the rows. -/
def rrefResidual (R : FreeMatrix K m n) (v : FreeMod K n) : FreeMod K n :=
  fun c => v c - ∑ a ∈ finFinset _, rrefCoeff R v a * R a c
-- Reference: MRR 1988, Pt. II Ch. 6 (reading the coefficient of a combination
-- at the pivot column of row `a` as the residual coefficient).
/-- The span witness coefficient `d a` equals the residual coefficient
`rrefCoeff R v a` whenever row `a` has a pivot. -/
theorem rrefCoeff_eq_of_lt {R : FreeMatrix K m n} (hR : IsRref R) {v : FreeMod K n}
    {d : Fin m → K} (hd : ∀ j : Fin n, v j = ∑ a ∈ finFinset _, d a * R a j)
    (a : Fin m) (ha : matLeadingCol R a < n) : d a = rrefCoeff R v a := by
  unfold rrefCoeff
  exact Eq.mpr (congrArg (fun z => d a = z) (dite_eq_left ha))
    (((hd _).trans (rref_sum_at_pivot (d := d) hR (b := a)
      (c := ⟨matLeadingCol R a, ha⟩) (Fin.val_mk ha).symm)).symm)
-- Reference: MRR 1988, Pt. II Ch. 6 (the residual coefficient sum equals the
-- witness sum at every column).
/-- The sum of `rrefCoeff` times the rows equals the sum of `d` times the rows. -/
theorem inRowSpan_rref_iff_sum {R : FreeMatrix K m n} (hR : IsRref R) {v : FreeMod K n}
    {d : Fin m → K} (hd : ∀ j : Fin n, v j = ∑ a ∈ finFinset _, d a * R a j) (c : Fin n) :
    (∑ a ∈ finFinset _, rrefCoeff R v a * R a c) = ∑ a ∈ finFinset _, d a * R a c :=
  sum_finFinset_congr (fun a => by
    rcases Nat.lt_or_ge (matLeadingCol R a) n with hlt | hge
    · exact congrArg (· * R a c) (rrefCoeff_eq_of_lt hR hd a hlt).symm
    · have hn : matLeadingCol R a = n := Nat.le_antisymm (matLeadingCol_le R a) hge
      have hz : matRowZero R a := matRowZero_of_matLeadingCol_eq hn
      have h0 : (0 : K) * R a c = d a * R a c :=
        (zero_mul (R a c)).trans ((congrArg (d a * ·) (hz c)).trans (mul_zero _)).symm
      unfold rrefCoeff
      exact Eq.mpr (congrArg (fun z => z * R a c = d a * R a c)
        (dite_eq_right (Nat.not_lt.mpr hge))) h0)
-- Reference: MRR 1988, Pt. II Ch. 6 (membership in the row span of an RREF
-- matrix iff the residual against the pivot rows vanishes; the forward
-- direction evaluates the combination at each pivot column).
-- Reference: MRR 1988, Pt. II Ch. 6 (membership iff residual vanishes); the
-- forward step at a column.
/-- If `v` is a combination with coefficients `d`, the residual at `c` is
zero. -/
theorem inRowSpan_rref_iff_fwd {R : FreeMatrix K m n} (hR : IsRref R) {v : FreeMod K n}
    {d : Fin m → K} (hd : ∀ j : Fin n, v j = ∑ a ∈ finFinset _, d a * R a j) (c : Fin n) :
    rrefResidual R v c = 0 :=
  let e1 : v c = ∑ a ∈ finFinset _, d a * R a c := hd c
  let hsum2 := inRowSpan_rref_iff_sum hR hd c
  (congrArg (v c - ·) hsum2).trans
    (Eq.mpr (congrArg (fun z => z - ∑ a ∈ finFinset _, d a * R a c = 0) e1) (sub_self _))
-- Reference: MRR 1988, Pt. II Ch. 6 (membership in the row span of an RREF
-- matrix iff the residual against the pivot rows vanishes; the forward
-- direction evaluates the combination at each pivot column).
/-- `v` lies in the row span of the RREF matrix `R` iff its residual against
the pivot rows of `R` vanishes. -/
theorem inRowSpan_rref_iff {R : FreeMatrix K m n} (hR : IsRref R) (v : FreeMod K n) :
    inRowSpan R v ↔ ∀ c : Fin n, rrefResidual R v c = 0 :=
  ⟨fun h => by
      let ⟨d, hd⟩ := h
      intro c
      exact inRowSpan_rref_iff_fwd hR hd c,
    fun h => ⟨rrefCoeff R v, fun c => by
      have hc := h c
      unfold rrefResidual at hc
      exact sub_eq_zero.mp hc⟩⟩
-- Reference: MRR 1988, Pt. II Ch. 6 (reading the `≠ 0` test off a `false`
-- conjunction disjunct).
-- Reference: MRR 1988, Pt. II Ch. 6 (reading the `≠ 0` test off a `false`
-- conjunction disjunct); the `x = 0` step.
/-- If the `≠ 0` test is `false`, then `x = 0`. -/
theorem mul_eq_zero_of_and_false_x {x : K}
    (h1 : (if x ≠ 0 then true else false) = false) : x = 0 := by
  cases (inferInstance : Decidable (x ≠ 0)) with
  | isTrue hne =>
      have ht : (if x ≠ 0 then true else false) = true := ite_eq_left hne
      exact absurd (Eq.mp (congrArg (· = false) ht) h1) Bool.false_ne_true.symm
  | isFalse hnne =>
      cases (inferInstance : Decidable (x = 0)) with
      | isTrue h0 => exact h0
      | isFalse h2' => exact absurd (fun heq => h2' heq) hnne
-- Reference: MRR 1988, Pt. II Ch. 6 (reading the `≠ 0` test off a `false`
-- conjunction disjunct); the row-zero step.
/-- If the row-nonzero test is `false`, the row is zero. -/
theorem mul_eq_zero_of_and_false_row {B : FreeMatrix K m n} {a : Fin m}
    (h2 : matRowNonzeroBool B a = false) : matRowZero B a := by
  cases hs : findPivotRow (fun c => if B a c ≠ 0 then true else false) n 0 with
  | none => exact rowZero_of_findPivotRow_eq_none hs
  | some c =>
      have h2' : (some c).isSome = false :=
        (congrArg Option.isSome hs).symm.trans
          (h2 : (findPivotRow (fun c => if B a c ≠ 0 then true else false) n 0).isSome = false)
      exact absurd h2' (fun h => Bool.false_ne_true (h.symm.trans (Option.isSome_some (a := c))))
-- Reference: MRR 1988, Pt. II Ch. 6 (reading the `≠ 0` test off a `false`
-- conjunction disjunct).
/-- If the conjunction `(x ≠ 0 test) && (row nonzero test)` is `false`, then
`x * B a c = 0`. -/
theorem mul_eq_zero_of_and_false {x : K} {B : FreeMatrix K m n} {a : Fin m}
    (h : ((if x ≠ 0 then true else false) && matRowNonzeroBool B a) = false) (c : Fin n) :
    x * B a c = 0 :=
  match Bool.and_eq_false_iff.mp h with
  | Or.inl h1 =>
      let hx := mul_eq_zero_of_and_false_x h1
      (congrArg (· * B a c) hx).trans (zero_mul (B a c))
  | Or.inr h2 =>
      let hz := mul_eq_zero_of_and_false_row h2
      (congrArg (x * ·) (hz c)).trans (mul_zero x)
-- Reference: MRR 1988, Pt. II Ch. 6 (the leading column of a nonzero element
-- of the row span of an RREF matrix is a pivot column); vanishing step.
/-- Left of the pivot column of the first nonzero row of the combination, the
combination vanishes. -/
theorem exists_matLeadingCol_eq_vecLeadingCol_vanish {R : FreeMatrix K m n} (hR : IsRref R)
    {w : FreeMod K n} {d : Fin m → K}
    (hd : ∀ j : Fin n, w j = ∑ a ∈ finFinset _, d a * R a j)
    {ast : Fin m}
    (hs : findPivotRow (fun a => (if d a ≠ 0 then true else false) && matRowNonzeroBool R a)
      m 0 = some ast)
    (c : Fin n) (hc : c.val < matLeadingCol R ast) :
    w c = 0 := by
  let ⟨_, _, hR3, _⟩ := hR
  have e : w c = ∑ a ∈ finFinset _, d a * R a c := hd c
  refine Eq.mp (congrArg (fun z => z = 0) e.symm) (sum_finFinset_eq_zero (fun a => ?_))
  rcases Nat.lt_or_ge a.val ast.val with hlt | hge
  · exact mul_eq_zero_of_and_false (findPivotRow_some_first hs a (Nat.zero_le a.val) hlt) c
  · rcases Nat.lt_or_ge ast.val a.val with hlt2 | hge2
    · cases hs3 : findPivotRow (fun c => if R a c ≠ 0 then true else false) n 0 with
      | none =>
          exact (congrArg (d a * ·) (rowZero_of_findPivotRow_eq_none hs3 c)).trans (mul_zero (d a))
      | some c3 =>
          have hnb : ¬ matRowZero R a := fun hz =>
            ne_zero_of_pivotBool (findPivotRow_some_spec hs3).2.2 (hz c3)
          have hlt3 : matLeadingCol R ast < matLeadingCol R a :=
            hR3 ast a (Fin.lt_def.mpr hlt2) hnb
          exact (congrArg (d a * ·) (entry_eq_zero_of_lt_matLeadingCol (Nat.lt_trans hc hlt3))).trans
            (mul_zero (d a))
    · have heq : a = ast := Fin.eq_of_val_eq (Nat.le_antisymm hge2 hge)
      exact Eq.mpr (congrArg (fun z => d z * R z c = 0) heq)
        ((congrArg (d ast * ·) (entry_eq_zero_of_lt_matLeadingCol hc)).trans (mul_zero (d ast)))
-- Reference: MRR 1988, Pt. II Ch. 6 (the leading column of a nonzero element
-- of the row span of an RREF matrix is a pivot column); nonzero step.
/-- At the pivot column of the first nonzero row of the combination, the
combination is nonzero. -/
theorem exists_matLeadingCol_eq_vecLeadingCol_ne {R : FreeMatrix K m n} (hR : IsRref R)
    {w : FreeMod K n} {d : Fin m → K}
    (hd : ∀ j : Fin n, w j = ∑ a ∈ finFinset _, d a * R a j)
    {ast : Fin m}
    (hs : findPivotRow (fun a => (if d a ≠ 0 then true else false) && matRowNonzeroBool R a)
      m 0 = some ast)
    (hlc_lt : matLeadingCol R ast < n) :
    w ⟨matLeadingCol R ast, hlc_lt⟩ ≠ 0 := by
  have hspec := findPivotRow_some_spec hs
  rcases Bool.and_eq_true_iff.mp hspec.2.2 with ⟨hdne, hrow⟩
  have e2 := rref_sum_at_pivot (d := d) hR (b := ast) (c := ⟨matLeadingCol R ast, hlc_lt⟩)
    (Fin.val_mk hlc_lt).symm
  have e : w ⟨matLeadingCol R ast, hlc_lt⟩ = d ast := (hd _).trans e2
  exact fun h => ne_zero_of_pivotBool hdne (Eq.mpr (congrArg (· = 0) e.symm) h)
-- Reference: MRR 1988, Pt. II Ch. 6 (the leading column of a nonzero element
-- of the row span of an RREF matrix is a pivot column: take the first row
-- with a nonzero coefficient).
-- Reference: MRR 1988, Pt. II Ch. 6 (the leading column of a nonzero element
-- of the row span is a pivot column); the no-pivot case.
/-- If the combined search finds no row, the combination is zero,
contradicting `w ≠ 0`. -/
theorem exists_matLeadingCol_eq_vecLeadingCol_none {R : FreeMatrix K m n}
    {w : FreeMod K n} {d : Fin m → K} (hd : ∀ j : Fin n, w j = ∑ a ∈ finFinset _, d a * R a j)
    (hw0 : w ≠ 0)
    (hs : findPivotRow (fun a => (if d a ≠ 0 then true else false) && matRowNonzeroBool R a)
      m 0 = none) : ∃ b : Fin m, ¬ matRowZero R b ∧ matLeadingCol R b = vecLeadingCol w :=
  let hzero : ∀ a : Fin m, ∀ c : Fin n, d a * R a c = 0 := fun a c =>
    mul_eq_zero_of_and_false
      (findPivotRow_none_spec hs a (Nat.zero_le a.val)
        (Eq.subst (Nat.zero_add m).symm a.isLt)) c
  absurd (funext (fun c => (hd c).trans (sum_finFinset_eq_zero (fun a => hzero a c)))) hw0
-- Reference: MRR 1988, Pt. II Ch. 6 (the leading column of a nonzero element
-- of the row span is a pivot column); the leading column of a nonzero row.
/-- The leading column of a nonzero row `ast` of `R` is `< n`. -/
theorem exists_matLeadingCol_eq_vecLeadingCol_lt {R : FreeMatrix K m n} {ast : Fin m}
    (hrow' : ¬ matRowZero R ast) :
    matLeadingCol R ast < n := by
  cases hs2 : findPivotRow (fun c => if R ast c ≠ 0 then true else false) n 0 with
  | none => exact absurd (rowZero_of_findPivotRow_eq_none hs2) hrow'
  | some c => exact Eq.mpr (congrArg (· < n) (matLeadingCol_eq_some hs2)) c.isLt
theorem exists_matLeadingCol_eq_vecLeadingCol {R : FreeMatrix K m n} (hR : IsRref R)
    {w : FreeMod K n} (hw : inRowSpan R w) (hw0 : w ≠ 0) :
    ∃ b : Fin m, ¬ matRowZero R b ∧ matLeadingCol R b = vecLeadingCol w := by
  let ⟨d, hd⟩ := hw
  cases hs : findPivotRow
      (fun a => (if d a ≠ 0 then true else false) && matRowNonzeroBool R a) m 0 with
  | none => exact exists_matLeadingCol_eq_vecLeadingCol_none hd hw0 hs
  | some ast =>
      let hspec := findPivotRow_some_spec hs
      let ⟨hdne, hrow⟩ := Bool.and_eq_true_iff.mp hspec.2.2
      let hrow' : ¬ matRowZero R ast := matRowNonzeroBool_true.mp hrow
      let hlc_lt : matLeadingCol R ast < n :=
        exists_matLeadingCol_eq_vecLeadingCol_lt hrow'
      let hvan : ∀ c : Fin n, c.val < matLeadingCol R ast → w c = 0 :=
        fun c hc => exists_matLeadingCol_eq_vecLeadingCol_vanish hR hd hs c hc
      let hne : w ⟨matLeadingCol R ast, hlc_lt⟩ ≠ 0 :=
        exists_matLeadingCol_eq_vecLeadingCol_ne hR hd hs hlc_lt
      let hlcw : vecLeadingCol w = matLeadingCol R ast :=
        vecLeadingCol_eq_of_zero_before hlc_lt hvan hne
      exact ⟨ast, hrow', hlcw.symm⟩
end BoringMath
