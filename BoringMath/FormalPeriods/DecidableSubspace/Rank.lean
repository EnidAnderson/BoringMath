/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Init
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Fin.Basic
import BoringMath.FormalPeriods.DecidableSubspace.Sums
import BoringMath.FormalPeriods.DecidableSubspace.RowSpan
import BoringMath.FormalPeriods.DecidableSubspace.Pivots
import BoringMath.FormalPeriods.FreeMod
import BoringMath.FormalPeriods.RowReduction
/-!
# Nonzero-row counting: the computed rank (P.2.3, part 4)

Piece 4 of `BoringMath.FormalPeriods.DecidableSubspace`: `matRowNonzeroBool`,
`nzCount`, `matTail`, and the counting lemmas for an RREF matrix whose first
row is zero or nonzero.
-/
universe u
namespace BoringMath
variable {K : Type u} [Field K] {m n k p : ℕ}
variable [DecidableEq K]
/-! ## Nonzero-row counting (the computed rank) -/
-- Reference: MRR 1988, Pt. II Ch. 6 (deciding whether a row is zero over a
-- discrete field is a finite search for a nonzero entry).
/-- A row is nonzero iff the pivot search in it finds a column; a `Bool`. -/
def matRowNonzeroBool (B : FreeMatrix K m n) (a : Fin m) : Bool :=
  (findPivotRow (fun c => if B a c ≠ 0 then true else false) n 0).isSome
-- Reference: MRR 1988, Pt. II Ch. 6 (soundness of the search).
-- Reference: MRR 1988, Pt. II Ch. 6 (soundness of the search); the `none` case.
/-- If the search of row `a` finds nothing, the row is zero, contradicting the
test. -/
theorem matRowNonzeroBool_true_none {B : FreeMatrix K m n} {a : Fin m}
    (hs : findPivotRow (fun c => if B a c ≠ 0 then true else false) n 0 = none)
    (h : ¬ matRowZero B a) : matRowNonzeroBool B a = true :=
  absurd (rowZero_of_findPivotRow_eq_none hs) h
-- Reference: MRR 1988, Pt. II Ch. 6 (soundness of the search); the `some` case.
/-- If the search of row `a` finds `c`, the test is `true`. -/
theorem matRowNonzeroBool_true_some {B : FreeMatrix K m n} {a : Fin m} {c : Fin n}
    (hs : findPivotRow (fun c => if B a c ≠ 0 then true else false) n 0 = some c) :
    matRowNonzeroBool B a = true :=
  (congrArg Option.isSome hs).trans (Option.isSome_some (a := c))
-- Reference: MRR 1988, Pt. II Ch. 6 (soundness of the search).
/-- The nonzero test says `true` iff the row is not zero. -/
theorem matRowNonzeroBool_true {B : FreeMatrix K m n} {a : Fin m} :
    matRowNonzeroBool B a = true ↔ ¬ matRowZero B a :=
  ⟨fun h hzero =>
      absurd ((congrArg Option.isSome (findPivotRow_eq_none_of_rowZero hzero)).symm.trans h)
        Bool.false_ne_true,
    fun h => by
      cases hs : findPivotRow (fun c => if B a c ≠ 0 then true else false) n 0 with
      | none => exact matRowNonzeroBool_true_none hs h
      | some c => exact matRowNonzeroBool_true_some hs⟩
-- Reference: MRR 1988, Pt. II Ch. 6 (completeness of the search).
/-- A zero row tests `false`. -/
theorem matRowNonzeroBool_false_of_rowZero {B : FreeMatrix K m n} {a : Fin m}
    (h : matRowZero B a) : matRowNonzeroBool B a = false := by
  unfold matRowNonzeroBool
  exact (congrArg Option.isSome (findPivotRow_eq_none_of_rowZero h)).trans Option.isSome_none
-- Reference: MRR 1988, Pt. II Ch. 6 (rows with equal entries test equally).
/-- The nonzero test is a congruence on the row entries. -/
theorem matRowNonzeroBool_congr {p q : ℕ} {A : FreeMatrix K p n} {B : FreeMatrix K q n}
    {a : Fin p} {b : Fin q}
    (h : ∀ c, A a c = B b c) :
    matRowNonzeroBool A a = matRowNonzeroBool B b := by
  unfold matRowNonzeroBool
  exact congrArg Option.isSome (findPivotRow_congr
    (fun c => congrArg (fun x => if x ≠ 0 then true else false) (h c)) n 0)
-- Reference: MRR 1988, Pt. II Ch. 6 (the rank is the number of nonzero rows
-- of the normal form; here the count over any matrix).
/-- The number of nonzero rows of `B`, computed by counting. -/
def nzCount (B : FreeMatrix K m n) : ℕ :=
  (List.finRange m).countP (fun a => matRowNonzeroBool B a)
-- Reference: MRR 1988, Pt. II Ch. 6 (dropping the last row of a `snoc`).
-- Reference: MRR 1988, Pt. II Ch. 6 (dropping the last row of a `snoc`); the
-- last row is zero.
/-- The last row of `matSnoc A 0` is the zero row. -/
theorem nzCount_snoc_zero_hz (A : FreeMatrix K m n) :
    matRowZero (matSnoc A 0) (Fin.last m) :=
  fun c => (matSnoc_last A 0 c).trans (Pi.zero_apply c)
-- Reference: MRR 1988, Pt. II Ch. 6 (dropping the last row of a `snoc`); the
-- last row tests `false`.
/-- The last row of `matSnoc A 0` tests `false`. -/
theorem nzCount_snoc_zero_hb (A : FreeMatrix K m n) :
    matRowNonzeroBool (matSnoc A 0) (Fin.last m) = false :=
  matRowNonzeroBool_false_of_rowZero (nzCount_snoc_zero_hz A)
-- Reference: MRR 1988, Pt. II Ch. 6 (dropping the last row of a `snoc`); the
-- count over the `castSucc` rows agrees.
/-- The nonzero-test predicate of `matSnoc A 0` composed with `castSucc` is
that of `A`. -/
theorem nzCount_snoc_zero_hcomp (A : FreeMatrix K m n) :
    (fun a => matRowNonzeroBool (matSnoc A 0) a) ∘ Fin.castSucc
      = fun a => matRowNonzeroBool A a :=
  funext (fun a => matRowNonzeroBool_congr (A := matSnoc A 0) (B := A)
    (a := Fin.castSucc a) (b := a) (fun c => matSnoc_castSucc A 0 a c))
-- Reference: MRR 1988, Pt. II Ch. 6 (dropping the last row of a `snoc`); the
-- singleton contributes zero.
/-- The singleton list `[Fin.last m]` contributes zero to the count. -/
theorem nzCount_snoc_zero_hlast (A : FreeMatrix K m n) :
    List.countP (fun a => matRowNonzeroBool (matSnoc A 0) a) [Fin.last m] = 0 :=
  (List.countP_cons_of_neg
    (fun h => Bool.false_ne_true ((nzCount_snoc_zero_hb A).symm.trans h))).trans
    List.countP_nil
-- Reference: MRR 1988, Pt. II Ch. 6 (dropping the last row of a `snoc`).
/-- Appending a zero row does not change the nonzero-row count. -/
theorem nzCount_snoc_zero (A : FreeMatrix K m n) : nzCount (matSnoc A 0) = nzCount A := by
  unfold nzCount
  exact ((congrArg (List.countP (fun a => matRowNonzeroBool (matSnoc A 0) a))
      List.finRange_succ_last).trans (List.countP_append (p := fun a => matRowNonzeroBool (matSnoc A 0) a)
        (l₁ := (List.finRange m).map Fin.castSucc) (l₂ := [Fin.last m]))).trans
    (((congrArg (· + List.countP (fun a => matRowNonzeroBool (matSnoc A 0) a) [Fin.last m])
        (List.countP_map (p := fun a => matRowNonzeroBool (matSnoc A 0) a) (f := Fin.castSucc)
          (l := List.finRange m))).trans
    ((congrArg (fun g => List.countP g (List.finRange m)
        + List.countP (fun a => matRowNonzeroBool (matSnoc A 0) a) [Fin.last m])
        (nzCount_snoc_zero_hcomp A)).trans
    ((congrArg (List.countP (fun a => matRowNonzeroBool A a) (List.finRange m) + ·)
        (nzCount_snoc_zero_hlast A)).trans
    (Nat.add_zero _)))))
-- Reference: MRR 1988, Pt. II Ch. 6 (the tail matrix: all rows but the first).
/-- The tail of a matrix: rows `1, ...` as a matrix with one row fewer. -/
def matTail (R : FreeMatrix K (k + 1) n) : FreeMatrix K k n := fun a => R (Fin.succ a)
-- Reference: definitional peel of `matTail`.
/-- Pointwise unfolding of `matTail`. -/
theorem matRowNonzeroBool_tail (R : FreeMatrix K (k + 1) n) (a : Fin k) :
    matRowNonzeroBool (matTail R) a = matRowNonzeroBool R (Fin.succ a) :=
  rfl
-- Reference: MRR 1988, Pt. II Ch. 6 (counting with the first row peeled off).
-- Reference: MRR 1988, Pt. II Ch. 6 (counting with the first row peeled off).
/-- If row `0` is nonzero, the count is one plus the count of the tail. -/
theorem nzCount_succ_eq (R : FreeMatrix K (k + 1) n) (h : ¬ matRowZero R 0) :
    nzCount R = nzCount (matTail R) + 1 := by
  unfold nzCount
  let hcomp : (fun a => matRowNonzeroBool R a) ∘ Fin.succ
      = fun a => matRowNonzeroBool (matTail R) a :=
    funext (fun a => (matRowNonzeroBool_tail R a).symm)
  let hb : matRowNonzeroBool R 0 = true := matRowNonzeroBool_true.mpr h
  let e1 := congrArg (List.countP (fun a => matRowNonzeroBool R a)) List.finRange_succ
  let e2 := List.countP_cons (p := fun a => matRowNonzeroBool R a) (a := 0)
    (l := (List.finRange k).map Fin.succ)
  let e3 := congrArg (· + if matRowNonzeroBool R 0 then 1 else 0)
    (List.countP_map (p := fun a => matRowNonzeroBool R a) (f := Fin.succ) (l := List.finRange k))
  let e4 := congrArg (fun g => List.countP g (List.finRange k)
      + if matRowNonzeroBool R 0 then 1 else 0) hcomp
  let e5 : (if matRowNonzeroBool R 0 then 1 else 0) = 1 := ite_eq_left hb
  exact ((e1.trans e2).trans e3).trans (e4.trans (congrArg _ e5))
-- Reference: MRR 1988, Pt. II Ch. 6 (zero rows sit at the bottom, so a zero
-- first row makes the whole matrix zero).
-- Reference: MRR 1988, Pt. II Ch. 6 (zero rows sit at the bottom); all rows are
-- zero if row `0` is.
/-- If row `0` of an RREF matrix is zero, every row is zero. -/
theorem nzCount_eq_zero_of_rowZero_zero_all {R : FreeMatrix K (k + 1) n} (hR : IsRref R)
    (hz : matRowZero R 0) : ∀ a : Fin (k + 1), matRowZero R a :=
  let ⟨h1, _, _, _⟩ := hR
  fun a =>
    match Fin.eq_zero_or_eq_succ a with
    | Or.inl h => Eq.mpr (congrArg (fun z => matRowZero R z) h) hz
    | Or.inr ⟨j, h⟩ => Eq.mpr (congrArg (fun z => matRowZero R z) h)
        (h1 0 (Fin.succ j) (Fin.succ_pos j) hz)
-- Reference: MRR 1988, Pt. II Ch. 6 (zero rows sit at the bottom, so a zero
-- first row makes the whole matrix zero).
/-- If row `0` is zero in an RREF matrix, all rows are zero and the count is
`0`. -/
theorem nzCount_eq_zero_of_rowZero_zero {R : FreeMatrix K (k + 1) n} (hR : IsRref R)
    (hz : matRowZero R 0) : nzCount R = 0 := by
  unfold nzCount
  exact list_countP_eq_zero (fun a _ =>
    Bool.eq_false_iff.mp
      (matRowNonzeroBool_false_of_rowZero (nzCount_eq_zero_of_rowZero_zero_all hR hz a)))
-- Reference: MRR 1988, Pt. II Ch. 6 (a nonzero first row contributes).
/-- If row `0` is nonzero, the count is positive. -/
theorem nzCount_pos_of_not_rowZero_zero {R : FreeMatrix K (k + 1) n} (h : ¬ matRowZero R 0) :
    0 < nzCount R := by
  unfold nzCount
  exact List.countP_pos_iff.mpr ⟨0, List.mem_finRange 0, matRowNonzeroBool_true.mpr h⟩
end BoringMath
