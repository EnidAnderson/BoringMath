/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Init
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Fin.Basic
import BoringMath.FormalPeriods.DecidableSubspace.RowSpan
import BoringMath.FormalPeriods.DecidableSubspace.Pivots
import BoringMath.FormalPeriods.DecidableSubspace.Rank
import BoringMath.FormalPeriods.FreeMod
import BoringMath.FormalPeriods.RowReduction
/-!
# RREF is preserved by tails and by appending a zero row (P.2.3, part 6)

Piece 6 of `BoringMath.FormalPeriods.DecidableSubspace`: `IsRref` is inherited
by `matTail` and by `matSnoc R 0`.
-/
universe u
namespace BoringMath
variable {K : Type u} [Field K] {m n k p : ℕ}
variable [DecidableEq K]
/-! ## RREF is preserved by tails and by appending a zero row -/
-- Reference: MRR 1988, Pt. II Ch. 6 (dropping the first row of an RREF matrix).
-- Reference: MRR 1988, Pt. II Ch. 6 (dropping the first row of an RREF matrix).
/-- The tail of an RREF matrix is in RREF. -/
theorem isRref_matTail {R : FreeMatrix K (k + 1) n} (hR : IsRref R) : IsRref (matTail R) :=
  let ⟨h1, h2, h3, h4⟩ := hR
  ⟨fun a b hab hza c => h1 (Fin.succ a) (Fin.succ b) (Fin.succ_lt_succ_iff.mpr hab) hza c,
   fun a c hlc => h2 (Fin.succ a) c hlc,
   fun a b hab hnb => h3 (Fin.succ a) (Fin.succ b) (Fin.succ_lt_succ_iff.mpr hab) hnb,
   fun a b hne c hlc => h4 (Fin.succ a) (Fin.succ b) (fun h => hne (Fin.succ_inj.mp h)) c hlc⟩
-- Reference: MRR 1988, Pt. II Ch. 6 (appending a zero row at the bottom of an
-- RREF matrix keeps it in RREF: zero rows sit at the bottom).
-- Reference: MRR 1988, Pt. II Ch. 6 (appending a zero row); the last row of
-- `matSnoc R 0` is zero.
/-- The last row of `matSnoc R 0` is the zero row. -/
theorem isRref_snoc_zero_last {R : FreeMatrix K m n} (hR : IsRref R) :
    matRowZero (matSnoc R 0) (Fin.last m) :=
  fun c => (matSnoc_last R 0 c).trans (Pi.zero_apply c)
-- Reference: MRR 1988, Pt. II Ch. 6 (appending a zero row); leading column of
-- the zero last row.
/-- The leading column of the zero last row of `matSnoc R 0` is `n`. -/
theorem isRref_snoc_zero_hlc_last {R : FreeMatrix K m n}
    (hz : matRowZero (matSnoc R 0) (Fin.last m)) :
    matLeadingCol (matSnoc R 0) (Fin.last m) = n :=
  matLeadingCol_eq_of_rowZero _ _ hz
-- Reference: MRR 1988, Pt. II Ch. 6 (appending a zero row); leading columns of
-- the old rows are unchanged.
/-- The leading column of a `castSucc` row of `matSnoc R 0` is that of `R`. -/
theorem isRref_snoc_zero_hlc_cast {R : FreeMatrix K m n} (a : Fin m) :
    matLeadingCol (matSnoc R 0) (Fin.castSucc a) = matLeadingCol R a :=
  matLeadingCol_congr (A := matSnoc R 0) (B := R) (a := Fin.castSucc a) (b := a)
    (fun c => matSnoc_castSucc R 0 a c)
-- Reference: MRR 1988, Pt. II Ch. 6 (appending a zero row); zero-row test of
-- the old rows is unchanged.
/-- Zero-rowedness of a `castSucc` row of `matSnoc R 0` matches `R`. -/
theorem isRref_snoc_zero_hz_cast {R : FreeMatrix K m n} (a : Fin m) :
    matRowZero (matSnoc R 0) (Fin.castSucc a) ↔ matRowZero R a :=
  ⟨fun h c => Eq.mp (congrArg (fun z => z = 0) (matSnoc_castSucc R 0 a c)) (h c),
    fun h c => Eq.mpr (congrArg (fun z => z = 0) (matSnoc_castSucc R 0 a c)) (h c)⟩
-- Reference: MRR 1988, Pt. II Ch. 6 (appending a zero row); clause 1: zero rows
-- sit at the bottom.
/-- Clause 1 of RREF for `matSnoc R 0`: zero rows sit at the bottom. -/
theorem isRref_snoc_zero_c1 {R : FreeMatrix K m n}
    (h1 : ∀ a b : Fin m, a < b → matRowZero R a → matRowZero R b)
    (hz_cast : ∀ a : Fin m, matRowZero (matSnoc R 0) (Fin.castSucc a) ↔ matRowZero R a)
    (hlc_cast : ∀ a : Fin m, matLeadingCol (matSnoc R 0) (Fin.castSucc a) = matLeadingCol R a)
    (hz : matRowZero (matSnoc R 0) (Fin.last m)) :
    ∀ a b : Fin (m + 1), a < b → matRowZero (matSnoc R 0) a →
      ∀ c : Fin n, matSnoc R 0 b c = 0 := by
  intro a b hab hza c
  rcases Fin.eq_castSucc_or_eq_last b with ⟨b', hb⟩ | hb
  · rcases Fin.eq_castSucc_or_eq_last a with ⟨a', ha⟩ | ha
    · have hab' : a' < b' := Fin.castSucc_lt_castSucc_iff.mp
        (Eq.mp (congrArg (Fin.castSucc a' < ·) hb) (Eq.mp (congrArg (· < b) ha) hab))
      exact ((congrArg (fun z => matSnoc R 0 z c) hb).trans (matSnoc_castSucc R 0 b' c)).trans
        (h1 a' b' hab' ((hz_cast a').mp
          (Eq.mp (congrArg (fun z => matRowZero (matSnoc R 0) z) ha) hza)) c)
    · exact absurd (Eq.mp (congrArg (Fin.last m < ·) hb) (Eq.mp (congrArg (· < b) ha) hab))
        (Fin.not_lt.mpr (Fin.le_of_lt (Fin.castSucc_lt_last b')))
  · exact Eq.mpr (congrArg (fun z => matSnoc R 0 z c = 0) hb) (hz c)
-- Reference: MRR 1988, Pt. II Ch. 6 (appending a zero row); clause 2: pivot
-- entries are `1`.
/-- Clause 2 of RREF for `matSnoc R 0`: pivot entries are `1`. -/
theorem isRref_snoc_zero_c2 {R : FreeMatrix K m n}
    (h2 : ∀ a : Fin m, ∀ c : Fin n, matLeadingCol R a = c.val → R a c = 1)
    (hlc_cast : ∀ a : Fin m, matLeadingCol (matSnoc R 0) (Fin.castSucc a) = matLeadingCol R a)
    (hlc_last : matLeadingCol (matSnoc R 0) (Fin.last m) = n) :
    ∀ a : Fin (m + 1), ∀ c : Fin n, matLeadingCol (matSnoc R 0) a = c.val →
      matSnoc R 0 a c = 1 := by
  intro a c hlc
  rcases Fin.eq_castSucc_or_eq_last a with ⟨a', ha⟩ | ha
  · have hlc' : matLeadingCol R a' = c.val :=
      Eq.mp (congrArg (fun z => z = c.val) (hlc_cast a'))
        (Eq.mp (congrArg (fun z => matLeadingCol (matSnoc R 0) z = c.val) ha) hlc)
    exact (Eq.mpr (congrArg (fun z => matSnoc R 0 z c = R a' c) ha) (matSnoc_castSucc R 0 a' c)).trans
      (h2 a' c hlc')
  · exact absurd c.isLt (Nat.not_lt.mpr (Nat.le_of_eq
      (Eq.mp (congrArg (· = c.val) hlc_last)
        (Eq.mp (congrArg (fun z => matLeadingCol (matSnoc R 0) z = c.val) ha) hlc))))
-- Reference: MRR 1988, Pt. II Ch. 6 (appending a zero row); clause 3: leading
-- columns strictly increase.
/-- Clause 3 of RREF for `matSnoc R 0`: leading columns strictly increase. -/
theorem isRref_snoc_zero_c3 {R : FreeMatrix K m n}
    (h3 : ∀ a b : Fin m, a < b → ¬ matRowZero R b → matLeadingCol R a < matLeadingCol R b)
    (hlc_cast : ∀ a : Fin m, matLeadingCol (matSnoc R 0) (Fin.castSucc a) = matLeadingCol R a)
    (hz : matRowZero (matSnoc R 0) (Fin.last m))
    (hz_cast : ∀ a : Fin m, matRowZero (matSnoc R 0) (Fin.castSucc a) ↔ matRowZero R a) :
    ∀ a b : Fin (m + 1), a < b → ¬ matRowZero (matSnoc R 0) b →
      matLeadingCol (matSnoc R 0) a < matLeadingCol (matSnoc R 0) b := by
  intro a b hab hnb
  rcases Fin.eq_castSucc_or_eq_last b with ⟨b', hb⟩ | hb
  · rcases Fin.eq_castSucc_or_eq_last a with ⟨a', ha⟩ | ha
    · have hab' : a' < b' := Fin.castSucc_lt_castSucc_iff.mp
        (Eq.mp (congrArg (Fin.castSucc a' < ·) hb) (Eq.mp (congrArg (· < b) ha) hab))
      have hnb' : ¬ matRowZero R b' := mt (hz_cast b').mpr
        (Eq.mp (congrArg (fun z => ¬ matRowZero (matSnoc R 0) z) hb) hnb)
      have eq := congrArg₂ (· < ·)
        ((congrArg (fun z => matLeadingCol (matSnoc R 0) z) ha).trans (hlc_cast a'))
        ((congrArg (fun z => matLeadingCol (matSnoc R 0) z) hb).trans (hlc_cast b'))
      exact Eq.mpr eq (h3 a' b' hab' hnb')
    · exact absurd (Eq.mp (congrArg (Fin.last m < ·) hb) (Eq.mp (congrArg (· < b) ha) hab))
        (Fin.not_lt.mpr (Fin.le_of_lt (Fin.castSucc_lt_last b')))
  · exact absurd hz (Eq.mp (congrArg (fun z => ¬ matRowZero (matSnoc R 0) z) hb) hnb)
-- Reference: MRR 1988, Pt. II Ch. 6 (appending a zero row); clause 4: pivot
-- columns are zero in every other row.
/-- Clause 4 of RREF for `matSnoc R 0`: pivot columns vanish off-pivot. -/
theorem isRref_snoc_zero_c4 {R : FreeMatrix K m n}
    (h4 : ∀ a b : Fin m, a ≠ b → ∀ c : Fin n, matLeadingCol R a = c.val → R b c = 0)
    (hlc_cast : ∀ a : Fin m, matLeadingCol (matSnoc R 0) (Fin.castSucc a) = matLeadingCol R a)
    (hlc_last : matLeadingCol (matSnoc R 0) (Fin.last m) = n) :
    ∀ a b : Fin (m + 1), a ≠ b → ∀ c : Fin n, matLeadingCol (matSnoc R 0) a = c.val →
      matSnoc R 0 b c = 0 := by
  intro a b hne c hlc
  rcases Fin.eq_castSucc_or_eq_last a with ⟨a', ha⟩ | ha
  · have hlc' : matLeadingCol R a' = c.val :=
      Eq.mp (congrArg (fun z => z = c.val) (hlc_cast a'))
        (Eq.mp (congrArg (fun z => matLeadingCol (matSnoc R 0) z = c.val) ha) hlc)
    rcases Fin.eq_castSucc_or_eq_last b with ⟨b', hb⟩ | hb
    · have hne' : a' ≠ b' := fun h => hne (ha.trans ((congrArg Fin.castSucc h).trans hb.symm))
      exact (Eq.mpr (congrArg (fun z => matSnoc R 0 z c = R b' c) hb) (matSnoc_castSucc R 0 b' c)).trans
        (h4 a' b' hne' c hlc')
    · exact Eq.mpr (congrArg (fun z => matSnoc R 0 z c = 0) hb)
        ((matSnoc_last R 0 c).trans (Pi.zero_apply c))
  · exact absurd c.isLt (Nat.not_lt.mpr (Nat.le_of_eq
      (Eq.mp (congrArg (· = c.val) hlc_last)
        (Eq.mp (congrArg (fun z => matLeadingCol (matSnoc R 0) z = c.val) ha) hlc))))
-- Reference: MRR 1988, Pt. II Ch. 6 (appending a zero row at the bottom of an
-- RREF matrix keeps it in RREF: zero rows sit at the bottom).
-- Reference: MRR 1988, Pt. II Ch. 6 (appending a zero row at the bottom of an
-- RREF matrix keeps it in RREF: zero rows sit at the bottom).
/-- Appending a zero row to an RREF matrix keeps it in RREF. -/
theorem isRref_snoc_zero {R : FreeMatrix K m n} (hR : IsRref R) :
    IsRref (matSnoc R 0) :=
  let ⟨h1, h2, h3, h4⟩ := hR
  let hz := isRref_snoc_zero_last hR
  let hlc_last := isRref_snoc_zero_hlc_last hz
  let hlc_cast := isRref_snoc_zero_hlc_cast (R := R)
  let hz_cast := isRref_snoc_zero_hz_cast (R := R)
  ⟨isRref_snoc_zero_c1 h1 hz_cast hlc_cast hz,
   isRref_snoc_zero_c2 h2 hlc_cast hlc_last,
   isRref_snoc_zero_c3 h3 hlc_cast hz hz_cast,
   isRref_snoc_zero_c4 h4 hlc_cast hlc_last⟩
end BoringMath
