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
import BoringMath.FormalPeriods.DecidableSubspace.RrefProps
import BoringMath.FormalPeriods.DecidableSubspace.Residual
import BoringMath.FormalPeriods.FreeMod
import BoringMath.FormalPeriods.RowReduction
/-!
# Uniqueness of the reduced row-echelon form (P.2.3, part 8)

Piece 8 of `BoringMath.FormalPeriods.DecidableSubspace`: one-sided subset
implies equality for RREF matrices (`rref_eq_of_subset_aux`), hence
`rref_eq_of_span_eq` and the rank-counting refinement
`rref_eq_of_subset_nzCount`.
-/
universe u
namespace BoringMath
open BigOperators
variable {K : Type u} [Field K] {m n k p : ℕ}
variable [DecidableEq K]
/-! ## Uniqueness of the reduced row-echelon form -/
-- Reference: MRR 1988, Pt. II Ch. 6 (lifting a combination over the tail to a
-- combination over the whole matrix with zero first coefficient).
/-- A combination over the tail rows lifts to the whole matrix. -/
theorem inRowSpan_matTail_lift {R : FreeMatrix K (k + 1) n} {w : FreeMod K n}
    {e : Fin k → K} (he : ∀ j : Fin n, w j = ∑ a ∈ finFinset k, e a * matTail R a j) :
    inRowSpan R w :=
  ⟨Fin.cases 0 e, fun j => by
    have h2 := sum_finFinset_succ (fun b : Fin (k + 1) => Fin.cases 0 e b * R b j)
    have c0 : Fin.cases 0 e 0 * R 0 j = 0 :=
      (congrArg (· * R 0 j) (Fin.cases_zero (motive := fun _ => K) (zero := (0 : K)) (succ := e))).trans
        (zero_mul (R 0 j))
    have cS : (∑ a ∈ finFinset k, Fin.cases 0 e (Fin.succ a) * R (Fin.succ a) j)
        = ∑ a ∈ finFinset k, e a * R (Fin.succ a) j :=
      sum_finFinset_congr (fun a =>
        congrArg (· * R (Fin.succ a) j) (Fin.cases_succ (motive := fun _ => K) (zero := (0 : K)) (succ := e) a))
    have h2' : (∑ b ∈ finFinset (k + 1), Fin.cases 0 e b * R b j)
        = ∑ a ∈ finFinset k, e a * R (Fin.succ a) j :=
      h2.trans ((congrArg (· + _) c0).trans
        ((congrArg (0 + ·) cS).trans (zero_add _)))
    exact (he j).trans h2'.symm⟩
-- Reference: MRR 1988, Pt. II Ch. 6 (if the tail rows of `R` vanish at
-- column `c`, the combination over the tail vanishes there).
/-- A tail combination vanishes at a column where the tail rows vanish. -/
theorem inRowSpan_matTail_of_subset_wc {R : FreeMatrix K (k + 1) n} {w : FreeMod K n}
    {e : Fin k → K} (he : ∀ j : Fin n, w j = ∑ a ∈ finFinset k, e a * matTail R a j)
    {c : Fin n} (hcR : ∀ a : Fin k, R (Fin.succ a) c = 0) : w c = 0 :=
  Eq.mp (congrArg (fun z => z = 0) (he c).symm)
    (sum_finFinset_eq_zero (fun a => (congrArg (e a * ·) (hcR a)).trans (mul_zero (e a))))
-- Reference: MRR 1988, Pt. II Ch. 6 (evaluating the `S`-combination at the
-- pivot column of row `0` of `S` reads off the first coefficient).
/-- At the pivot column of row `0` of `S`, the `S`-combination equals `f 0`. -/
theorem inRowSpan_matTail_of_subset_f0 {S : FreeMatrix K (k + 1) n}
    (hS2 : ∀ a : Fin (k + 1), ∀ c : Fin n, matLeadingCol S a = c.val → S a c = 1)
    (hS4 : ∀ a b : Fin (k + 1), a ≠ b → ∀ c : Fin n,
      matLeadingCol S a = c.val → S b c = 0)
    {w : FreeMod K n} {f : Fin (k + 1) → K}
    (hf : ∀ j : Fin n, w j = ∑ b ∈ finFinset (k + 1), f b * S b j)
    {c : Fin n} (hlcS : matLeadingCol S 0 = c.val) (hwc : w c = 0) : f 0 = 0 := by
  have e1 : w c = ∑ b ∈ finFinset (k + 1), f b * S b c := hf c
  have hcl : ∀ a : Fin k, S (Fin.succ a) c = 0 := fun a =>
    hS4 0 (Fin.succ a) (Ne.symm (Fin.succ_ne_zero a)) c hlcS
  have hsum : (∑ a ∈ finFinset k, f (Fin.succ a) * S (Fin.succ a) c) = 0 :=
    sum_finFinset_eq_zero (fun a => (congrArg (f (Fin.succ a) * ·) (hcl a)).trans (mul_zero _))
  have h2 : (∑ b ∈ finFinset (k + 1), f b * S b c)
      = f 0 * S 0 c + ∑ a ∈ finFinset k, f (Fin.succ a) * S (Fin.succ a) c :=
    sum_finFinset_succ (fun b : Fin (k + 1) => f b * S b c)
  have e2 : (∑ b ∈ finFinset (k + 1), f b * S b c) = f 0 :=
    h2.trans ((congrArg (· + _) (congrArg (f 0 * ·) (hS2 0 c hlcS))).trans
      ((congrArg (f 0 * 1 + ·) hsum).trans ((add_zero _).trans (mul_one _))))
  exact ((Eq.mp (congrArg (fun z => z = ∑ b ∈ finFinset (k + 1), f b * S b c) hwc) e1).trans e2).symm
-- Reference: MRR 1988, Pt. II Ch. 6 (if the rows of `R` after the first vanish
-- at column `c`, then the span of the tail of `R` injects into the span of
-- the tail of `S` via the coefficient at row `0` of `S`).
-- Reference: MRR 1988, Pt. II Ch. 6 (tail-span injection); the final sum step.
/-- The `f 0` summand vanishes, so the full sum is the tail sum. -/
theorem inRowSpan_matTail_of_subset_tail {S : FreeMatrix K (k + 1) n} {f : Fin (k + 1) → K}
    (hf0 : f 0 = 0) (j : Fin n) :
    (∑ b ∈ finFinset (k + 1), f b * S b j)
      = ∑ a ∈ finFinset k, f (Fin.succ a) * S (Fin.succ a) j :=
  let h2 : (∑ b ∈ finFinset (k + 1), f b * S b j)
      = f 0 * S 0 j + ∑ a ∈ finFinset k, f (Fin.succ a) * S (Fin.succ a) j :=
    sum_finFinset_succ (fun b : Fin (k + 1) => f b * S b j)
  h2.trans ((congrArg (· + _) ((congrArg (· * S 0 j) hf0).trans (zero_mul (S 0 j)))).trans
    (zero_add _))
-- Reference: MRR 1988, Pt. II Ch. 6 (if the rows of `R` after the first vanish
-- at column `c`, then the span of the tail of `R` injects into the span of
-- the tail of `S` via the coefficient at row `0` of `S`).
/-- If every tail row of `R` vanishes at column `c`, where `c` is the pivot
column of row `0` of the RREF matrix `S`, then the row span of the tail of
`R` is contained in the row span of the tail of `S`. -/
theorem inRowSpan_matTail_of_subset {R S : FreeMatrix K (k + 1) n}
    (hS : IsRref S) (hsub : ∀ w : FreeMod K n, inRowSpan R w → inRowSpan S w)
    {c : Fin n} (hcR : ∀ a : Fin k, R (Fin.succ a) c = 0)
    (hlcS : matLeadingCol S 0 = c.val) :
    ∀ w : FreeMod K n, inRowSpan (matTail R) w → inRowSpan (matTail S) w := by
  rcases hS with ⟨_, hS2, _, hS4⟩
  intro w hw
  let ⟨e, he⟩ := hw
  let hwR : inRowSpan R w := inRowSpan_matTail_lift he
  let ⟨f, hf⟩ := hsub w hwR
  let hwc : w c = 0 := inRowSpan_matTail_of_subset_wc he hcR
  let hf0 : f 0 = 0 := inRowSpan_matTail_of_subset_f0 hS2 hS4 hf hlcS hwc
  refine ⟨fun a => f (Fin.succ a), fun j => ?_⟩
  exact (hf j).trans (inRowSpan_matTail_of_subset_tail hf0 j)
-- Reference: MRR 1988, Pt. II Ch. 6 (uniqueness of the reduced row-echelon
-- form); the case where row `0` of `R` is zero (then all rows of both
-- matrices are zero).
/-- If row `0` of the RREF matrix `R` is zero, then `R = S`. -/
theorem rref_eq_of_subset_aux_zero_row {n k : ℕ} {R S : FreeMatrix K (k + 1) n}
    (hR : IsRref R) (hS : IsRref S)
    (hsub : ∀ w : FreeMod K n, inRowSpan R w → inRowSpan S w)
    (hd : (∀ w : FreeMod K n, inRowSpan S w → inRowSpan R w) ∨ nzCount R = nzCount S)
    (hs0 : findPivotRow (fun c => if R 0 c ≠ 0 then true else false) n 0 = none) :
    R = S := by
  let ⟨hR1, hR2, hR3, hR4⟩ := hR
  let ⟨hS1, hS2, hS3, hS4⟩ := hS
  have hzR : matRowZero R 0 := rowZero_of_findPivotRow_eq_none hs0
  have hzRall : ∀ a : Fin (k + 1), matRowZero R a := fun a =>
    match Fin.eq_zero_or_eq_succ a with
    | Or.inl h => Eq.mpr (congrArg (fun z => matRowZero R z) h) hzR
    | Or.inr ⟨j, h⟩ => Eq.mpr (congrArg (fun z => matRowZero R z) h) (hR1 0 (Fin.succ j) (Fin.succ_pos j) hzR)
  have hk0 : nzCount R = 0 := nzCount_eq_zero_of_rowZero_zero ⟨hR1, hR2, hR3, hR4⟩ hzR
  have hzS : ∀ b : Fin (k + 1), matRowZero S b := by
    rcases hd with hback | hk
    · intro b
      have hmem : inRowSpan R (S b) := hback (S b) (inRowSpan_self S b)
      let ⟨c, hc⟩ := hmem
      intro c'
      have hsum : (∑ a ∈ finFinset (k + 1), c a * R a c') = 0 :=
        sum_finFinset_eq_zero (fun a => (congrArg (c a * ·) (hzRall a c')).trans (mul_zero (c a)))
      exact (hc c').trans hsum
    · have hkS : nzCount S = 0 := hk.symm.trans hk0
      intro b
      cases hs' : findPivotRow (fun c => if S b c ≠ 0 then true else false) n 0 with
      | none => exact rowZero_of_findPivotRow_eq_none hs'
      | some c =>
          have hpos : 0 < nzCount S := by
            unfold nzCount
            exact List.countP_pos_iff.mpr
              ⟨b, List.mem_finRange b, (congrArg Option.isSome hs').trans (Option.isSome_some (a := c))⟩
          exact absurd (Eq.mp (congrArg (0 < ·) hkS) hpos) (Nat.lt_irrefl 0)
  funext a c
  exact (hzRall a c).trans (hzS a c).symm
-- Reference: MRR 1988, Pt. II Ch. 6 (uniqueness of the reduced row-echelon
-- form); the successor case of the induction on the number of rows, with a
-- pivot in row `0` of `R`.
/-- The successor case of the RREF uniqueness induction: row `0` of `R` is
nonzero; compare leading columns, recurse on the tails, and match row `0`. -/
theorem rref_eq_of_subset_aux_succ {n k : ℕ} (ih : ∀ (R S : FreeMatrix K k n),
    IsRref R → IsRref S →
    (∀ w : FreeMod K n, inRowSpan R w → inRowSpan S w) →
    ((∀ w : FreeMod K n, inRowSpan S w → inRowSpan R w) ∨ nzCount R = nzCount S) →
    R = S)
    {R S : FreeMatrix K (k + 1) n} (hR : IsRref R) (hS : IsRref S)
    (hsub : ∀ w : FreeMod K n, inRowSpan R w → inRowSpan S w)
    (hd : (∀ w : FreeMod K n, inRowSpan S w → inRowSpan R w) ∨ nzCount R = nzCount S)
    {c0 : Fin n}
    (hs0 : findPivotRow (fun c => if R 0 c ≠ 0 then true else false) n 0 = some c0) :
    R = S := by
  let ⟨hR1, hR2, hR3, hR4⟩ := hR
  let ⟨hS1, hS2, hS3, hS4⟩ := hS
  have hspec0 := findPivotRow_some_spec hs0
  have hneR0 : R 0 c0 ≠ 0 := ne_zero_of_pivotBool hspec0.2.2
  have hnzR0 : ¬ matRowZero R 0 := fun hz => hneR0 (hz c0)
  have hlcR : matLeadingCol R 0 = c0.val := matLeadingCol_eq_some hs0
  have hjR : c0.val < n := c0.isLt
  have hjR' : matLeadingCol R 0 < n := Eq.mpr (congrArg (· < n) hlcR) hjR
  have hnzS0 : ¬ matRowZero S 0 := by
    rcases hd with hback | hk
    · intro hzS
      have hzSall : ∀ b : Fin (k + 1), matRowZero S b := fun b =>
        match Fin.eq_zero_or_eq_succ b with
        | Or.inl h => Eq.mpr (congrArg (fun z => matRowZero S z) h) hzS
        | Or.inr ⟨j, h⟩ => Eq.mpr (congrArg (fun z => matRowZero S z) h) (hS1 0 (Fin.succ j) (Fin.succ_pos j) hzS)
      have hmem : inRowSpan S (R 0) := hsub (R 0) (inRowSpan_self R 0)
      let ⟨c, hc⟩ := hmem
      have hsum : ∀ c' : Fin n, (∑ a ∈ finFinset (k + 1), c a * S a c') = 0 :=
        fun c' => sum_finFinset_eq_zero (fun a => (congrArg (c a * ·) (hzSall a c')).trans (mul_zero (c a)))
      have h00 : R 0 c0 = 0 := Eq.mpr (congrArg (· = 0) (hc c0)) (hsum c0)
      exact hneR0 h00
    · intro hzS
      have hkpos : 0 < nzCount R := nzCount_pos_of_not_rowZero_zero hnzR0
      have hkS : nzCount S = nzCount R := hk.symm
      have hk0 : nzCount S = 0 := nzCount_eq_zero_of_rowZero_zero ⟨hS1, hS2, hS3, hS4⟩ hzS
      have hR0 : nzCount R = 0 := hkS.symm.trans hk0
      exact absurd (Eq.mp (congrArg (0 < ·) hR0) hkpos) (Nat.lt_irrefl 0)
  cases hs1 : findPivotRow (fun c => if S 0 c ≠ 0 then true else false) n 0 with
  | none => exact absurd (rowZero_of_findPivotRow_eq_none hs1) hnzS0
  | some c1 =>
    have hlcS : matLeadingCol S 0 = c1.val := matLeadingCol_eq_some hs1
    have hjS : c1.val < n := c1.isLt
    have hjS' : matLeadingCol S 0 < n := Eq.mpr (congrArg (· < n) hlcS) hjS
    -- Step A(i): the leading column of row 0 of S is at most that of R.
    have hle1 : matLeadingCol S 0 ≤ matLeadingCol R 0 := by
      rcases Nat.lt_or_ge (matLeadingCol R 0) (matLeadingCol S 0) with hlt | hge
      · have hvan : ∀ b : Fin (k + 1),
            S b ⟨matLeadingCol R 0, hjR'⟩ = 0 := fun b =>
          entry_eq_zero_of_lt_matLeadingCol
            (Nat.lt_of_lt_of_le hlt (matLeadingCol_zero_le ⟨hS1, hS2, hS3, hS4⟩ b))
        rcases hsub (R 0) (inRowSpan_self R 0) with ⟨d, hd⟩
        have e1 : R 0 ⟨matLeadingCol R 0, hjR'⟩ = 1 := hR2 0 _ (Fin.val_mk hjR').symm
        have e2 : R 0 ⟨matLeadingCol R 0, hjR'⟩
            = ∑ b ∈ finFinset _, d b * S b ⟨matLeadingCol R 0, hjR'⟩ := hd _
        have e3 : (∑ b ∈ finFinset _, d b * S b ⟨matLeadingCol R 0, hjR'⟩) = 0 :=
          sum_finFinset_eq_zero (fun b => (congrArg (d b * ·) (hvan b)).trans (mul_zero (d b)))
        exact absurd (e1.symm.trans (e2.trans e3)) one_ne_zero
      · exact hge
    -- Step A(ii): the leading column of row 0 of R is at most that of S.
    have hle2 : matLeadingCol R 0 ≤ matLeadingCol S 0 := by
      rcases hd with hback | hk
      · rcases Nat.lt_or_ge (matLeadingCol S 0) (matLeadingCol R 0) with hlt | hge
        · have hvan : ∀ b : Fin (k + 1),
              R b ⟨matLeadingCol S 0, hjS'⟩ = 0 := fun b =>
            entry_eq_zero_of_lt_matLeadingCol
              (Nat.lt_of_lt_of_le hlt (matLeadingCol_zero_le ⟨hR1, hR2, hR3, hR4⟩ b))
          rcases hback (S 0) (inRowSpan_self S 0) with ⟨d, hd⟩
          have e1 : S 0 ⟨matLeadingCol S 0, hjS'⟩ = 1 :=
            hS2 0 _ (Fin.val_mk hjS').symm
          have e2 : S 0 ⟨matLeadingCol S 0, hjS'⟩
              = ∑ b ∈ finFinset _, d b * R b ⟨matLeadingCol S 0, hjS'⟩ := hd _
          have e3 : (∑ b ∈ finFinset _, d b * R b ⟨matLeadingCol S 0, hjS'⟩) = 0 :=
            sum_finFinset_eq_zero (fun b => (congrArg (d b * ·) (hvan b)).trans (mul_zero (d b)))
          exact absurd (e1.symm.trans (e2.trans e3)) one_ne_zero
        · exact hge
      · rcases Nat.lt_or_ge (matLeadingCol S 0) (matLeadingCol R 0) with hlt | hge
        · -- jS < jR: absurdity via the tails
          rcases hsub (R 0) (inRowSpan_self R 0) with ⟨d, hd⟩
          have hd0 : d 0 = 0 := by
            have e1 : R 0 ⟨matLeadingCol S 0, hjS'⟩
                = ∑ b ∈ finFinset _, d b * S b ⟨matLeadingCol S 0, hjS'⟩ := hd _
            have e0 : R 0 ⟨matLeadingCol S 0, hjS'⟩ = 0 :=
              entry_eq_zero_of_lt_matLeadingCol hlt
            have hcl : ∀ a : Fin k,
                S (Fin.succ a) ⟨matLeadingCol S 0, hjS'⟩ = 0 := fun a =>
              hS4 0 (Fin.succ a) (Ne.symm (Fin.succ_ne_zero a)) _ (Fin.val_mk hjS').symm
            have hsum : (∑ a ∈ finFinset k,
                d (Fin.succ a) * S (Fin.succ a) ⟨matLeadingCol S 0, hjS'⟩) = 0 :=
              sum_finFinset_eq_zero (fun a => (congrArg (d (Fin.succ a) * ·) (hcl a)).trans (mul_zero _))
            have h2 : (∑ b ∈ finFinset (k + 1), d b * S b ⟨matLeadingCol S 0, hjS'⟩)
                = d 0 * S 0 ⟨matLeadingCol S 0, hjS'⟩
                  + ∑ a ∈ finFinset k,
                    d (Fin.succ a) * S (Fin.succ a) ⟨matLeadingCol S 0, hjS'⟩ :=
              sum_finFinset_succ
                (fun b : Fin (k + 1) => d b * S b ⟨matLeadingCol S 0, hjS'⟩)
            have e2 : (∑ b ∈ finFinset _, d b * S b ⟨matLeadingCol S 0, hjS'⟩) = d 0 :=
              h2.trans ((congrArg (· + _)
                (congrArg (d 0 * ·) (hS2 0 _ (Fin.val_mk hjS' ).symm))).trans
                ((congrArg (d 0 * 1 + ·) hsum).trans ((add_zero _).trans (mul_one _))))
            exact (e0.symm.trans (e1.trans e2)).symm
          have hcR' : ∀ a : Fin k,
              R (Fin.succ a) ⟨matLeadingCol S 0, hjS'⟩ = 0 := by
            intro a
            cases hs3 : findPivotRow
                (fun c => if R (Fin.succ a) c ≠ 0 then true else false) n 0 with
            | none => exact rowZero_of_findPivotRow_eq_none hs3 _
            | some c3 =>
                have hnb : ¬ matRowZero R (Fin.succ a) := fun hz =>
                  ne_zero_of_pivotBool (findPivotRow_some_spec hs3).2.2 (hz c3)
                have hlt3 : matLeadingCol R 0 < matLeadingCol R (Fin.succ a) :=
                  hR3 0 (Fin.succ a) (Fin.succ_pos a) hnb
                exact entry_eq_zero_of_lt_matLeadingCol (Nat.lt_trans hlt hlt3)
          have htail_sub : ∀ w : FreeMod K n, inRowSpan (matTail R) w →
              inRowSpan (matTail S) w :=
            inRowSpan_matTail_of_subset ⟨hS1, hS2, hS3, hS4⟩ hsub hcR'
              (Fin.val_mk hjS').symm
          have hktail : nzCount (matTail R) = nzCount (matTail S) := by
            have e1 := nzCount_succ_eq R hnzR0
            have e2 := nzCount_succ_eq S hnzS0
            exact Nat.add_right_cancel ((Eq.mp (congrArg (fun z => z = nzCount (matTail R) + 1) hk) e1).symm.trans e2)
          have htail_eq : matTail R = matTail S :=
            ih (matTail R) (matTail S) (isRref_matTail ⟨hR1, hR2, hR3, hR4⟩)
              (isRref_matTail ⟨hS1, hS2, hS3, hS4⟩) htail_sub (Or.inr hktail)
          have hR0tail : inRowSpan (matTail S) (R 0) := by
            refine ⟨fun a => d (Fin.succ a), fun j => ?_⟩
            have h2 : (∑ b ∈ finFinset (k + 1), d b * S b j)
                = d 0 * S 0 j + ∑ a ∈ finFinset k, d (Fin.succ a) * S (Fin.succ a) j :=
              sum_finFinset_succ (fun b : Fin (k + 1) => d b * S b j)
            have h2' : (∑ b ∈ finFinset (k + 1), d b * S b j)
                = ∑ a ∈ finFinset k, d (Fin.succ a) * S (Fin.succ a) j :=
              h2.trans ((congrArg (· + _) ((congrArg (· * S 0 j) hd0).trans (zero_mul (S 0 j)))).trans
                (zero_add _))
            exact (hd j).trans h2'
          let hw_tail : inRowSpan (matTail R) (R 0) := Eq.mpr (congrArg (fun M => inRowSpan M (R 0)) htail_eq) hR0tail
          let ⟨e, he⟩ := hw_tail
          have e1 : R 0 ⟨matLeadingCol R 0, hjR'⟩ = 1 := hR2 0 _ (Fin.val_mk hjR').symm
          have e2 : R 0 ⟨matLeadingCol R 0, hjR'⟩
              = ∑ a ∈ finFinset _, e a * matTail R a ⟨matLeadingCol R 0, hjR'⟩ := he _
          have e3 : (∑ a ∈ finFinset _, e a * matTail R a ⟨matLeadingCol R 0, hjR'⟩) = 0 :=
            sum_finFinset_eq_zero (fun a => by
              change e a * R (Fin.succ a) ⟨matLeadingCol R 0, hjR'⟩ = 0
              cases hs3 : findPivotRow
                  (fun c => if R (Fin.succ a) c ≠ 0 then true else false) n 0 with
              | none =>
                  exact (congrArg (e a * ·) (rowZero_of_findPivotRow_eq_none hs3 _)).trans (mul_zero (e a))
              | some c3 =>
                  have hnb : ¬ matRowZero R (Fin.succ a) := fun hz =>
                    ne_zero_of_pivotBool (findPivotRow_some_spec hs3).2.2 (hz c3)
                  have hlt3 : matLeadingCol R 0 < matLeadingCol R (Fin.succ a) :=
                    hR3 0 (Fin.succ a) (Fin.succ_pos a) hnb
                  exact (congrArg (e a * ·) (entry_eq_zero_of_lt_matLeadingCol
                    (c := ⟨matLeadingCol R 0, hjR'⟩) hlt3)).trans (mul_zero (e a)))
          exact absurd (e1.symm.trans (e2.trans e3)) one_ne_zero
        · exact hge
    have hj : matLeadingCol R 0 = matLeadingCol S 0 := Nat.le_antisymm hle2 hle1
    -- The tails: span of the tail of R injects into the tail of S.
    have hcR : ∀ a : Fin k, R (Fin.succ a) ⟨matLeadingCol R 0, hjR'⟩ = 0 := by
      intro a
      cases hs3 : findPivotRow
          (fun c => if R (Fin.succ a) c ≠ 0 then true else false) n 0 with
      | none => exact rowZero_of_findPivotRow_eq_none hs3 _
      | some c3 =>
          have hnb : ¬ matRowZero R (Fin.succ a) := fun hz =>
            ne_zero_of_pivotBool (findPivotRow_some_spec hs3).2.2 (hz c3)
          have hlt3 : matLeadingCol R 0 < matLeadingCol R (Fin.succ a) :=
            hR3 0 (Fin.succ a) (Fin.succ_pos a) hnb
          exact entry_eq_zero_of_lt_matLeadingCol
            (c := ⟨matLeadingCol R 0, hjR'⟩) hlt3
    have hlcS_at : matLeadingCol S 0
        = (⟨matLeadingCol R 0, hjR'⟩ : Fin n).val :=
      Eq.mp (congrArg (fun z => z = (⟨matLeadingCol R 0, hjR'⟩ : Fin n).val) hj) (Fin.val_mk hjR').symm
    have htail_sub : ∀ w : FreeMod K n, inRowSpan (matTail R) w →
        inRowSpan (matTail S) w :=
      inRowSpan_matTail_of_subset ⟨hS1, hS2, hS3, hS4⟩ hsub hcR hlcS_at
    have hdtail : (∀ w : FreeMod K n, inRowSpan (matTail S) w →
          inRowSpan (matTail R) w) ∨
        nzCount (matTail R) = nzCount (matTail S) := by
      rcases hd with hback | hk
      · left
        have hcS : ∀ a : Fin k,
            S (Fin.succ a) ⟨matLeadingCol S 0, hjS'⟩ = 0 := by
          intro a
          cases hs3 : findPivotRow
              (fun c => if S (Fin.succ a) c ≠ 0 then true else false) n 0 with
          | none => exact rowZero_of_findPivotRow_eq_none hs3 _
          | some c3 =>
              have hnb : ¬ matRowZero S (Fin.succ a) := fun hz =>
                ne_zero_of_pivotBool (findPivotRow_some_spec hs3).2.2 (hz c3)
              have hlt3 : matLeadingCol S 0 < matLeadingCol S (Fin.succ a) :=
                hS3 0 (Fin.succ a) (Fin.succ_pos a) hnb
              exact entry_eq_zero_of_lt_matLeadingCol
                (c := ⟨matLeadingCol S 0, hjS'⟩) hlt3
        have hlcR_at : matLeadingCol R 0
            = (⟨matLeadingCol S 0, hjS'⟩ : Fin n).val :=
          Eq.mp (congrArg (fun z => z = (⟨matLeadingCol S 0, hjS'⟩ : Fin n).val) hj.symm) (Fin.val_mk hjS').symm
        exact inRowSpan_matTail_of_subset ⟨hR1, hR2, hR3, hR4⟩ hback hcS hlcR_at
      · right
        have e1 := nzCount_succ_eq R hnzR0
        have e2 := nzCount_succ_eq S hnzS0
        exact Nat.add_right_cancel ((Eq.mp (congrArg (fun z => z = nzCount (matTail R) + 1) hk) e1).symm.trans e2)
    have htail_eq : matTail R = matTail S :=
      ih (matTail R) (matTail S) (isRref_matTail ⟨hR1, hR2, hR3, hR4⟩)
        (isRref_matTail ⟨hS1, hS2, hS3, hS4⟩) htail_sub hdtail
    have hrows : ∀ a : Fin k, R (Fin.succ a) = S (Fin.succ a) :=
      fun a => congrFun htail_eq a
    -- The coefficient of row 0 in the expansion of R 0 over S is 1.
    rcases hsub (R 0) (inRowSpan_self R 0) with ⟨d, hd⟩
    have hd0 : d 0 = 1 := by
      have e1 : R 0 ⟨matLeadingCol R 0, hjR'⟩
          = ∑ b ∈ finFinset _, d b * S b ⟨matLeadingCol R 0, hjR'⟩ := hd _
      have e0 : R 0 ⟨matLeadingCol R 0, hjR'⟩ = 1 :=
        hR2 0 _ (Fin.val_mk hjR').symm
      have hcl : ∀ a : Fin k,
          S (Fin.succ a) ⟨matLeadingCol R 0, hjR'⟩ = 0 := fun a =>
        hS4 0 (Fin.succ a) (Ne.symm (Fin.succ_ne_zero a)) _ hlcS_at
      have hsum : (∑ a ∈ finFinset k,
          d (Fin.succ a) * S (Fin.succ a) ⟨matLeadingCol R 0, hjR'⟩) = 0 :=
        sum_finFinset_eq_zero (fun a => (congrArg (d (Fin.succ a) * ·) (hcl a)).trans (mul_zero _))
      have h2 : (∑ b ∈ finFinset (k + 1), d b * S b ⟨matLeadingCol R 0, hjR'⟩)
          = d 0 * S 0 ⟨matLeadingCol R 0, hjR'⟩
            + ∑ a ∈ finFinset k,
              d (Fin.succ a) * S (Fin.succ a) ⟨matLeadingCol R 0, hjR'⟩ :=
        sum_finFinset_succ
          (fun b : Fin (k + 1) => d b * S b ⟨matLeadingCol R 0, hjR'⟩)
      have e2 : (∑ b ∈ finFinset _, d b * S b ⟨matLeadingCol R 0, hjR'⟩) = d 0 :=
        h2.trans ((congrArg (· + _) (congrArg (d 0 * ·) (hS2 0 _ hlcS_at))).trans
          ((congrArg (d 0 * 1 + ·) hsum).trans ((add_zero _).trans (mul_one _))))
      exact (e0.symm.trans (e1.trans e2)).symm
    -- The difference `R 0 - S 0` lies in the span of the tail of S.
    have hw_tail : inRowSpan (matTail S) (R 0 - S 0) := by
      refine ⟨fun a => d (Fin.succ a), fun j => ?_⟩
      have h2 : (∑ b ∈ finFinset (k + 1), d b * S b j)
          = d 0 * S 0 j + ∑ a ∈ finFinset k, d (Fin.succ a) * S (Fin.succ a) j :=
        sum_finFinset_succ (fun b : Fin (k + 1) => d b * S b j)
      have h2' : (∑ b ∈ finFinset (k + 1), d b * S b j)
          = S 0 j + ∑ a ∈ finFinset k, d (Fin.succ a) * S (Fin.succ a) j :=
        h2.trans (congrArg (· + ∑ a ∈ finFinset k, d (Fin.succ a) * S (Fin.succ a) j)
          ((congrArg (· * S 0 j) hd0).trans (one_mul (S 0 j))))
      change R 0 j - S 0 j = ∑ a ∈ finFinset k, d (Fin.succ a) * S (Fin.succ a) j
      exact Eq.mpr (congrArg (fun z => z - S 0 j = ∑ a ∈ finFinset k, d (Fin.succ a) * S (Fin.succ a) j) (hd j))
        (Eq.mpr (congrArg (fun z => z - S 0 j = ∑ a ∈ finFinset k, d (Fin.succ a) * S (Fin.succ a) j) h2')
          (add_sub_cancel_left _ _))
    let hw_tail' : inRowSpan (matTail R) (R 0 - S 0) := Eq.mpr (congrArg (fun M => inRowSpan M (R 0 - S 0)) htail_eq) hw_tail
    -- Show `R 0 = S 0`: otherwise the pivot lemma contradicts clause 4.
    have hR0eqS0 : R 0 = S 0 := by
      cases (inferInstance : Decidable (R 0 - S 0 = 0)) with
      | isTrue h => exact sub_eq_zero.mp h
      | isFalse hw0 =>
          rcases exists_matLeadingCol_eq_vecLeadingCol
              (isRref_matTail ⟨hR1, hR2, hR3, hR4⟩) hw_tail' hw0 with
            ⟨bstar, hnb, hlc⟩
          have hlc' : matLeadingCol R (Fin.succ bstar)
              = vecLeadingCol (R 0 - S 0) := hlc
          have hvan : ∀ c : Fin n, c.val ≤ matLeadingCol R 0 →
              (R 0 - S 0) c = 0 := by
            intro c hc
            rcases Nat.lt_or_ge c.val (matLeadingCol R 0) with hlt | hge
            · exact (Pi.sub_apply (R 0) (S 0) c).trans
                ((congrArg₂ (· - ·)
                  (entry_eq_zero_of_lt_matLeadingCol (A := R) (a := 0) (c := c) hlt)
                  (entry_eq_zero_of_lt_matLeadingCol (A := S) (a := 0) (c := c)
(Eq.mp (congrArg (c.val < ·) hj) hlt))).trans (sub_self 0))
            · have heq : c = ⟨matLeadingCol R 0, hjR'⟩ :=
                Fin.eq_of_val_eq (Nat.le_antisymm hc hge)
              exact Eq.mpr (congrArg (fun z => (R 0 - S 0) z = 0) heq) ((Pi.sub_apply (R 0) (S 0) _).trans
                ((congrArg₂ (· - ·) (hR2 0 _ (Fin.val_mk hjR').symm) (hS2 0 _ hlcS_at)).trans
                  (sub_self 1)))
          have hgt : matLeadingCol R 0 < vecLeadingCol (R 0 - S 0) :=
            vecLeadingCol_lt_of_vanish hw0 hvan
          have hjj : vecLeadingCol (R 0 - S 0) < n := vecLeadingCol_lt hw0
          have hne_w : (R 0 - S 0) ⟨vecLeadingCol (R 0 - S 0), hjj⟩ ≠ 0 :=
            vecLeadingCol_ne_zero hw0
          have hlcS' : matLeadingCol S (Fin.succ bstar)
              = (⟨vecLeadingCol (R 0 - S 0), hjj⟩ : Fin n).val := by
            have h1 := matLeadingCol_congr (A := R) (B := S)
              (a := Fin.succ bstar) (b := Fin.succ bstar)
              (fun c => congrFun (hrows bstar) c)
            exact Eq.mp (congrArg (fun z => z = (⟨vecLeadingCol (R 0 - S 0), hjj⟩ : Fin n).val) h1) (hlc'.trans (Fin.val_mk hjj).symm)
          have hS0 : S 0 ⟨vecLeadingCol (R 0 - S 0), hjj⟩ = 0 :=
            hS4 (Fin.succ bstar) 0 (Fin.succ_ne_zero bstar) _ hlcS'
          have hR0 : R 0 ⟨vecLeadingCol (R 0 - S 0), hjj⟩ = 0 :=
            hR4 (Fin.succ bstar) 0 (Fin.succ_ne_zero bstar) _ hlc'
          have hzero : (R 0 - S 0) ⟨vecLeadingCol (R 0 - S 0), hjj⟩ = 0 :=
            (Pi.sub_apply (R 0) (S 0) _).trans
              ((congrArg₂ (· - ·) hR0 hS0).trans (sub_self 0))
          exact absurd hzero hne_w
    funext a
    rcases Fin.eq_zero_or_eq_succ a with h | ⟨j', h⟩
    · exact Eq.mpr (congrArg (fun z => R z = S z) h) hR0eqS0
    · exact Eq.mpr (congrArg (fun z => R z = S z) h) (hrows j')
-- Reference: MRR 1988, Pt. II Ch. 6 (uniqueness of the reduced row-echelon
-- form: proved by induction on the number of rows — compare the leading
-- columns of the first rows, show the first rows agree, and recurse on the
-- tails). The disjunctive hypothesis covers both the symmetric case (spans
-- equal) and the one-sided case (nonzero-row counts equal).
/-- Auxiliary induction for uniqueness of the RREF: two RREF matrices with
the same number of rows, one-sided span inclusion, and either the reverse
inclusion or equal nonzero-row counts, are equal. -/
theorem rref_eq_of_subset_aux {n : ℕ} :
    ∀ (l : ℕ) (R S : FreeMatrix K l n), IsRref R → IsRref S →
      (∀ w : FreeMod K n, inRowSpan R w → inRowSpan S w) →
      ((∀ w : FreeMod K n, inRowSpan S w → inRowSpan R w) ∨ nzCount R = nzCount S) →
      R = S :=
  fun l => Nat.rec (motive := fun l => ∀ (R S : FreeMatrix K l n), IsRref R → IsRref S →
      (∀ w : FreeMod K n, inRowSpan R w → inRowSpan S w) →
      ((∀ w : FreeMod K n, inRowSpan S w → inRowSpan R w) ∨ nzCount R = nzCount S) →
      R = S)
    (fun R S _ _ _ _ => funext fun a => Fin.elim0 a)
    (fun k ih R S hR hS hsub hd => by
      cases hs0 : findPivotRow (fun c => if R 0 c ≠ 0 then true else false) n 0 with
      | none => exact rref_eq_of_subset_aux_zero_row hR hS hsub hd hs0
      | some c0 => exact rref_eq_of_subset_aux_succ ih hR hS hsub hd hs0)
    l
-- Reference: MRR 1988, Pt. II Ch. 6 (uniqueness of the RREF).
/-- Two RREF matrices with the same number of rows and the same row span are
equal. -/
theorem rref_eq_of_span_eq {l : ℕ} {R S : FreeMatrix K l n} (hR : IsRref R) (hS : IsRref S)
    (h : ∀ w : FreeMod K n, inRowSpan R w ↔ inRowSpan S w) : R = S :=
  rref_eq_of_subset_aux l R S hR hS (fun w hw => (h w).mp hw)
    (Or.inl (fun w hw => (h w).mpr hw))
-- Reference: MRR 1988, Pt. II Ch. 6 (uniqueness of the RREF, one-sided form:
-- inclusion of spans plus equal rank forces equality).
/-- Two RREF matrices with the same number of rows, one-sided span inclusion,
and equal nonzero-row counts are equal. -/
theorem rref_eq_of_subset_nzCount {l : ℕ} {R S : FreeMatrix K l n} (hR : IsRref R)
    (hS : IsRref S) (hsub : ∀ w : FreeMod K n, inRowSpan R w → inRowSpan S w)
    (hk : nzCount R = nzCount S) : R = S :=
  rref_eq_of_subset_aux l R S hR hS hsub (Or.inr hk)
end BoringMath
