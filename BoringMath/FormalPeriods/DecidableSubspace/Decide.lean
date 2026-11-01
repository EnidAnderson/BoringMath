/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Init
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Field.Rat
import Mathlib.Data.Fin.Basic
import BoringMath.FormalPeriods.DecidableSubspace.Sums
import BoringMath.FormalPeriods.DecidableSubspace.RowSpan
import BoringMath.FormalPeriods.DecidableSubspace.Pivots
import BoringMath.FormalPeriods.DecidableSubspace.Rank
import BoringMath.FormalPeriods.DecidableSubspace.RowOps
import BoringMath.FormalPeriods.DecidableSubspace.RrefProps
import BoringMath.FormalPeriods.DecidableSubspace.Residual
import BoringMath.FormalPeriods.DecidableSubspace.Uniqueness
import BoringMath.FormalPeriods.AxiomLint
import BoringMath.FormalPeriods.FreeMod
import BoringMath.FormalPeriods.RowReduction
/-!
# The rank criterion, the decision procedures, smoke tests, axiom lint (P.2.3, part 9)

Piece 9 of `BoringMath.FormalPeriods.DecidableSubspace`: `rankOf`, the rank
criterion `inRowSpan A v ↔ rankOf (matSnoc A v) = rankOf A`, the computable
decision procedures `memRowSpanBool`/`spanContainsBool`/`spanEqBool`/
`rrefResidualBool` with their `Decidable` instances and correctness lemmas,
the smoke tests over `ℚ`, and the `#lint_axioms` block.
-/
universe u
namespace BoringMath
variable {K : Type u} [Field K] {m n k p : ℕ}
variable (invK : K → K)
variable [DecidableEq K]
/-! ## The rank criterion and the decision procedures -/
-- Reference: MRR 1988, Pt. II Ch. 6 (the rank of a matrix is the number of
-- nonzero rows of its RREF).
/-- The computed rank of `A`: the number of nonzero rows of its RREF. -/
def rankOf (invK : K → K) (A : FreeMatrix K m n) : ℕ := nzCount (rref invK A)
-- Reference: MRR 1988, Pt. II Ch. 6 (`v ∈ span S` implies
-- `rank(S ∪ {v}) = rank S`: the span is unchanged, the RREF is unique, and
-- appending a zero row does not change the count).
/-- If `v` lies in the row span of `A`, appending it as a row does not change
the computed rank. -/
theorem nzCount_rref_snoc_eq_of_mem (hinv : ∀ a : K, a ≠ 0 → invK a * a = 1)
    {A : FreeMatrix K m n} {v : FreeMod K n} (hv : inRowSpan A v) :
    nzCount (rref invK (matSnoc A v)) = nzCount (rref invK A) := by
  have hR : IsRref (rref invK A) := rref_isRref invK hinv A
  have hR' : IsRref (rref invK (matSnoc A v)) := rref_isRref invK hinv (matSnoc A v)
  have hpad : IsRref (matSnoc (rref invK A) 0) := isRref_snoc_zero hR
  have hs1 : ∀ w : FreeMod K n, inRowSpan (matSnoc (rref invK A) 0) w ↔
      inRowSpan (rref invK A) w :=
    fun w => inRowSpan_snoc_of_mem (w := w) (inRowSpan_zero (rref invK A))
  have hs2 : ∀ w : FreeMod K n, inRowSpan (rref invK (matSnoc A v)) w ↔
      inRowSpan (matSnoc A v) w := fun w => inRowSpan_rref invK hinv (matSnoc A v) w
  have hs3 : ∀ w : FreeMod K n, inRowSpan (rref invK A) w ↔ inRowSpan A w :=
    fun w => inRowSpan_rref invK hinv A w
  have hs4 : ∀ w : FreeMod K n, inRowSpan (matSnoc A v) w ↔ inRowSpan A w :=
    fun w => inRowSpan_snoc_of_mem hv
  have heq : ∀ w : FreeMod K n, inRowSpan (matSnoc (rref invK A) 0) w ↔
      inRowSpan (rref invK (matSnoc A v)) w :=
    fun w => (hs1 w).trans ((hs3 w).trans ((hs4 w).symm.trans (hs2 w).symm))
  have h_eq_mat := rref_eq_of_span_eq hpad hR' heq
  exact Eq.mp (congrArg (fun M => nzCount M = nzCount (rref invK A)) h_eq_mat) (nzCount_snoc_zero (rref invK A))
-- Reference: MRR 1988, Pt. II Ch. 6 (`rank(S ∪ {v}) = rank S` implies
-- `v ∈ span S`: pad the RREF of `A` with a zero row; the one-sided uniqueness
-- with equal counts forces it to equal the RREF of `A` with `v` appended).
/-- If appending `v` as a row does not change the computed rank, then `v`
lies in the row span of `A`. -/
theorem mem_of_nzCount_rref_snoc_eq (hinv : ∀ a : K, a ≠ 0 → invK a * a = 1)
    {A : FreeMatrix K m n} {v : FreeMod K n}
    (hk : nzCount (rref invK (matSnoc A v)) = nzCount (rref invK A)) :
    inRowSpan A v := by
  have hR : IsRref (rref invK A) := rref_isRref invK hinv A
  have hR' : IsRref (rref invK (matSnoc A v)) := rref_isRref invK hinv (matSnoc A v)
  have hpad : IsRref (matSnoc (rref invK A) 0) := isRref_snoc_zero hR
  have hkpad : nzCount (matSnoc (rref invK A) 0) = nzCount (rref invK (matSnoc A v)) :=
    (nzCount_snoc_zero (rref invK A)).trans hk.symm
  have hsub : ∀ w : FreeMod K n, inRowSpan (matSnoc (rref invK A) 0) w →
      inRowSpan (rref invK (matSnoc A v)) w := by
    intro w hw
    have h1 : inRowSpan (rref invK A) w :=
      (inRowSpan_snoc_of_mem (w := w) (inRowSpan_zero (rref invK A))).mp hw
    have h2 : inRowSpan A w := (inRowSpan_rref invK hinv A w).mp h1
    have h3 : inRowSpan (matSnoc A v) w := inRowSpan_snoc_mono h2
    exact (inRowSpan_rref invK hinv (matSnoc A v) w).mpr h3
  have h_eq_mat := rref_eq_of_subset_nzCount hpad hR' hsub hkpad
  have hv1 : inRowSpan (matSnoc A v) v := inRowSpan_snoc_self
  have hv2 : inRowSpan (rref invK (matSnoc A v)) v :=
    (inRowSpan_rref invK hinv (matSnoc A v) v).mpr hv1
  have hv2' : inRowSpan (matSnoc (rref invK A) 0) v := Eq.mpr (congrArg (fun M => inRowSpan M v) h_eq_mat) hv2
  have hv3 : inRowSpan (rref invK A) v :=
    (inRowSpan_snoc_of_mem (w := v) (inRowSpan_zero (rref invK A))).mp hv2'
  exact (inRowSpan_rref invK hinv A v).mp hv3
-- Reference: MRR 1988, Pt. II Ch. 6 (the rank criterion for membership:
-- `v ∈ span S` iff `rank(S ∪ {v}) = rank S`).
/-- The rank criterion: `v` lies in the row span of `A` iff appending it as a
row leaves the computed rank unchanged. -/
theorem inRowSpan_iff_rankOf_snoc_eq (hinv : ∀ a : K, a ≠ 0 → invK a * a = 1)
    {A : FreeMatrix K m n} {v : FreeMod K n} :
    inRowSpan A v ↔ rankOf invK (matSnoc A v) = rankOf invK A := by
  unfold rankOf
  exact ⟨fun hv => nzCount_rref_snoc_eq_of_mem invK hinv hv,
    fun hk => mem_of_nzCount_rref_snoc_eq invK hinv hk⟩
-- Reference: MRR 1988, Pt. II Ch. 6 (membership decided by the rank
-- comparison, as a `Bool`).
/-- The membership decision for a spanning-set subspace: `v ∈ span(rows A)`
iff `rankOf (A; v) = rankOf A`, computed as a `Bool`. -/
def memRowSpanBool (invK : K → K) (A : FreeMatrix K m n) (v : FreeMod K n) : Bool :=
  (rankOf invK (matSnoc A v) == rankOf invK A)
-- Reference: issue #110 (membership decided by the rank comparison).
/-- The membership decision is correct: it says `true` iff `v` lies in the
row span of `A`. -/
theorem memRowSpanBool_true_iff (hinv : ∀ a : K, a ≠ 0 → invK a * a = 1)
    {A : FreeMatrix K m n} {v : FreeMod K n} :
    memRowSpanBool invK A v = true ↔ inRowSpan A v :=
  beq_iff_eq.trans (inRowSpan_iff_rankOf_snoc_eq invK hinv).symm
-- Reference: issue #110 (an explicit `Decidable` instance replacing
-- `Classical.dec`).
/-- Decidable membership in the row span of `A`, computed by the rank
comparison; explicit in the inverse data `invK`/`hinv` (STYLE §2.3), so this
is a `def` rather than a typeclass instance. -/
def memRowSpanDecidable (invK : K → K) (hinv : ∀ a : K, a ≠ 0 → invK a * a = 1)
    (A : FreeMatrix K m n) (v : FreeMod K n) : Decidable (inRowSpan A v) :=
  decidable_of_iff (memRowSpanBool invK A v = true) (memRowSpanBool_true_iff invK hinv)
-- Reference: MRR 1988, Pt. II Ch. 6 (containment of spans reduces to
-- membership of the generators of one in the other).
/-- Containment of spans is decided by membership of every row of `B` in the
span of `A`, row by row, as a `Bool`. -/
def spanContainsBool (invK : K → K) (A : FreeMatrix K m n) (B : FreeMatrix K p n) : Bool :=
  (List.finRange p).all (fun b => memRowSpanBool invK A (B b))
-- Reference: MRR 1988, Pt. II Ch. 6 (`span B ⊆ span A` iff every generator of
-- `B` lies in `span A`).
omit [DecidableEq K] in
/-- Containment of spans holds iff every row of `B` lies in the span of `A`. -/
theorem spanContains_iff_rows {A : FreeMatrix K m n} {B : FreeMatrix K p n} :
    (∀ b : Fin p, inRowSpan A (B b)) ↔
      ∀ w : FreeMod K n, inRowSpan B w → inRowSpan A w :=
  ⟨fun h w hw => inRowSpan_mono (B := A) _ B w h hw, fun h b => h (B b) (inRowSpan_self B b)⟩
-- Reference: MRR 1988, Pt. II Ch. 6 (the elements of `finRange n` are exactly
-- the `Fin n`).
/-- A pointwise condition on `List.finRange n` is equivalent to the condition
on all of `Fin n`. -/
theorem forall_mem_finRange {n : ℕ} {p : Fin n → Bool} :
    (∀ x ∈ List.finRange n, p x = true) ↔ ∀ x : Fin n, p x = true :=
  ⟨fun h x => h x (List.mem_finRange x), fun h x _ => h x⟩
-- Reference: issue #110 (containment decided by the membership decisions).
-- Reference: issue #110 (containment decided by the membership decisions);
-- the pointwise iff step.
/-- Membership decisions say `true` pointwise iff every row of `B` is in the
span of `A`. -/
theorem spanContainsBool_true_iff_rows (hinv : ∀ a : K, a ≠ 0 → invK a * a = 1)
    {A : FreeMatrix K m n} {B : FreeMatrix K p n} :
    (∀ b : Fin p, memRowSpanBool invK A (B b) = true) ↔ ∀ b : Fin p, inRowSpan A (B b) :=
  forall_congr' (fun b => memRowSpanBool_true_iff invK hinv (A := A) (v := B b))
theorem spanContainsBool_true_iff (hinv : ∀ a : K, a ≠ 0 → invK a * a = 1)
    {A : FreeMatrix K m n} {B : FreeMatrix K p n} :
    spanContainsBool invK A B = true ↔ ∀ b : Fin p, inRowSpan A (B b) := by
  change (List.finRange p).all (fun b => memRowSpanBool invK A (B b)) = true ↔ _
  exact ((List.all_eq_true (l := List.finRange p)
      (p := fun b => memRowSpanBool invK A (B b))).trans forall_mem_finRange).trans
    (spanContainsBool_true_iff_rows invK hinv)
-- Reference: issue #110 (an explicit `Decidable` for containment).
/-- Decidable containment `span B ⊆ span A`, computed row by row; explicit
in the inverse data `invK`/`hinv` (STYLE §2.3), so a `def`. -/
def spanContainsDecidable (invK : K → K) (hinv : ∀ a : K, a ≠ 0 → invK a * a = 1)
    (A : FreeMatrix K m n) (B : FreeMatrix K p n) :
    Decidable (∀ w : FreeMod K n, inRowSpan B w → inRowSpan A w) :=
  decidable_of_iff (spanContainsBool invK A B = true)
    ((spanContainsBool_true_iff invK hinv).trans (spanContains_iff_rows))
-- Reference: MRR 1988, Pt. II Ch. 6 (equality of spans is mutual
-- containment).
/-- Equality of spans is decided by mutual containment, as a `Bool`. -/
def spanEqBool (invK : K → K) (A : FreeMatrix K m n) (B : FreeMatrix K p n) : Bool :=
  spanContainsBool invK A B && spanContainsBool invK B A
-- Reference: issue #110 (equality decided by mutual containment).
-- Reference: issue #110 (equality decided by mutual containment); forward
-- direction.
/-- If both containment decisions hold, the spans are equal. -/
theorem spanEqBool_true_iff_fwd (hinv : ∀ a : K, a ≠ 0 → invK a * a = 1)
    {A : FreeMatrix K m n} {B : FreeMatrix K p n}
    (h1 : spanContainsBool invK A B = true) (h2 : spanContainsBool invK B A = true) :
    ∀ w : FreeMod K n, inRowSpan A w ↔ inRowSpan B w :=
  let e1 := (spanContainsBool_true_iff invK hinv).mp h1
  let e2 := (spanContainsBool_true_iff invK hinv).mp h2
  fun w => ⟨(spanContains_iff_rows.mp e2) w, (spanContains_iff_rows.mp e1) w⟩
-- Reference: issue #110 (equality decided by mutual containment); backward
-- direction.
/-- If the spans are equal, both containment decisions hold. -/
theorem spanEqBool_true_iff_bwd (hinv : ∀ a : K, a ≠ 0 → invK a * a = 1)
    {A : FreeMatrix K m n} {B : FreeMatrix K p n}
    (h : ∀ w : FreeMod K n, inRowSpan A w ↔ inRowSpan B w) :
    spanContainsBool invK A B = true ∧ spanContainsBool invK B A = true :=
  ⟨(spanContainsBool_true_iff invK hinv).mpr (fun b => (h (B b)).mpr (inRowSpan_self B b)),
    (spanContainsBool_true_iff invK hinv).mpr (fun a => (h (A a)).mp (inRowSpan_self A a))⟩
theorem spanEqBool_true_iff (hinv : ∀ a : K, a ≠ 0 → invK a * a = 1)
    {A : FreeMatrix K m n} {B : FreeMatrix K p n} :
    spanEqBool invK A B = true ↔ ∀ w : FreeMod K n, inRowSpan A w ↔ inRowSpan B w := by
  change (spanContainsBool invK A B && spanContainsBool invK B A) = true ↔ _
  exact Bool.and_eq_true_iff.trans
    ⟨fun ⟨h1, h2⟩ => spanEqBool_true_iff_fwd invK hinv h1 h2,
      fun h => spanEqBool_true_iff_bwd invK hinv h⟩
-- Reference: issue #110 (an explicit `Decidable` for span equality).
/-- Decidable equality of the spans of `A` and `B`, computed by mutual
containment; explicit in the inverse data `invK`/`hinv` (STYLE §2.3), so a
`def`. -/
def spanEqDecidable (invK : K → K) (hinv : ∀ a : K, a ≠ 0 → invK a * a = 1)
    (A : FreeMatrix K m n) (B : FreeMatrix K p n) :
    Decidable (∀ w : FreeMod K n, inRowSpan A w ↔ inRowSpan B w) :=
  decidable_of_iff (spanEqBool invK A B = true) (spanEqBool_true_iff invK hinv)
-- Reference: MRR 1988, Pt. II Ch. 6 (for an RREF-given subspace, membership is
-- decided by the residual against the pivot rows).
/-- The membership decision for an RREF-given subspace: the residual of `v`
against the pivot rows vanishes at every column, as a `Bool`. -/
def rrefResidualBool (R : FreeMatrix K m n) (v : FreeMod K n) : Bool :=
  (List.finRange n).all (fun c => if rrefResidual R v c = 0 then true else false)
-- Reference: MRR 1988, Pt. II Ch. 6 (the residual criterion, as a `Bool`).
-- Reference: MRR 1988, Pt. II Ch. 6 (the residual criterion, as a `Bool`); the
-- per-column iff.
/-- The residual test at `c` says `true` iff the residual at `c` is zero. -/
theorem rrefResidualBool_true_iff_col {R : FreeMatrix K m n} {v : FreeMod K n} (c : Fin n) :
    (if rrefResidual R v c = 0 then true else false) = true ↔ rrefResidual R v c = 0 :=
  ⟨fun h => by
      cases (inferInstance : Decidable (rrefResidual R v c = 0)) with
      | isTrue h0 => exact h0
      | isFalse h0 =>
          let hf : (if rrefResidual R v c = 0 then true else false) = false := ite_eq_right h0
          exact absurd (Eq.mp (congrArg (· = true) hf) h) Bool.false_ne_true,
    fun h => ite_eq_left h⟩
-- Reference: MRR 1988, Pt. II Ch. 6 (the residual criterion, as a `Bool`); the
-- pointwise iff over all columns.
/-- The residual test holds on all of `finRange n` iff the residual vanishes
at every column. -/
theorem rrefResidualBool_true_iff_all {R : FreeMatrix K m n} {v : FreeMod K n} :
    (∀ x ∈ List.finRange n, (if rrefResidual R v x = 0 then true else false) = true) ↔
      ∀ c : Fin n, rrefResidual R v c = 0 :=
  forall_mem_finRange.trans (forall_congr' (fun c => rrefResidualBool_true_iff_col c))
-- Reference: MRR 1988, Pt. II Ch. 6 (the residual criterion, as a `Bool`).
/-- The residual decision is correct for RREF matrices. -/
theorem rrefResidualBool_true_iff {R : FreeMatrix K m n} (hR : IsRref R) (v : FreeMod K n) :
    rrefResidualBool R v = true ↔ inRowSpan R v := by
  change (List.finRange n).all (fun c => if rrefResidual R v c = 0 then true else false)
      = true ↔ _
  exact ((List.all_eq_true (l := List.finRange n)
      (p := fun c => if rrefResidual R v c = 0 then true else false)).trans
    rrefResidualBool_true_iff_all).trans (inRowSpan_rref_iff hR v).symm
-- Reference: issue #110 (an explicit `Decidable` for membership in an
-- RREF-given subspace; the RREF predicate is explicit data, STYLE §2.3).
/-- Decidable membership in the row span of an RREF matrix `R`, computed by
the residual criterion; explicit in the RREF proof (a `def`, not a typeclass
instance). -/
def rrefMemRowSpanDecidable (R : FreeMatrix K m n) (hR : IsRref R) (v : FreeMod K n) :
    Decidable (inRowSpan R v) :=
  decidable_of_iff (rrefResidualBool R v = true) (rrefResidualBool_true_iff hR v)
/-! ## Smoke tests -/
-- Reference: smoke test for the acceptance criterion of issue #110 (concrete
-- decisions over `ℚ`).
/-- The explicit inverse of a nonzero rational, as the core data `Rat.inv`
(avoiding the choice-tainted `⁻¹` instance path at the pin, as in
`RowReduction`). -/
def ratInv (a : ℚ) : ℚ := Rat.inv a
-- Reference: smoke test (issue #110): the plane in `ℚ³` spanned by `(1,0,1)`
-- and `(0,1,1)`.
/-- A 2×3 matrix over `ℚ` whose rows span a plane in `ℚ³`. -/
def smokeA : Fin 2 → Fin 3 → ℚ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 1 | 0, 2 => 1
  | 1, 1 => 1 | 1, 2 => 1
  | _, _ => 0
-- Reference: smoke test: the row `(1,1,2)` lies in the plane (it is the sum of
-- the two rows of `smokeA`).
/-- A 1×3 matrix over `ℚ` whose row lies in the plane of `smokeA`. -/
def smokeB : Fin 1 → Fin 3 → ℚ := fun _ j =>
  match j.val with
  | 0 => 1 | 1 => 1 | 2 => 2
  | _ => 0
-- Reference: smoke test: the row `(1,1,1)` does not lie in the plane.
/-- A 1×3 matrix over `ℚ` whose row does not lie in the plane of `smokeA`. -/
def smokeC : Fin 1 → Fin 3 → ℚ := fun _ j =>
  match j.val with
  | 0 => 1 | 1 => 1 | 2 => 1
  | _ => 0
#eval memRowSpanBool ratInv smokeA (smokeB 0)
#eval memRowSpanBool ratInv smokeA (smokeC 0)
#eval spanContainsBool ratInv smokeA smokeB
#eval spanContainsBool ratInv smokeA smokeC
#eval spanEqBool ratInv smokeA smokeA
#eval rrefResidualBool (rref ratInv smokeA) (smokeB 0)
#eval rrefResidualBool (rref ratInv smokeA) (smokeC 0)
#eval rankOf ratInv smokeA
#eval rankOf ratInv (matSnoc smokeA (smokeB 0))
/-! ## Axiom lint -/
#lint_axioms BoringMath.inRowSpan
#lint_axioms BoringMath.inRowSpan_self
#lint_axioms BoringMath.inRowSpan_zero
#lint_axioms BoringMath.inRowSpan_smul
#lint_axioms BoringMath.inRowSpan_add
#lint_axioms BoringMath.inRowSpan_neg
#lint_axioms BoringMath.inRowSpan_sub
#lint_axioms BoringMath.matSnoc
#lint_axioms BoringMath.matSnoc_castSucc
#lint_axioms BoringMath.matSnoc_last
#lint_axioms BoringMath.inRowSpan_snoc
#lint_axioms BoringMath.inRowSpan_mono
#lint_axioms BoringMath.inRowSpan_snoc_self
#lint_axioms BoringMath.inRowSpan_snoc_mono
#lint_axioms BoringMath.inRowSpan_snoc_of_mem
#lint_axioms BoringMath.findPivotRow_congr
#lint_axioms BoringMath.findPivotRow_some_first
#lint_axioms BoringMath.matLeadingCol_congr
#lint_axioms BoringMath.matLeadingCol_le
#lint_axioms BoringMath.findPivotRow_eq_none_of_rowZero
#lint_axioms BoringMath.rowZero_of_findPivotRow_eq_none
#lint_axioms BoringMath.matRowZero_of_matLeadingCol_eq
#lint_axioms BoringMath.entry_eq_zero_of_lt_matLeadingCol
#lint_axioms BoringMath.matLeadingCol_zero_le
#lint_axioms BoringMath.matRowNonzeroBool
#lint_axioms BoringMath.matRowNonzeroBool_true
#lint_axioms BoringMath.matRowNonzeroBool_false_of_rowZero
#lint_axioms BoringMath.matRowNonzeroBool_congr
#lint_axioms BoringMath.nzCount
#lint_axioms BoringMath.nzCount_snoc_zero
#lint_axioms BoringMath.matTail
#lint_axioms BoringMath.matRowNonzeroBool_tail
#lint_axioms BoringMath.nzCount_succ_eq
#lint_axioms BoringMath.nzCount_eq_zero_of_rowZero_zero
#lint_axioms BoringMath.nzCount_pos_of_not_rowZero_zero
#lint_axioms BoringMath.matRowSwap_row_left
#lint_axioms BoringMath.matRowSwap_row_right
#lint_axioms BoringMath.matRowSwap_row_other
#lint_axioms BoringMath.inRowSpan_swap
#lint_axioms BoringMath.matRowScale_row_self
#lint_axioms BoringMath.matRowScale_row_other
#lint_axioms BoringMath.ne_zero_invK
#lint_axioms BoringMath.inRowSpan_scale
#lint_axioms BoringMath.matRowElim_row_self
#lint_axioms BoringMath.matRowElim_row_other
#lint_axioms BoringMath.inRowSpan_elim
#lint_axioms BoringMath.inRowSpan_rrefAux
#lint_axioms BoringMath.inRowSpan_rref
#lint_axioms BoringMath.isRref_matTail
#lint_axioms BoringMath.isRref_snoc_zero
#lint_axioms BoringMath.vecLeadingCol
#lint_axioms BoringMath.vecLeadingCol_eq_some
#lint_axioms BoringMath.vecLeadingCol_eq_none
#lint_axioms BoringMath.vecLeadingCol_eq_of_zero_before
#lint_axioms BoringMath.vecLeadingCol_lt
#lint_axioms BoringMath.vecLeadingCol_ne_zero
#lint_axioms BoringMath.vecLeadingCol_vanish_before
#lint_axioms BoringMath.vecLeadingCol_lt_of_vanish
#lint_axioms BoringMath.rref_sum_at_pivot
#lint_axioms BoringMath.rrefCoeff
#lint_axioms BoringMath.rrefResidual
#lint_axioms BoringMath.inRowSpan_rref_iff
#lint_axioms BoringMath.mul_eq_zero_of_and_false
#lint_axioms BoringMath.exists_matLeadingCol_eq_vecLeadingCol
#lint_axioms BoringMath.inRowSpan_matTail_of_subset
#lint_axioms BoringMath.rref_eq_of_subset_aux
#lint_axioms BoringMath.rref_eq_of_span_eq
#lint_axioms BoringMath.rref_eq_of_subset_nzCount
#lint_axioms BoringMath.rankOf
#lint_axioms BoringMath.nzCount_rref_snoc_eq_of_mem
#lint_axioms BoringMath.mem_of_nzCount_rref_snoc_eq
#lint_axioms BoringMath.inRowSpan_iff_rankOf_snoc_eq
#lint_axioms BoringMath.memRowSpanBool
#lint_axioms BoringMath.memRowSpanBool_true_iff
#lint_axioms BoringMath.memRowSpanDecidable
#lint_axioms BoringMath.spanContainsBool
#lint_axioms BoringMath.forall_mem_finRange
#lint_axioms BoringMath.spanContains_iff_rows
#lint_axioms BoringMath.spanContainsBool_true_iff
#lint_axioms BoringMath.spanContainsDecidable
#lint_axioms BoringMath.spanEqBool
#lint_axioms BoringMath.spanEqBool_true_iff
#lint_axioms BoringMath.spanEqDecidable
#lint_axioms BoringMath.rrefResidualBool
#lint_axioms BoringMath.rrefResidualBool_true_iff
#lint_axioms BoringMath.rrefMemRowSpanDecidable
#lint_axioms BoringMath.ratInv
#lint_axioms BoringMath.smokeA
#lint_axioms BoringMath.smokeB
#lint_axioms BoringMath.smokeC
#lint_axioms BoringMath.finFinset
#lint_axioms BoringMath.finSum
#lint_axioms BoringMath.sum_finFinset
#lint_axioms BoringMath.finSum_succ
#lint_axioms BoringMath.finSum_castSucc
#lint_axioms BoringMath.sum_finFinset_succ
#lint_axioms BoringMath.sum_finFinset_castSucc
#lint_axioms BoringMath.list_sum_eq_zero
#lint_axioms BoringMath.list_sum_congr
#lint_axioms BoringMath.list_sum_eq_single
#lint_axioms BoringMath.finSum_eq_zero
#lint_axioms BoringMath.finSum_zero
#lint_axioms BoringMath.list_countP_eq_zero
#lint_axioms BoringMath.finSum_congr
#lint_axioms BoringMath.finSum_eq_single
#lint_axioms BoringMath.sum_finFinset_eq_zero
#lint_axioms BoringMath.sum_finFinset_congr
#lint_axioms BoringMath.sum_finFinset_eq_single
end BoringMath
