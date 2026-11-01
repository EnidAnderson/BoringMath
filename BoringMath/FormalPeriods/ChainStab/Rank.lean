/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Init
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import BoringMath.FormalPeriods.DecidableSubspace
/-!
# Computed rank: pivot bound, monotonicity, equality criterion (P.2.4, part 1)

Piece 1 of `BoringMath.FormalPeriods.ChainStab`: the counting layer behind the
chain-stabilization engine — a nodup list inside another list is no longer,
the pivot columns of an RREF matrix are distinct, so the computed rank is
bounded by the number of columns (`rankOf_le`); rank monotonicity under
span containment; and containment plus equal computed rank forcing equality
of spans (`spanEq_of_contains_and_rankOf_eq`), with strictness for proper
containment (`rankOf_lt_of_proper_contains`).
-/

universe u

namespace BoringMath

variable {K : Type u} [Field K] [DecidableEq K] {m n k p : ℕ}
variable (invK : K → K)

/-! ## List counting: a nodup list of elements of a list is no longer -/

-- Reference: MRR 1988, Pt. II Ch. 6 (finite pigeonhole); a nodup list whose
-- elements all lie in `l₂` is a subperm of `l₂` (`List.Nodup.subperm`), and
-- subperms are no longer (`List.Subperm.length_le`).
/-- A nodup list all of whose elements lie in `l₂` is no longer than `l₂`. -/
theorem list_nodup_length_le_of_subset {l₁ l₂ : List ℕ} (h₁ : l₁.Nodup)
    (hsub : ∀ x ∈ l₁, x ∈ l₂) : l₁.length ≤ l₂.length :=
  List.Subperm.length_le (List.Nodup.subperm h₁ hsub)

/-! ## Pivot columns of an RREF matrix and the rank bound -/

-- Reference: definitional peel: `vecLeadingCol` of a row and `matLeadingCol`
-- of the row are the same pivot search.
/-- The leading column of the vector `A a` (a row of `A`) is `matLeadingCol A a`. -/
theorem vecLeadingCol_row (A : FreeMatrix K m n) (a : Fin m) :
    vecLeadingCol (A a) = matLeadingCol A a := rfl

omit [DecidableEq K] in
-- Reference: MRR 1988, Pt. II Ch. 6 (a row is zero iff all its entries are).
/-- A row that is not zero is a nonzero vector. -/
theorem ne_zero_of_not_matRowZero {A : FreeMatrix K m n} {a : Fin m}
    (h : ¬ matRowZero A a) : A a ≠ 0 :=
  fun heq => h (fun c => (congrFun heq c).trans (Pi.zero_apply c))

-- Reference: MRR 1988, Pt. II Ch. 6 (a nonzero row has a pivot column `< n`);
-- `exists_matLeadingCol_eq_vecLeadingCol_lt`.
/-- A row testing nonzero has leading column `< n`. -/
theorem matLeadingCol_lt_of_matRowNonzeroBool {R : FreeMatrix K m n} {a : Fin m}
    (h : matRowNonzeroBool R a = true) : matLeadingCol R a < n :=
  exists_matLeadingCol_eq_vecLeadingCol_lt (matRowNonzeroBool_true.mp h)

-- Reference: MRR 1988, Pt. II Ch. 6 (pivot columns strictly increase down an
-- RREF matrix); the third component of `IsRref`.
/-- Pivot columns of two rows of an RREF matrix with `a < b` and row `b`
nonzero are distinct. -/
theorem matLeadingCol_ne_of_lt {R : FreeMatrix K m n} (hR : IsRref R) {a b : Fin m}
    (hlt : a < b) (hb : matRowNonzeroBool R b = true) :
    matLeadingCol R a ≠ matLeadingCol R b :=
  Nat.ne_of_lt (hR.2.2.1 a b hlt (matRowNonzeroBool_true.mp hb))

-- Reference: MRR 1988, Pt. II Ch. 6 (pivot columns are distinct); the
-- trichotomy on the row indices.
/-- The leading-column map is injective on the nonzero-test rows. -/
theorem matLeadingCol_inj_on_nzFilter {R : FreeMatrix K m n} (hR : IsRref R) :
    ∀ a ∈ (List.finRange m).filter (matRowNonzeroBool R),
      ∀ b ∈ (List.finRange m).filter (matRowNonzeroBool R),
        matLeadingCol R a = matLeadingCol R b → a = b := by
  intro a ha b hb heq
  rcases Nat.lt_trichotomy a.val b.val with h | h | h
  · exact absurd heq (matLeadingCol_ne_of_lt hR (Fin.lt_def.mpr h) (List.mem_filter.mp hb).2)
  · exact Fin.eq_of_val_eq h
  · exact absurd heq.symm
      (matLeadingCol_ne_of_lt hR (Fin.lt_def.mpr h) (List.mem_filter.mp ha).2)

-- Reference: MRR 1988, Pt. II Ch. 6; the nonzero-test rows of `finRange m`
-- form a nodup list (a sublist of the nodup `finRange`).
/-- The list of nonzero-test rows is nodup. -/
theorem nzFilter_nodup (R : FreeMatrix K m n) :
    ((List.finRange m).filter (matRowNonzeroBool R)).Nodup :=
  List.Nodup.sublist (List.filter_sublist (p := matRowNonzeroBool R) (l := List.finRange m))
    (List.nodup_finRange m)

-- Reference: MRR 1988, Pt. II Ch. 6 (the rank is a count); `countP` is the
-- length of the filter (`List.countP_eq_length_filter`).
/-- The nonzero-row count is the length of the nonzero-test filter list. -/
theorem nzCount_eq_filter_length (B : FreeMatrix K m n) :
    nzCount B = ((List.finRange m).filter (matRowNonzeroBool B)).length := by
  unfold nzCount
  exact List.countP_eq_length_filter (p := matRowNonzeroBool B) (l := List.finRange m)

-- Reference: MRR 1988, Pt. II Ch. 6; mapping does not change the length
-- (`List.length_map`).
/-- The mapped nonzero-test filter list has the same length. -/
theorem nzFilter_map_matLeadingCol_length {R : FreeMatrix K m n} :
    (((List.finRange m).filter (matRowNonzeroBool R)).map (matLeadingCol R)).length
      = ((List.finRange m).filter (matRowNonzeroBool R)).length :=
  List.length_map (f := matLeadingCol R)

-- Reference: MRR 1988, Pt. II Ch. 6 (pivot columns are distinct); nodup is
-- preserved by an injective-on-the-list map (`List.Nodup.map_on`).
/-- The pivot columns of the nonzero rows form a nodup list. -/
theorem nzFilter_map_matLeadingCol_nodup {R : FreeMatrix K m n} (hR : IsRref R) :
    (((List.finRange m).filter (matRowNonzeroBool R)).map (matLeadingCol R)).Nodup :=
  List.Nodup.map_on (matLeadingCol_inj_on_nzFilter hR) (nzFilter_nodup R)

-- Reference: MRR 1988, Pt. II Ch. 6 (the rank is at most the number of
-- columns: the nonzero rows of the RREF have distinct pivot columns, all
-- `< n`); Hörmann arXiv:2106.03803 Remark 3.3 (the dimension bound).
/-- The computed rank of `A` is at most `n`, the number of columns: the
pivot columns of the RREF form a nodup list inside `List.range n`. -/
theorem rankOf_le (hinv : ∀ a : K, a ≠ 0 → invK a * a = 1) (A : FreeMatrix K m n) :
    rankOf invK A ≤ n := by
  have hR : IsRref (rref invK A) := rref_isRref invK hinv A
  have hlen : nzCount (rref invK A)
      = (((List.finRange m).filter (matRowNonzeroBool (rref invK A))).map
          (matLeadingCol (rref invK A))).length :=
    (nzCount_eq_filter_length (rref invK A)).trans nzFilter_map_matLeadingCol_length.symm
  have hsub : ∀ x ∈ ((List.finRange m).filter (matRowNonzeroBool (rref invK A))).map
      (matLeadingCol (rref invK A)), x ∈ List.range n := by
    intro x hx
    obtain ⟨a, ha, he⟩ := List.mem_map.mp hx
    exact List.mem_range.mpr (Eq.subst (motive := fun t : ℕ => t < n) he
      (matLeadingCol_lt_of_matRowNonzeroBool (List.mem_filter.mp ha).2))
  have hle := list_nodup_length_le_of_subset (nzFilter_map_matLeadingCol_nodup hR) hsub
  show nzCount (rref invK A) ≤ n
  exact (Nat.le_of_eq hlen).trans (hle.trans (Nat.le_of_eq List.length_range))

/-! ## Rank monotonicity under containment of spans -/

-- Reference: MRR 1988, Pt. II Ch. 6 (the leading column of a nonzero element
-- of the span of an RREF matrix is a pivot column);
-- `exists_matLeadingCol_eq_vecLeadingCol`.
/-- A nonzero vector in the row span of an RREF matrix has, as its leading
column, a pivot column of the matrix. -/
theorem exists_pivotCol_eq_vecLeadingCol_of_mem {S : FreeMatrix K p n} (hS : IsRref S)
    {w : FreeMod K n} (hw : inRowSpan S w) (hw0 : w ≠ 0) :
    ∃ b : Fin p, matRowNonzeroBool S b = true ∧ matLeadingCol S b = vecLeadingCol w :=
  let ⟨b, hb, hlc⟩ := exists_matLeadingCol_eq_vecLeadingCol hS hw hw0
  ⟨b, matRowNonzeroBool_true.mpr hb, hlc⟩

-- Reference: MRR 1988, Pt. II Ch. 6 (every pivot column of `R` is a pivot
-- column of `S` when the rows of `R` lie in the span of `S`).
/-- If every row of `R` lies in the span of the RREF matrix `S`, then every
pivot column of `R` is a pivot column of `S`. -/
theorem matLeadingCol_mem_map_nzFilter_of_rows_mem {R : FreeMatrix K m n}
    {S : FreeMatrix K p n} (hS : IsRref S) (h : ∀ a : Fin m, inRowSpan S (R a)) :
    ∀ x ∈ ((List.finRange m).filter (matRowNonzeroBool R)).map (matLeadingCol R),
      x ∈ ((List.finRange p).filter (matRowNonzeroBool S)).map (matLeadingCol S) := by
  intro x hx
  obtain ⟨a, ha, he⟩ := List.mem_map.mp hx
  have hb := (List.mem_filter.mp ha).2
  have hw0 : R a ≠ 0 := ne_zero_of_not_matRowZero (matRowNonzeroBool_true.mp hb)
  obtain ⟨b, hbS, hlc⟩ := exists_pivotCol_eq_vecLeadingCol_of_mem hS (h a) hw0
  refine List.mem_map.mpr ⟨b, List.mem_filter.mpr ⟨List.mem_finRange b, hbS⟩, ?_⟩
  exact (hlc.trans (vecLeadingCol_row R a)).trans he

-- Reference: MRR 1988, Pt. II Ch. 6 (the nonzero rows of an RREF matrix
-- inside another span are no more than the pivot columns of the latter).
/-- If every row of the RREF matrix `R` lies in the span of the RREF matrix
`S`, then the nonzero-row count of `R` is at most that of `S`. -/
theorem nzCount_le_of_rows_mem_rref {R : FreeMatrix K m n} {S : FreeMatrix K p n}
    (hR : IsRref R) (hS : IsRref S) (h : ∀ a : Fin m, inRowSpan S (R a)) :
    nzCount R ≤ nzCount S := by
  have h1 : nzCount R = (((List.finRange m).filter (matRowNonzeroBool R)).map
      (matLeadingCol R)).length :=
    (nzCount_eq_filter_length R).trans nzFilter_map_matLeadingCol_length.symm
  have h2 : nzCount S = (((List.finRange p).filter (matRowNonzeroBool S)).map
      (matLeadingCol S)).length :=
    (nzCount_eq_filter_length S).trans nzFilter_map_matLeadingCol_length.symm
  have hle := list_nodup_length_le_of_subset (nzFilter_map_matLeadingCol_nodup hR)
    (matLeadingCol_mem_map_nzFilter_of_rows_mem hS h)
  exact (Nat.le_of_eq h1).trans (hle.trans (Nat.le_of_eq h2.symm))

-- Reference: MRR 1988, Pt. II Ch. 6 (containment of spans gives rank
-- monotonicity: `span B ⊆ span A` implies `rank B ≤ rank A`, via the RREFs
-- and `inRowSpan_rref`).
/-- If every row of `B` lies in the row span of `A`, then the computed rank
of `B` is at most that of `A`. -/
theorem rankOf_mono_of_spanContains (hinv : ∀ a : K, a ≠ 0 → invK a * a = 1)
    {A : FreeMatrix K m n} {B : FreeMatrix K p n}
    (h : ∀ b : Fin p, inRowSpan A (B b)) : rankOf invK B ≤ rankOf invK A := by
  have hR : IsRref (rref invK B) := rref_isRref invK hinv B
  have hS : IsRref (rref invK A) := rref_isRref invK hinv A
  have hrows : ∀ a : Fin p, inRowSpan (rref invK A) (rref invK B a) := fun a =>
    (inRowSpan_rref invK hinv A (rref invK B a)).mpr ((spanContains_iff_rows.mp h)
      (rref invK B a) ((inRowSpan_rref invK hinv B (rref invK B a)).mp
        (inRowSpan_self (rref invK B) a)))
  have hle := nzCount_le_of_rows_mem_rref hR hS hrows
  show nzCount (rref invK B) ≤ nzCount (rref invK A)
  exact hle

-- Reference: MRR 1988, Pt. II Ch. 6; the `∀ w` form of containment, via
-- `spanContains_iff_rows`.
/-- If the row span of `B` is contained in the row span of `A`, then the
computed rank of `B` is at most that of `A`. -/
theorem rankOf_mono_of_span_subset (hinv : ∀ a : K, a ≠ 0 → invK a * a = 1)
    {A : FreeMatrix K m n} {B : FreeMatrix K p n}
    (h : ∀ w : FreeMod K n, inRowSpan B w → inRowSpan A w) :
    rankOf invK B ≤ rankOf invK A :=
  rankOf_mono_of_spanContains invK hinv (spanContains_iff_rows.mpr h)

/-! ## Equality and strictness of ranks -/

omit [DecidableEq K] in
-- Reference: MRR 1988, Pt. II Ch. 6 (the rows of `A` are rows of `matSnoc A v`
-- up to the `castSucc` peel `matSnoc_castSucc`).
/-- A row of `A` lies in the span of `B` as a row of `matSnoc A v`. -/
theorem inRowSpan_matSnoc_castSucc {A : FreeMatrix K m n} {B : FreeMatrix K p n}
    {v : FreeMod K n} (a : Fin m) (h : inRowSpan B (A a)) :
    inRowSpan B (matSnoc A v (Fin.castSucc a)) :=
  Eq.mpr (congrArg (inRowSpan B) (funext (fun c => matSnoc_castSucc A v a c))) h

omit [DecidableEq K] in
-- Reference: MRR 1988, Pt. II Ch. 6 (the appended vector is the last row,
-- peel `matSnoc_last`).
/-- The appended vector, as the last row of `matSnoc A v`, lies in `B`'s span. -/
theorem inRowSpan_matSnoc_last {A : FreeMatrix K m n} {B : FreeMatrix K p n}
    {v : FreeMod K n} (h : inRowSpan B v) :
    inRowSpan B (matSnoc A v (Fin.last m)) :=
  Eq.mpr (congrArg (inRowSpan B) (funext (fun c => matSnoc_last A v c))) h

omit [DecidableEq K] in
-- Reference: MRR 1988, Pt. II Ch. 6; case split `Fin.eq_castSucc_or_eq_last`.
/-- If every row of `A` and the vector `v` lie in the span of `B`, then every
row of `matSnoc A v` lies in the span of `B`. -/
theorem rows_mem_matSnoc {A : FreeMatrix K m n} {B : FreeMatrix K p n} {v : FreeMod K n}
    (hA : ∀ a : Fin m, inRowSpan B (A a)) (hv : inRowSpan B v) :
    ∀ b : Fin (m + 1), inRowSpan B (matSnoc A v b) := fun b =>
  match Fin.eq_castSucc_or_eq_last b with
  | Or.inl ⟨a, ha⟩ =>
      Eq.mpr (congrArg (fun z => inRowSpan B (matSnoc A v z)) ha)
        (inRowSpan_matSnoc_castSucc a (hA a))
  | Or.inr ha =>
      Eq.mpr (congrArg (fun z => inRowSpan B (matSnoc A v z)) ha)
        (inRowSpan_matSnoc_last hv)

-- Reference: MRR 1988, Pt. II Ch. 6 (appending a row only grows the span).
/-- The computed rank grows by appending a row: `rankOf A ≤ rankOf (A; v)`. -/
theorem rankOf_le_snoc (hinv : ∀ a : K, a ≠ 0 → invK a * a = 1)
    {A : FreeMatrix K m n} {v : FreeMod K n} :
    rankOf invK A ≤ rankOf invK (matSnoc A v) :=
  rankOf_mono_of_spanContains invK hinv (fun a =>
    Eq.mpr (congrArg (inRowSpan (matSnoc A v))
      (funext (fun c => matSnoc_castSucc A v a c)).symm)
      (inRowSpan_self (matSnoc A v) (Fin.castSucc a)))

-- Reference: MRR 1988, Pt. II Ch. 6 (containment plus equal rank gives
-- equality of spans; here via the rank criterion
-- `inRowSpan_iff_rankOf_snoc_eq`: `rankOf (A; w) = rankOf A` forces
-- `w ∈ span A`).
/-- If the span of `A` is contained in the span of `B` and the computed ranks
are equal, then the spans are equal. -/
theorem spanEq_of_contains_and_rankOf_eq (hinv : ∀ a : K, a ≠ 0 → invK a * a = 1)
    {A : FreeMatrix K m n} {B : FreeMatrix K p n}
    (hsub : ∀ w : FreeMod K n, inRowSpan A w → inRowSpan B w)
    (hrank : rankOf invK A = rankOf invK B) :
    ∀ w : FreeMod K n, inRowSpan A w ↔ inRowSpan B w :=
  fun w => ⟨hsub w, fun hwB => by
    have hrowsA : ∀ a : Fin m, inRowSpan B (A a) := fun a => hsub (A a) (inRowSpan_self A a)
    have hle1 : rankOf invK A ≤ rankOf invK (matSnoc A w) := rankOf_le_snoc invK hinv
    have hle2 : rankOf invK (matSnoc A w) ≤ rankOf invK B :=
      rankOf_mono_of_spanContains invK hinv (rows_mem_matSnoc hrowsA hwB)
    have heq : rankOf invK (matSnoc A w) = rankOf invK A :=
      Nat.le_antisymm (hle2.trans (Nat.le_of_eq hrank.symm)) hle1
    exact (inRowSpan_iff_rankOf_snoc_eq invK hinv).mpr heq⟩

-- Reference: MRR 1988, Pt. II Ch. 6 (proper containment strictly increases
-- the rank); `Nat.lt_iff_le_and_ne` with monotonicity and the equality lemma.
/-- If the span of `A` is properly contained in the span of `B`, then the
computed rank of `A` is strictly less than that of `B`. -/
theorem rankOf_lt_of_proper_contains (hinv : ∀ a : K, a ≠ 0 → invK a * a = 1)
    {A : FreeMatrix K m n} {B : FreeMatrix K p n}
    (hsub : ∀ w : FreeMod K n, inRowSpan A w → inRowSpan B w)
    (hne : ¬ ∀ w : FreeMod K n, inRowSpan B w → inRowSpan A w) :
    rankOf invK A < rankOf invK B :=
  Nat.lt_iff_le_and_ne.mpr ⟨rankOf_mono_of_span_subset invK hinv hsub,
    fun heq => hne (fun w hw =>
      (spanEq_of_contains_and_rankOf_eq invK hinv hsub heq w).mpr hw)⟩

end BoringMath
