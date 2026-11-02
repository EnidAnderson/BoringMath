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
import BoringMath.FormalPeriods.ChainStab.Rank
/-!
# Chain stabilization theorem and toy example (P.2.4, part 2)

Piece 2 of `BoringMath.FormalPeriods.ChainStab`: the finite-pigeonhole lemma
(`exists_consec_eq_of_nondecreasing_le`), the main theorem
`span_chain_stabilizes` — an ascending chain of row spans of matrices over
`FreeMod K n` has a constant step `span (A k) = span (A (k+1))` at some depth
`k ≤ n` — its computed `Bool` form, the toy dim-2 chain over `ℚ` with
`#eval` smoke tests, and the `#lint_axioms` block for the whole module.
-/

universe u

namespace BoringMath

variable {K : Type u} [Field K] [DecidableEq K] {m n k p : ℕ}
variable (invK : K → K)

/-! ## The chain stabilization theorem -/

omit [DecidableEq K] in
-- Reference: MRR 1988, Pt. II Ch. 6 (transitivity of containment along the
-- chain); `Nat.le_induction`.
/-- Along an ascending chain, span containment is transitive: `i ≤ j`
implies `span (A i) ⊆ span (A j)`. -/
theorem span_chain_mono {A : ℕ → FreeMatrix K m n}
    (hchain : ∀ i w, inRowSpan (A i) w → inRowSpan (A (i + 1)) w) :
    ∀ i j, i ≤ j → ∀ w, inRowSpan (A i) w → inRowSpan (A j) w :=
  fun _ j hij => Nat.le_induction (fun _ hw => hw)
    (fun k _ ih _ hw => hchain k _ (ih _ hw)) j hij

-- Reference: MRR 1988, Pt. II Ch. 6 (the rank sequence of a chain is
-- nondecreasing); one step of the chain plus rank monotonicity.
/-- Along an ascending chain, the computed ranks are nondecreasing. -/
theorem rank_chain_nondecreasing (hinv : ∀ a : K, a ≠ 0 → invK a * a = 1)
    {A : ℕ → FreeMatrix K m n}
    (hchain : ∀ i w, inRowSpan (A i) w → inRowSpan (A (i + 1)) w) :
    ∀ i, rankOf invK (A i) ≤ rankOf invK (A (i + 1)) :=
  fun i => rankOf_mono_of_span_subset invK hinv (hchain i)

-- Reference: MRR 1988, Pt. II Ch. 6 (finite counting); if the minimum is
-- `< b` then the minimum is the left argument.
/-- If `min a b < b` then `min a b = a`. -/
theorem min_eq_left_of_min_lt {a b : ℕ} (h : min a b < b) : min a b = a := by
  cases (inferInstance : Decidable (a ≤ b)) with
  | isTrue hle => exact Nat.min_eq_left hle
  | isFalse hle =>
      exact False.elim (Nat.lt_irrefl b
        (Eq.subst (motive := fun t : ℕ => t < b) (Nat.min_eq_right (Nat.le_of_not_le hle)) h))

-- Reference: MRR 1988, Pt. II Ch. 6 (finite pigeonhole on dimensions: a
-- nondecreasing sequence of naturals bounded by `b` has a constant step
-- `r k = r (k+1)` with `k ≤ b`); proved by induction on `b`, compressing the
-- values with `min · b`.
/-- A nondecreasing sequence of naturals bounded by `b` has a constant step
at index `k ≤ b`. -/
theorem exists_consec_eq_of_nondecreasing_le :
    ∀ (b : ℕ) (r : ℕ → ℕ), (∀ i, r i ≤ b) → (∀ i, r i ≤ r (i + 1)) →
      ∃ k, k ≤ b ∧ r k = r (k + 1) := by
  intro b
  induction b with
  | zero =>
      intro r hb _
      exact ⟨0, Nat.le_refl 0,
        (Nat.eq_zero_of_le_zero (hb 0)).trans (Nat.eq_zero_of_le_zero (hb 1)).symm⟩
  | succ b ih =>
      intro r hb hmono
      have hsb : ∀ i, min (r i) b ≤ b := fun i => Nat.min_le_right (r i) b
      have hsmono : ∀ i, min (r i) b ≤ min (r (i + 1)) b :=
        fun i => min_le_min (hmono i) (Nat.le_refl b)
      obtain ⟨k, hk, hkeq⟩ := ih (fun j => min (r j) b) hsb hsmono
      have hkeq' : min (r k) b = min (r (k + 1)) b := hkeq
      rcases Nat.lt_or_ge (min (r k) b) b with hlt | hge
      · have h1 : min (r k) b = r k := min_eq_left_of_min_lt hlt
        have hlt' : min (r (k + 1)) b < b :=
          Eq.subst (motive := fun t : ℕ => t < b) hkeq' hlt
        have h2 : min (r (k + 1)) b = r (k + 1) := min_eq_left_of_min_lt hlt'
        exact ⟨k, Nat.le_trans hk (Nat.le_succ b), h1.symm.trans (hkeq'.trans h2)⟩
      · have hsk : min (r k) b = b := Nat.le_antisymm (Nat.min_le_right (r k) b) hge
        have hrk : b ≤ r k := (Nat.le_of_eq hsk.symm).trans (Nat.min_le_left (r k) b)
        have hsk1 : min (r (k + 1)) b = b := hkeq'.symm.trans hsk
        have hrk1 : b ≤ r (k + 1) :=
          (Nat.le_of_eq hsk1.symm).trans (Nat.min_le_left (r (k + 1)) b)
        rcases Nat.lt_or_ge (r k) (r (k + 1)) with hlt2 | hge2
        · have hrk_eq : r k = b :=
            Nat.le_antisymm (Nat.le_of_lt_succ (hlt2.trans_le (hb (k + 1)))) hrk
          have hlt3 : b < r (k + 1) := (Nat.le_of_eq hrk_eq.symm).trans_lt hlt2
          have hrk1_eq : r (k + 1) = b + 1 :=
            Nat.le_antisymm (hb (k + 1)) (Nat.succ_le_of_lt hlt3)
          have hrk2_eq : r (k + 2) = b + 1 :=
            Nat.le_antisymm (hb (k + 2))
              ((Nat.le_of_eq hrk1_eq.symm).trans (hmono (k + 1)))
          exact ⟨k + 1, Nat.succ_le_succ hk, hrk1_eq.trans hrk2_eq.symm⟩
        · exact ⟨k, Nat.le_trans hk (Nat.le_succ b), Nat.le_antisymm (hmono k) hge2⟩

-- Reference: Hörmann arXiv:2106.03803, Remark 3.3 (verified against the arXiv
-- HTML): the successive quotients of the same finite-dimensional space
-- stabilize, `P^k(M) = P^{k+1}(M) = ⋯ = P^∞(M)` for `k = dim H_B(M)`;
-- MRR 1988, Pt. II Ch. 6 (the dimension bound, computed): an ascending chain
-- of subspaces of an `n`-dimensional space has a constant step at depth
-- `≤ n` (finite pigeonhole on the computed ranks, each `≤ n` by `rankOf_le`).
/-- **Chain stabilization.** For an ascending chain of row spans of matrices
over `FreeMod K n`, there is a depth `k ≤ n` at which the chain reaches a
fixed point: `span (A k) = span (A (k+1))`. -/
theorem span_chain_stabilizes (hinv : ∀ a : K, a ≠ 0 → invK a * a = 1)
    {A : ℕ → FreeMatrix K m n}
    (hchain : ∀ i w, inRowSpan (A i) w → inRowSpan (A (i + 1)) w) :
    ∃ k, k ≤ n ∧ ∀ w : FreeMod K n, inRowSpan (A k) w ↔ inRowSpan (A (k + 1)) w := by
  obtain ⟨k, hk, hkeq⟩ := exists_consec_eq_of_nondecreasing_le n (fun i => rankOf invK (A i))
    (fun i => rankOf_le invK hinv (A i)) (fun i => rank_chain_nondecreasing invK hinv hchain i)
  exact ⟨k, hk, fun w => spanEq_of_contains_and_rankOf_eq invK hinv (hchain k) hkeq w⟩

-- Reference: issue #111 (the computed fixed point); `spanEqBool_true_iff`.
/-- The same fixed point, as a computed `Bool`: `spanEqBool` says `true` at
some depth `k ≤ n`. -/
theorem span_chain_stabilizes_bool (hinv : ∀ a : K, a ≠ 0 → invK a * a = 1)
    {A : ℕ → FreeMatrix K m n}
    (hchain : ∀ i w, inRowSpan (A i) w → inRowSpan (A (i + 1)) w) :
    ∃ k, k ≤ n ∧ spanEqBool invK (A k) (A (k + 1)) = true := by
  obtain ⟨k, hk, h⟩ := span_chain_stabilizes invK hinv hchain
  exact ⟨k, hk, (spanEqBool_true_iff invK hinv).mpr h⟩

/-! ## Toy example: a dim-2 chain with three relation steps over `ℚ` -/

-- Reference: smoke test for the acceptance criterion of issue #111 (a toy
-- chain of dimension 2 with three relation steps over `ℚ`, evaluated by
-- computation with `ratInv`).
/-- Depth 0: the zero relation set (rank 0). -/
def toyA0 : Fin 2 → Fin 2 → ℚ := fun _ _ => 0

-- Reference: smoke test (issue #111): depth 1 adds the relation `e₁`. -/
/-- Depth 1: the relation set spanned by `(1, 0)` (rank 1). -/
def toyA1 : Fin 2 → Fin 2 → ℚ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 1
  | _, _ => 0

-- Reference: smoke test (issue #111): depth 2 adds `e₂` (rank 2 = dim). -/
/-- Depth 2: the relation set spanned by `(1, 0), (0, 1)` (rank 2 = dim). -/
def toyA2 : Fin 2 → Fin 2 → ℚ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 1 | 1, 1 => 1
  | _, _ => 0

-- Reference: smoke test (issue #111): depth 3 adds `(1, 1)`, already in the
-- span (rank stays 2): the fixed point at depth 2 = dim.
/-- Depth 3: adds the relation `(1, 1)`, already in the span (fixed point). -/
def toyA3 : Fin 2 → Fin 2 → ℚ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 1 | 1, 0 => 1 | 1, 1 => 1
  | _, _ => 0

-- Reference: smoke test (issue #111): the toy chain `A 0, A 1, A 2, A 3, …`
-- with three relation steps in `FreeMod ℚ 2`.
/-- The toy chain over `ℚ` in dimension 2: zero, then `e₁`, then the full
plane, then a dependent relation. -/
def toyChain (i : ℕ) : Fin 2 → Fin 2 → ℚ :=
  match i with
  | 0 => toyA0 | 1 => toyA1 | 2 => toyA2
  | _ => toyA3

#eval rankOf ratInv (toyChain 0)
#eval rankOf ratInv (toyChain 1)
#eval rankOf ratInv (toyChain 2)
#eval rankOf ratInv (toyChain 3)
#eval rankOf ratInv (toyChain 4)
#eval spanContainsBool ratInv (toyChain 1) (toyChain 0)
#eval spanContainsBool ratInv (toyChain 2) (toyChain 1)
#eval spanContainsBool ratInv (toyChain 3) (toyChain 2)
#eval spanEqBool ratInv (toyChain 1) (toyChain 2)
#eval spanEqBool ratInv (toyChain 2) (toyChain 3)
#eval spanEqBool ratInv (toyChain 3) (toyChain 4)

/-! ## Axiom lint -/

#lint_axioms BoringMath.list_nodup_length_le_of_subset
#lint_axioms BoringMath.min_eq_left_of_min_lt
#lint_axioms BoringMath.vecLeadingCol_row
#lint_axioms BoringMath.ne_zero_of_not_matRowZero
#lint_axioms BoringMath.matLeadingCol_lt_of_matRowNonzeroBool
#lint_axioms BoringMath.matLeadingCol_ne_of_lt
#lint_axioms BoringMath.matLeadingCol_inj_on_nzFilter
#lint_axioms BoringMath.nzFilter_nodup
#lint_axioms BoringMath.nzCount_eq_filter_length
#lint_axioms BoringMath.nzFilter_map_matLeadingCol_length
#lint_axioms BoringMath.nzFilter_map_matLeadingCol_nodup
#lint_axioms BoringMath.rankOf_le
#lint_axioms BoringMath.exists_pivotCol_eq_vecLeadingCol_of_mem
#lint_axioms BoringMath.matLeadingCol_mem_map_nzFilter_of_rows_mem
#lint_axioms BoringMath.nzCount_le_of_rows_mem_rref
#lint_axioms BoringMath.rankOf_mono_of_spanContains
#lint_axioms BoringMath.rankOf_mono_of_span_subset
#lint_axioms BoringMath.inRowSpan_matSnoc_castSucc
#lint_axioms BoringMath.inRowSpan_matSnoc_last
#lint_axioms BoringMath.rows_mem_matSnoc
#lint_axioms BoringMath.rankOf_le_snoc
#lint_axioms BoringMath.spanEq_of_contains_and_rankOf_eq
#lint_axioms BoringMath.rankOf_lt_of_proper_contains
#lint_axioms BoringMath.span_chain_mono
#lint_axioms BoringMath.rank_chain_nondecreasing
#lint_axioms BoringMath.exists_consec_eq_of_nondecreasing_le
#lint_axioms BoringMath.span_chain_stabilizes
#lint_axioms BoringMath.span_chain_stabilizes_bool
#lint_axioms BoringMath.toyA0
#lint_axioms BoringMath.toyA1
#lint_axioms BoringMath.toyA2
#lint_axioms BoringMath.toyA3
#lint_axioms BoringMath.toyChain
end BoringMath
