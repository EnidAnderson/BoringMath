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
import BoringMath.FormalPeriods.FreeMod
import BoringMath.FormalPeriods.RowReduction
/-!
# The row span of an explicit spanning set, and appending a row (P.2.3, part 2)

Piece 2 of `BoringMath.FormalPeriods.DecidableSubspace`: `inRowSpan` (an
explicit linear combination of the rows, pointwise in the coordinates), its
algebra operations, `matSnoc`, and the monotonicity lemmas for appending a
row to the spanning set.
-/
universe u
namespace BoringMath
open BigOperators
variable {K : Type u} [Field K] {m n k p : ℕ}
/-! ## The row span of an explicit spanning set -/
-- Reference: Mines–Richman–Ruitenburg 1988, Pt. II Ch. 6 (row space of a
-- matrix over a discrete field); Axler, Ch. 1 (span = linear combinations).
/-- `v` lies in the row span of `A`: an explicit linear combination of the
rows of `A`, stated pointwise in the coordinates. -/
def inRowSpan (A : FreeMatrix K m n) (v : FreeMod K n) : Prop :=
  ∃ c : Fin m → K, ∀ j : Fin n, v j = ∑ a ∈ finFinset _, c a * A a j
-- Reference: MRR 1988, Pt. II Ch. 6 (a row lies in its own row space).
/-- Every row of `A` lies in the row span of `A`. -/
theorem inRowSpan_self (A : FreeMatrix K m n) (b : Fin m) : inRowSpan A (A b) :=
  ⟨fun a => if a = b then 1 else 0, fun j =>
    let hs := sum_finFinset_eq_single (f := fun a => (if a = b then 1 else 0) * A a j)
      (fun a hab => (congrArg (· * A a j) (ite_eq_right hab)).trans (zero_mul (A a j)))
    let e : (if b = b then 1 else 0) * A b j = A b j :=
      (congrArg (· * A b j) (ite_eq_left (Eq.refl b))).trans (one_mul (A b j))
    (hs.trans e).symm⟩
-- Reference: MRR 1988, Pt. II Ch. 6 (the zero vector is in every span).
/-- The zero vector lies in the row span of `A`. -/
theorem inRowSpan_zero (A : FreeMatrix K m n) : inRowSpan A 0 :=
  ⟨fun _ => 0, fun _ => (sum_finFinset_eq_zero (fun _ => zero_mul _)).symm⟩
-- Reference: MRR 1988, Pt. II Ch. 6 (spans are closed under scalar
-- multiplication).
/-- The row span is closed under scalar multiplication. -/
theorem inRowSpan_smul (c : K) {A : FreeMatrix K m n} {v : FreeMod K n}
    (h : inRowSpan A v) : inRowSpan A (c • v) :=
  let ⟨d, hd⟩ := h
  ⟨fun a => c * d a, fun j =>
    (Pi.smul_apply c v j).trans ((congrArg (c * ·) (hd j)).trans
      ((Finset.mul_sum _ _ c).trans (sum_finFinset_congr (fun a =>
        (mul_assoc c (d a) (A a j)).symm))))⟩
-- Reference: MRR 1988, Pt. II Ch. 6 (spans are closed under addition).
/-- The row span is closed under addition. -/
theorem inRowSpan_add {A : FreeMatrix K m n} {u v : FreeMod K n}
    (hu : inRowSpan A u) (hv : inRowSpan A v) : inRowSpan A (u + v) :=
  let ⟨cu, hu'⟩ := hu
  let ⟨cv, hv'⟩ := hv
  ⟨fun a => cu a + cv a, fun j =>
    (Pi.add_apply u v j).trans ((congrArg₂ (· + ·) (hu' j) (hv' j)).trans
      ((Finset.sum_add_distrib).symm.trans (sum_finFinset_congr (fun a =>
        (add_mul (cu a) (cv a) (A a j)).symm))))⟩
-- Reference: MRR 1988, Pt. II Ch. 6 (spans are closed under negation).
/-- The row span is closed under negation. -/
theorem inRowSpan_neg {A : FreeMatrix K m n} {v : FreeMod K n} (h : inRowSpan A v) :
    inRowSpan A (-v) :=
  let ⟨d, hd⟩ := h
  ⟨fun a => -d a, fun j =>
    (Pi.neg_apply v j).trans ((congrArg (-·) (hd j)).trans
      (((Finset.sum_neg_distrib _).symm).trans (sum_finFinset_congr (fun a =>
        (neg_mul (d a) (A a j)).symm))))⟩
-- Reference: MRR 1988, Pt. II Ch. 6 (spans are closed under subtraction).
/-- The row span is closed under subtraction. -/
theorem inRowSpan_sub {A : FreeMatrix K m n} {u v : FreeMod K n}
    (hu : inRowSpan A u) (hv : inRowSpan A v) : inRowSpan A (u - v) :=
  Eq.mpr (congrArg (inRowSpan A) (sub_eq_add_neg u v)) (inRowSpan_add hu (inRowSpan_neg hv))
/-! ## Appending a row to the spanning set -/
-- Reference: MRR 1988, Pt. II Ch. 6 (appending a generator to a spanning set).
/-- Append the vector `v` as a new last row of `A`. -/
def matSnoc (A : FreeMatrix K m n) (v : FreeMod K n) : FreeMatrix K (m + 1) n :=
  fun a c => if h : a.val < m then A ⟨a.val, h⟩ c else v c
-- Reference: definitional peel of `matSnoc` at a `castSucc` row.
/-- The old rows of `A` are unchanged by `matSnoc`. -/
theorem matSnoc_castSucc (A : FreeMatrix K m n) (v : FreeMod K n) (a : Fin m) (c : Fin n) :
    matSnoc A v (Fin.castSucc a) c = A a c :=
  dite_eq_left a.isLt
-- Reference: definitional peel of `matSnoc` at the last row.
/-- The appended vector is the last row of `matSnoc A v`. -/
theorem matSnoc_last (A : FreeMatrix K m n) (v : FreeMod K n) (c : Fin n) :
    matSnoc A v (Fin.last m) c = v c :=
  dite_eq_right (Nat.lt_irrefl m)
-- Reference: MRR 1988, Pt. II Ch. 6 (the sum over the appended matrix splits
-- at the last row); peel of `sum_finFinset_castSucc` along `matSnoc`.
/-- The `finFinset` sum of `c a * matSnoc A v a j` splits at the last row. -/
theorem inRowSpan_snoc_sum_fwd {A : FreeMatrix K m n} {v : FreeMod K n}
    (c : Fin (m + 1) → K) (j : Fin n) :
    ∑ a ∈ finFinset (m + 1), c a * matSnoc A v a j
      = (∑ a ∈ finFinset m, c (Fin.castSucc a) * A a j) + c (Fin.last m) * v j := by
  have h2 : ∑ a ∈ finFinset (m + 1), c a * matSnoc A v a j
      = (∑ a ∈ finFinset m, c (Fin.castSucc a) * matSnoc A v (Fin.castSucc a) j)
        + c (Fin.last m) * matSnoc A v (Fin.last m) j :=
    sum_finFinset_castSucc (fun a : Fin (m + 1) => c a * matSnoc A v a j)
  have hcast : (∑ a ∈ finFinset m, c (Fin.castSucc a) * matSnoc A v (Fin.castSucc a) j)
      = ∑ a ∈ finFinset m, c (Fin.castSucc a) * A a j :=
    sum_finFinset_congr (fun a =>
      congrArg (c (Fin.castSucc a) * ·) (matSnoc_castSucc A v a j))
  have hlast : c (Fin.last m) * matSnoc A v (Fin.last m) j = c (Fin.last m) * v j :=
    congrArg (c (Fin.last m) * ·) (matSnoc_last A v j)
  exact h2.trans ((congrArg (· + c (Fin.last m) * matSnoc A v (Fin.last m) j) hcast).trans
    (congrArg ((∑ a ∈ finFinset m, c (Fin.castSucc a) * A a j) + ·) hlast))
-- Reference: MRR 1988, Pt. II Ch. 6 (the `dite`-coefficient sum reassembled
-- coefficient); peel of `sum_finFinset_castSucc` along the `dite` rows.
/-- The `finFinset` sum of a `dite` coefficient against `matSnoc` splits. -/
theorem inRowSpan_snoc_sum_bwd {A : FreeMatrix K m n} {v : FreeMod K n}
    (c : Fin m → K) (d : K) (j : Fin n) :
    ∑ a ∈ finFinset (m + 1),
        (if h : a.val < m then c ⟨a.val, h⟩ else d) * matSnoc A v a j
      = (∑ a ∈ finFinset m, c a * A a j) + d * v j := by
  have h2 : ∑ a ∈ finFinset (m + 1),
        (if h : a.val < m then c ⟨a.val, h⟩ else d) * matSnoc A v a j
      = (∑ a ∈ finFinset m, (if h : (Fin.castSucc a).val < m then
            c ⟨(Fin.castSucc a).val, h⟩ else d) * matSnoc A v (Fin.castSucc a) j)
        + (if h : (Fin.last m).val < m then c ⟨(Fin.last m).val, h⟩ else d)
          * matSnoc A v (Fin.last m) j :=
    sum_finFinset_castSucc (fun a : Fin (m + 1) =>
      (if h : a.val < m then c ⟨a.val, h⟩ else d) * matSnoc A v a j)
  have hcast : (∑ a ∈ finFinset m, (if h : (Fin.castSucc a).val < m then
        c ⟨(Fin.castSucc a).val, h⟩ else d) * matSnoc A v (Fin.castSucc a) j)
      = ∑ a ∈ finFinset m, c a * A a j :=
    sum_finFinset_congr (fun a =>
      ((congrArg (fun z => (if h : z < m then c ⟨z, h⟩ else d)
          * matSnoc A v (Fin.castSucc a) j) (Fin.val_castSucc a)).trans
        (congrArg (· * matSnoc A v (Fin.castSucc a) j) (dite_eq_left a.isLt))).trans
        (congrArg (c ⟨a.val, a.isLt⟩ * ·) (matSnoc_castSucc A v a j)))
  have hlast : (if h : (Fin.last m).val < m then c ⟨(Fin.last m).val, h⟩ else d)
      * matSnoc A v (Fin.last m) j = d * v j :=
    ((congrArg (fun z => (if h : z < m then c ⟨z, h⟩ else d)
        * matSnoc A v (Fin.last m) j) (Fin.val_last m)).trans
      (congrArg (· * matSnoc A v (Fin.last m) j)
        (dite_eq_right (Nat.lt_irrefl m)))).trans
      (congrArg (d * ·) (matSnoc_last A v j))
  exact h2.trans ((congrArg (· + (if h : (Fin.last m).val < m then c ⟨(Fin.last m).val, h⟩ else d)
        * matSnoc A v (Fin.last m) j) hcast).trans
    (congrArg ((∑ a ∈ finFinset m, c a * A a j) + ·) hlast))
-- Reference: MRR 1988, Pt. II Ch. 6 (span of a spanning set with one more
-- generator: `span(S ∪ {v}) = span S + K v`); forward direction.
/-- Forward direction of the snoc membership decomposition: read the coefficient of
the appended row off the last summand. -/
theorem inRowSpan_snoc_mp {A : FreeMatrix K m n} {v w : FreeMod K n}
    (h : inRowSpan (matSnoc A v) w) :
    ∃ u : FreeMod K n, inRowSpan A u ∧ ∃ d : K, ∀ j : Fin n, w j = u j + d * v j :=
  let ⟨c, hc⟩ := h
  ⟨fun j => ∑ a ∈ finFinset m, c (Fin.castSucc a) * A a j,
    ⟨fun a => c (Fin.castSucc a), fun _ => rfl⟩, c (Fin.last m), fun j =>
      (hc j).trans (inRowSpan_snoc_sum_fwd c j)⟩
-- Reference: MRR 1988, Pt. II Ch. 6 (span of a spanning set with one more
-- generator: `span(S ∪ {v}) = span S + K v`); backward direction.
/-- Backward direction of the snoc membership decomposition: reassemble the
combination with a `dite` coefficient. -/
theorem inRowSpan_snoc_mpr {A : FreeMatrix K m n} {v w : FreeMod K n}
    (h : ∃ u : FreeMod K n, inRowSpan A u ∧ ∃ d : K, ∀ j : Fin n, w j = u j + d * v j) :
    inRowSpan (matSnoc A v) w :=
  let ⟨u, ⟨c, hc⟩, d, hw⟩ := h
  ⟨fun a => if h : a.val < m then c ⟨a.val, h⟩ else d, fun j =>
    ((hw j).trans (congrArg (· + d * v j) (hc j))).trans
      (inRowSpan_snoc_sum_bwd c d j).symm⟩
-- Reference: MRR 1988, Pt. II Ch. 6 (span of a spanning set with one more
-- generator: `span(S ∪ {v}) = span S + K v`).
/-- Membership in the row span after appending one row: `w` is in
`span(rows A ∪ {v})` iff `w = u + d • v` pointwise with `u` in the row span
of `A`. -/
theorem inRowSpan_snoc {A : FreeMatrix K m n} {v w : FreeMod K n} :
    inRowSpan (matSnoc A v) w ↔
      ∃ u : FreeMod K n, inRowSpan A u ∧ ∃ d : K, ∀ j : Fin n, w j = u j + d * v j :=
  ⟨fun h => inRowSpan_snoc_mp h, fun h => inRowSpan_snoc_mpr h⟩
-- Reference: MRR 1988, Pt. II Ch. 6 (a matrix is the snoc of its tail and
-- its last row); definitional peel.
/-- Every matrix is the `matSnoc` of its `castSucc` rows and its last row. -/
theorem matSnoc_tail_last (A : FreeMatrix K (k + 1) n) :
    A = matSnoc (fun a : Fin k => A (Fin.castSucc a)) (A (Fin.last k)) :=
  funext fun a => funext fun c =>
    match Fin.eq_castSucc_or_eq_last a with
    | Or.inl ⟨a', ha'⟩ =>
        Eq.mp (congrArg (fun z => A z c = matSnoc (fun a' => A (Fin.castSucc a'))
            (A (Fin.last k)) z c) ha'.symm)
          (matSnoc_castSucc (fun a' => A (Fin.castSucc a')) (A (Fin.last k)) a' c).symm
    | Or.inr ha' =>
        Eq.mp (congrArg (fun z => A z c = matSnoc (fun a' => A (Fin.castSucc a'))
            (A (Fin.last k)) z c) ha'.symm)
          (matSnoc_last (fun a' => A (Fin.castSucc a')) (A (Fin.last k)) c).symm
-- Reference: MRR 1988, Pt. II Ch. 6 (if every generator of `S` lies in the
-- span of `T` then `span S ⊆ span T`); zero-row case.
/-- The zero-row case of the span monotonicity induction. -/
theorem inRowSpan_mono_zero {p : ℕ} {B : FreeMatrix K p n} (A : FreeMatrix K 0 n)
    (w : FreeMod K n) (hw : inRowSpan A w) : inRowSpan B w :=
  let ⟨c, hc⟩ := hw
  ⟨fun _ => 0, fun j =>
    ((hc j).trans ((sum_finFinset (fun a => c a * A a j)).trans finSum_zero)).trans
      (sum_finFinset_eq_zero (fun _ => zero_mul (B _ j))).symm⟩
-- Reference: MRR 1988, Pt. II Ch. 6 (if every generator of `S` lies in the
-- span of `T` then `span S ⊆ span T`); successor case, peeling the last row.
/-- The successor case of the span monotonicity induction. -/
theorem inRowSpan_mono_succ {p : ℕ} {B : FreeMatrix K p n} (k : ℕ)
    (ih : ∀ (A : FreeMatrix K k n) (w : FreeMod K n),
      (∀ a : Fin k, inRowSpan B (A a)) → inRowSpan A w → inRowSpan B w)
    (A : FreeMatrix K (k + 1) n) (w : FreeMod K n)
    (h : ∀ a : Fin (k + 1), inRowSpan B (A a)) (hw : inRowSpan A w) :
    inRowSpan B w :=
  let M := fun a : Fin k => A (Fin.castSucc a)
  let v := A (Fin.last k)
  let hsplit := matSnoc_tail_last A
  let hw' : inRowSpan (matSnoc M v) w :=
    Eq.mp (congrArg (fun M' => inRowSpan M' w) hsplit) hw
  let h' : ∀ a : Fin (k + 1), inRowSpan B (matSnoc M v a) :=
    fun a => Eq.mp (congrArg (fun M' => inRowSpan B (M' a)) hsplit) (h a)
  let ⟨u, hu, d, hwu⟩ := inRowSpan_snoc.mp hw'
  let hcast : ∀ a : Fin k, matSnoc M v (Fin.castSucc a) = A (Fin.castSucc a) :=
    fun a => funext (fun c => matSnoc_castSucc _ _ a c)
  let hlast : matSnoc M v (Fin.last k) = A (Fin.last k) := funext (fun c => matSnoc_last _ _ c)
  let hrows : ∀ a : Fin k, inRowSpan B (A (Fin.castSucc a)) :=
    fun a => Eq.mp (congrArg (inRowSpan B) (hcast a)) (h' (Fin.castSucc a))
  let huB : inRowSpan B u := ih M u hrows hu
  let hvB : inRowSpan B (A (Fin.last k)) :=
    Eq.mp (congrArg (inRowSpan B) hlast) (h' (Fin.last k))
  let hwB : inRowSpan B (u + d • A (Fin.last k)) := inRowSpan_add huB (inRowSpan_smul d hvB)
  Eq.mpr (congrArg (fun z => inRowSpan B z) (funext hwu)) hwB
-- Reference: MRR 1988, Pt. II Ch. 6 (if every generator of `S` lies in the
-- span of `T` then `span S ⊆ span T`); proved by induction on the number of
-- rows, so no choice of combination witnesses is needed.
/-- If every row of `A` lies in the row span of `B`, then every vector in
the row span of `A` lies in the row span of `B`. -/
theorem inRowSpan_mono {p : ℕ} {B : FreeMatrix K p n} :
    ∀ (q : ℕ) (A : FreeMatrix K q n) (w : FreeMod K n),
    (∀ a : Fin q, inRowSpan B (A a)) → inRowSpan A w → inRowSpan B w :=
  fun q => Nat.rec (motive := fun q => ∀ (A : FreeMatrix K q n) (w : FreeMod K n),
      (∀ a : Fin q, inRowSpan B (A a)) → inRowSpan A w → inRowSpan B w)
    (fun A w _ hw => inRowSpan_mono_zero A w hw)
    (fun k ih A w h hw => inRowSpan_mono_succ k ih A w h hw) q
-- Reference: MRR 1988, Pt. II Ch. 6 (the appended generator is in the span).
/-- The appended vector `v` lies in the row span of `matSnoc A v`. -/
theorem inRowSpan_snoc_self {A : FreeMatrix K m n} {v : FreeMod K n} :
    inRowSpan (matSnoc A v) v :=
  inRowSpan_snoc.mpr ⟨0, inRowSpan_zero _, 1, fun j =>
    (one_mul (v j)).symm.trans (zero_add (1 * v j)).symm⟩
-- Reference: MRR 1988, Pt. II Ch. 6 (span S ⊆ span(S ∪ {v})).
/-- The row span only grows when a row is appended. -/
theorem inRowSpan_snoc_mono {A : FreeMatrix K m n} {v w : FreeMod K n}
    (h : inRowSpan A w) : inRowSpan (matSnoc A v) w :=
  inRowSpan_snoc.mpr ⟨w, h, 0, fun j =>
    ((congrArg (w j + ·) (zero_mul (v j))).trans (add_zero (w j))).symm⟩
-- Reference: MRR 1988, Pt. II Ch. 6 (if `v ∈ span S` then
-- `span(S ∪ {v}) = span S`); the sum reassembly in the forward direction.
/-- The sum step of the forward direction: adding a multiple of the span
witness of `v` to the witness of `u` stays a span witness. -/
theorem inRowSpan_snoc_of_mem_sum {A : FreeMatrix K m n}
    (cu e : Fin m → K) (d : K) (j : Fin n) :
    (∑ a ∈ finFinset m, cu a * A a j) + d * (∑ a ∈ finFinset m, e a * A a j)
      = ∑ a ∈ finFinset m, (cu a + d * e a) * A a j :=
  (congrArg ((∑ a ∈ finFinset m, cu a * A a j) + ·)
    (Finset.mul_sum (finFinset m) (fun a => e a * A a j) d)).trans
    (Finset.sum_add_distrib.symm.trans (sum_finFinset_congr (fun a =>
      (congrArg (cu a * A a j + ·) (mul_assoc d (e a) (A a j)).symm).trans
        (add_mul (cu a) (d * e a) (A a j)).symm)))
-- Reference: MRR 1988, Pt. II Ch. 6 (if `v ∈ span S` then
-- `span(S ∪ {v}) = span S`); forward direction.
/-- Forward direction: membership in the enlarged span implies membership in
the original span. -/
theorem inRowSpan_snoc_of_mem_fwd {A : FreeMatrix K m n} {v w : FreeMod K n}
    (hv : inRowSpan A v) (h : inRowSpan (matSnoc A v) w) : inRowSpan A w :=
  let ⟨u, hu, d, hw⟩ := inRowSpan_snoc.mp h
  let ⟨cu, chu⟩ := hu
  let ⟨e, he⟩ := hv
  ⟨fun a => cu a + d * e a, fun j =>
    (hw j).trans ((congrArg₂ (· + ·) (chu j) (congrArg (d * ·) (he j))).trans
      (inRowSpan_snoc_of_mem_sum cu e d j))⟩
-- Reference: MRR 1988, Pt. II Ch. 6 (if v ∈ span S then span(S ∪ {v}) = span S).
/-- Appending a row that already lies in the span does not change the span. -/
theorem inRowSpan_snoc_of_mem {A : FreeMatrix K m n} {v w : FreeMod K n}
    (hv : inRowSpan A v) : inRowSpan (matSnoc A v) w ↔ inRowSpan A w :=
  ⟨fun h => inRowSpan_snoc_of_mem_fwd hv h, fun h => inRowSpan_snoc_mono h⟩
variable [DecidableEq K]
end BoringMath
