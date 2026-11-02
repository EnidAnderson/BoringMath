/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Probability.ProbabilityMassFunction.Basic

/-!
# From ℚ-mass prediction tables to `PMF` — ticket #286

Bridge between the epistemology thread's carrier (`Learning.lean` / #28's
prediction tables `hyp → List (ℚ × outcome)`) and mathlib's `PMF`: a finite
ℚ-table with nonnegative entries summing to `1` is a probability mass function
on the outcome type.

## References
* [Billingsley] P. Billingsley, *Probability and Measure*, Wiley 1995, ch. 1.
* mathlib pin v4.35.0-rc3: `PMF` (`ProbabilityMassFunction/Basic.lean`),
  `hasSum_fintype`.
-/

namespace BoringMath

open ENNReal

-- Reference: mathlib pin v4.35.0-rc3, `Real.toNNReal` and the coercion
-- `NNReal → ℝ≥0∞` via `ENNReal.ofNNReal` (`Basic/ENNReal/Basic.lean`, line 118).
/-- The embedding of a rational mass into `ℝ≥0∞`: a nonnegative rational goes
to its `NNReal`-cast, a negative one to `0` (never reached under `hnn`). -/
def ratToENNReal (q : ℚ) : ℝ≥0∞ := (Real.toNNReal (q : ℝ) : ℝ≥0∞)

-- Reference: local to this file; lets a `ℚ` table sum be read as an `ℝ≥0∞`
-- mass through `ratToENNReal` (not exported to importers).
/-- Local coercion `ℚ → ℝ≥0∞` through `ratToENNReal`. -/
local instance : CoeTC ℚ ℝ≥0∞ := ⟨ratToENNReal⟩

-- Reference: mathlib pin v4.35.0-rc3, `Rat.cast_zero`, `Real.toNNReal_zero`,
-- `ENNReal.coe_zero`.
/-- The zero rational has zero mass. -/
theorem ratToENNReal_zero : ratToENNReal 0 = 0 := by
  change (Real.toNNReal ((0 : ℚ) : ℝ) : ℝ≥0∞) = 0
  have h1 : (Real.toNNReal ((0 : ℚ) : ℝ) : ℝ≥0∞)
      = (Real.toNNReal (0 : ℝ) : ℝ≥0∞) :=
    congrArg (fun x : NNReal => (x : ℝ≥0∞)) (congrArg Real.toNNReal Rat.cast_zero)
  have h2 : (Real.toNNReal (0 : ℝ) : ℝ≥0∞) = ((0 : NNReal) : ℝ≥0∞) :=
    congrArg (fun x : NNReal => (x : ℝ≥0∞)) Real.toNNReal_zero
  exact (h1.trans h2).trans ENNReal.coe_zero

-- Reference: mathlib pin v4.35.0-rc3, `Rat.cast_one`, `Real.toNNReal_one`,
-- `ENNReal.coe_one`.
/-- The unit rational has unit mass. -/
theorem ratToENNReal_one : ratToENNReal 1 = 1 := by
  change (Real.toNNReal ((1 : ℚ) : ℝ) : ℝ≥0∞) = 1
  have h1 : (Real.toNNReal ((1 : ℚ) : ℝ) : ℝ≥0∞)
      = (Real.toNNReal (1 : ℝ) : ℝ≥0∞) :=
    congrArg (fun x : NNReal => (x : ℝ≥0∞)) (congrArg Real.toNNReal Rat.cast_one)
  have h2 : (Real.toNNReal (1 : ℝ) : ℝ≥0∞) = ((1 : NNReal) : ℝ≥0∞) :=
    congrArg (fun x : NNReal => (x : ℝ≥0∞)) Real.toNNReal_one
  exact (h1.trans h2).trans ENNReal.coe_one

-- Reference: mathlib pin v4.35.0-rc3, `Rat.cast_add`, `Rat.cast_nonneg`,
-- `Real.toNNReal_add`, `ENNReal.coe_add`.
/-- Additivity of `ratToENNReal` on nonnegative rationals. -/
theorem ratToENNReal_add (a b : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ratToENNReal (a + b) = ratToENNReal a + ratToENNReal b := by
  have hcast : ((a + b : ℚ) : ℝ) = (a : ℝ) + (b : ℝ) := Rat.cast_add a b
  have ha' : 0 ≤ (a : ℝ) := Rat.cast_nonneg.2 ha
  have hb' : 0 ≤ (b : ℝ) := Rat.cast_nonneg.2 hb
  change (Real.toNNReal (((a + b : ℚ) : ℝ)) : ℝ≥0∞)
      = (Real.toNNReal (a : ℝ) : ℝ≥0∞) + (Real.toNNReal (b : ℝ) : ℝ≥0∞)
  calc (Real.toNNReal (((a + b : ℚ) : ℝ)) : ℝ≥0∞)
      = (Real.toNNReal ((a : ℝ) + (b : ℝ)) : ℝ≥0∞) :=
        congrArg (fun x : NNReal => (x : ℝ≥0∞)) (congrArg Real.toNNReal hcast)
    _ = (Real.toNNReal (a : ℝ) + Real.toNNReal (b : ℝ) : ℝ≥0∞) :=
        congrArg (fun x : NNReal => (x : ℝ≥0∞)) (Real.toNNReal_add ha' hb')
    _ = (Real.toNNReal (a : ℝ) : ℝ≥0∞) + (Real.toNNReal (b : ℝ) : ℝ≥0∞) :=
        ENNReal.coe_add _ _

-- Reference: mathlib pin v4.35.0-rc3, `List.filter_cons`, `List.sum_cons`,
-- `List.mem_map`, `Finset.sum_ite_eq`, `Finset.sum_add_distrib`; fiber
-- decomposition of a list sum over the labels (Billingsley, ch. 1, §1).
/-- Fiber decomposition of a rational mass table: summing the `ratToENNReal`
masses of the per-outcome fibers over the finite outcome type gives the mass of
the total table sum. -/
theorem ratToENNReal_fiber_sum {outcome : Type} [Fintype outcome] [DecidableEq outcome]
    (t : List (ℚ × outcome)) (hnn : ∀ p ∈ t, 0 ≤ p.1) :
    (∑ o : outcome, ratToENNReal (((t.filter (fun p => p.2 = o)).map Prod.fst).sum))
      = ratToENNReal ((t.map Prod.fst).sum) := by
  revert hnn
  induction t with
  | nil =>
    intro _hnn
    change (∑ o : outcome, ratToENNReal (0 : ℚ)) = ratToENNReal (0 : ℚ)
    calc (∑ o : outcome, ratToENNReal (0 : ℚ))
        = ∑ o : outcome, (0 : ℝ≥0∞) := Finset.sum_congr rfl fun o _ => ratToENNReal_zero
      _ = 0 := Finset.sum_const_zero
      _ = ratToENNReal (0 : ℚ) := ratToENNReal_zero.symm
  | cons p t ih =>
    intro hnn
    have hnn_p : 0 ≤ p.1 := hnn p List.mem_cons_self
    have hnn_t : ∀ q ∈ t, 0 ≤ q.1 := fun q hq => hnn q (List.mem_cons_of_mem p hq)
    have hnn_sum : 0 ≤ (t.map Prod.fst).sum :=
      List.sum_nonneg fun q hq => by
        rcases List.mem_map.mp hq with ⟨r, hr, hrq⟩
        exact Eq.subst hrq (hnn_t r hr)
    have hnn_fib : ∀ o : outcome, 0 ≤ ((t.filter (fun p => p.2 = o)).map Prod.fst).sum := by
      intro o
      exact List.sum_nonneg fun q hq => by
        rcases List.mem_map.mp hq with ⟨r, hr, hrq⟩
        exact Eq.subst hrq (hnn_t r (List.mem_filter.mp hr).1)
    have ih' := ih hnn_t
    have hpt : ∀ o : outcome,
        ratToENNReal (((p :: t).filter (fun p => p.2 = o)).map Prod.fst).sum
          = ratToENNReal (((t.filter (fun p => p.2 = o)).map Prod.fst).sum)
            + (if p.2 = o then ratToENNReal p.1 else 0) := by
      intro o
      rcases Classical.em (p.2 = o) with h | h
      · have hfil : (p :: t).filter (fun p => p.2 = o)
            = p :: t.filter (fun p => p.2 = o) :=
          List.filter_cons.trans (ite_eq_left (decide_eq_true_iff.2 h))
        have hs : (((p :: t).filter (fun p => p.2 = o)).map Prod.fst).sum
            = p.1 + ((t.filter (fun p => p.2 = o)).map Prod.fst).sum :=
          (congrArg (fun l => (l.map Prod.fst).sum) hfil).trans
            ((congrArg List.sum List.map_cons).trans List.sum_cons)
        calc ratToENNReal (((p :: t).filter (fun p => p.2 = o)).map Prod.fst).sum
            = ratToENNReal (p.1 + ((t.filter (fun p => p.2 = o)).map Prod.fst).sum) :=
              congrArg ratToENNReal hs
          _ = ratToENNReal p.1
                + ratToENNReal (((t.filter (fun p => p.2 = o)).map Prod.fst).sum) :=
              ratToENNReal_add p.1 _ hnn_p (hnn_fib o)
          _ = ratToENNReal (((t.filter (fun p => p.2 = o)).map Prod.fst).sum)
                + ratToENNReal p.1 := add_comm _ _
          _ = ratToENNReal (((t.filter (fun p => p.2 = o)).map Prod.fst).sum)
                + (if p.2 = o then ratToENNReal p.1 else 0) :=
              (congrArg _ (ite_eq_left h)).symm
      · have hfil : (p :: t).filter (fun p => p.2 = o) = t.filter (fun p => p.2 = o) :=
          List.filter_cons.trans (ite_eq_right (fun hc => h (decide_eq_true_iff.1 hc)))
        have hs : (((p :: t).filter (fun p => p.2 = o)).map Prod.fst).sum
            = ((t.filter (fun p => p.2 = o)).map Prod.fst).sum :=
          congrArg (fun l => (l.map Prod.fst).sum) hfil
        calc ratToENNReal (((p :: t).filter (fun p => p.2 = o)).map Prod.fst).sum
            = ratToENNReal (((t.filter (fun p => p.2 = o)).map Prod.fst).sum) :=
              congrArg ratToENNReal hs
          _ = ratToENNReal (((t.filter (fun p => p.2 = o)).map Prod.fst).sum) + 0 :=
              (add_zero _).symm
          _ = ratToENNReal (((t.filter (fun p => p.2 = o)).map Prod.fst).sum)
                + (if p.2 = o then ratToENNReal p.1 else 0) :=
              (congrArg _ (ite_eq_right h)).symm
    calc (∑ o : outcome, ratToENNReal (((p :: t).filter (fun p => p.2 = o)).map Prod.fst).sum)
        = ∑ o : outcome, (ratToENNReal (((t.filter (fun p => p.2 = o)).map Prod.fst).sum)
            + (if p.2 = o then ratToENNReal p.1 else 0)) :=
          Finset.sum_congr rfl (fun o _ => hpt o)
      _ = (∑ o : outcome, ratToENNReal (((t.filter (fun p => p.2 = o)).map Prod.fst).sum))
          + (∑ o : outcome, (if p.2 = o then ratToENNReal p.1 else 0)) := Finset.sum_add_distrib
      _ = ratToENNReal ((t.map Prod.fst).sum) + ratToENNReal p.1 := by
          exact (congrArg (fun x => x + ∑ o : outcome, (if p.2 = o then ratToENNReal p.1 else 0))
            ih').trans
            (congrArg (fun x => ratToENNReal ((t.map Prod.fst).sum) + x)
              ((Finset.sum_ite_eq Finset.univ p.2 (fun _ => ratToENNReal p.1)).trans
                (ite_eq_left (Finset.mem_univ p.2))))
      _ = ratToENNReal (p.1 + (t.map Prod.fst).sum) :=
          (add_comm _ _).trans
            (ratToENNReal_add p.1 ((t.map Prod.fst).sum) hnn_p hnn_sum).symm
      _ = ratToENNReal (((p :: t).map Prod.fst).sum) :=
          congrArg ratToENNReal (((congrArg List.sum List.map_cons).trans List.sum_cons).symm)

-- Reference: mathlib pin v4.35.0-rc3, `HasSum` (`InfiniteSum/Defs.lean`); the
-- cast is the `eq ▸ h.hasProd` pattern of `Multipliable.hasProd_iff`, with the
-- motive spelled out to keep elaboration cheap on large table terms.
/-- A summable family with limit `A` also has limit `1` when `A = 1`. -/
theorem hasSum_congr_limit {β : Type} (F : β → ℝ≥0∞) (A : ℝ≥0∞)
    (h1 : HasSum F A) (h2 : A = 1) : HasSum F 1 :=
  Eq.mp (congrArg (fun x => HasSum F x) h2) h1

-- Reference: mathlib pin v4.35.0-rc3, `PMF` is `{f : α → ℝ≥0∞ // HasSum f 1}`;
-- `hasSum_fintype`; `Finset.sum_filter` / fiber sums.
/-- A **finite ℚ-mass table** (nonnegative entries summing to `1`) on a finite
outcome type is a `PMF`: the mass at `o` is the sum of the entries labelled `o`. -/
def PMF.ofRatTable {outcome : Type} [Fintype outcome] [DecidableEq outcome]
    (t : List (ℚ × outcome)) (hnn : ∀ p ∈ t, 0 ≤ p.1) (hsum : (t.map Prod.fst).sum = 1) :
    PMF outcome where
  val o := ((t.filter (fun p => p.2 = o)).map Prod.fst).sum
  property := by
    have h1 : HasSum (fun o => ratToENNReal (((t.filter (fun p => p.2 = o)).map Prod.fst).sum))
        (∑ o : outcome, ratToENNReal (((t.filter (fun p => p.2 = o)).map Prod.fst).sum)) :=
      hasSum_fintype _
    have h2 : (∑ o : outcome, ratToENNReal (((t.filter (fun p => p.2 = o)).map Prod.fst).sum))
        = 1 := (ratToENNReal_fiber_sum t hnn).trans
          ((congrArg ratToENNReal hsum).trans ratToENNReal_one)
    exact hasSum_congr_limit _ _ h1 h2

-- Reference: the definition, applied pointwise.
/-- The pointwise mass of `PMF.ofRatTable` at `o`. -/
theorem PMF.ofRatTable_apply {outcome : Type} [Fintype outcome] [DecidableEq outcome]
    (t : List (ℚ × outcome)) (hnn : ∀ p ∈ t, 0 ≤ p.1) (hsum : (t.map Prod.fst).sum = 1)
    (o : outcome) :
    PMF.ofRatTable t hnn hsum o
      = ((t.filter (fun p => p.2 = o)).map Prod.fst).sum := rfl

end BoringMath
