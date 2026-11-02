/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Init
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Fin.Basic
import BoringMath.FormalPeriods.RowReduction.RowOps
import BoringMath.FormalPeriods.RowReduction.PivotSearch
import BoringMath.FormalPeriods.RowReduction.Predicates

/-!
# Peels for the invariant induction (P.2.1, part 5)

Part 5 of `BoringMath.FormalPeriods.RowReduction`: the boolean pivot
test, the pivot-search lemmas specialized to the loop, the
leading-column lemmas, and the zero-column invariant step.
-/

universe u

namespace BoringMath

variable {K : Type u} [Field K] {m n : ℕ}
variable [DecidableEq K]

/-! ## Peels for the invariant induction -/

-- Reference: definitional peel of the `≠ 0` test used in the pivot search.
/-- A nonzero element tests `true`. -/
theorem pivotBool_true {x : K} (h : x ≠ 0) :
    (if x ≠ 0 then true else false) = true :=
  ite_eq_left h

-- Reference: definitional peel of the `≠ 0` test used in the pivot search.
/-- A zero element tests `false`. -/
theorem pivotBool_false {x : K} (h : x = 0) :
    (if x ≠ 0 then true else false) = false :=
  ite_eq_right (fun hne => hne h)

-- Reference: Mines–Richman–Ruitenburg 2008, Pt. II Ch. 6 (reading the test).
/-- If the test is `true`, the element is nonzero. -/
theorem ne_zero_of_pivotBool {x : K} (h : (if x ≠ 0 then true else false) = true) :
    x ≠ 0 := by
  cases (inferInstance : Decidable (x ≠ 0)) with
  | isTrue h' => exact h'
  | isFalse h' =>
      have h2 : (if x ≠ 0 then true else false) = false := ite_eq_right h'
      -- Eq.subst with named rule `h2` at `h`: fully instantiated; the unique
      -- occurrence is the LHS of `h` (motive `fun v => v = true`); gives `false = true`.
      have h3 : false = true := Eq.subst (motive := fun v => v = true) h2 h
      exact absurd h3 Bool.false_ne_true

-- Reference: Mines–Richman–Ruitenburg 2008, Pt. II Ch. 6 (reading the test).
/-- If the test is `false`, the element is zero. -/
theorem eq_zero_of_pivotBool {x : K} (h : (if x ≠ 0 then true else false) = false) :
    x = 0 := by
  cases (inferInstance : Decidable (x ≠ 0)) with
  | isTrue h' =>
      have h2 : (if x ≠ 0 then true else false) = true := ite_eq_left h'
      -- Eq.subst with named rule `h2` at `h`: fully instantiated; the unique
      -- occurrence is the LHS of `h` (motive `fun v => v = false`); gives `true = false`.
      have h3 : true = false := Eq.subst (motive := fun v => v = false) h2 h
      exact absurd h3.symm Bool.false_ne_true
  | isFalse h' =>
      cases (inferInstance : Decidable (x = 0)) with
      | isTrue h0 => exact h0
      | isFalse h2 => exact absurd h2 h'

-- Reference: Mines–Richman–Ruitenburg 2008, Pt. II Ch. 6 (soundness of the
-- pivot search, specialized to the loop's column predicate).
/-- A found pivot row is at or below `r` and has a nonzero entry in column
`j`. -/
theorem rrefAux_pivot_some {A : FreeMatrix K m n} {r j : ℕ} {hj : j < n} {i : Fin m}
    (h : findPivotRow
        (fun i => Nat.ble r i.val && (if A i ⟨j, hj⟩ ≠ 0 then true else false)) m r
        = some i) :
    r ≤ i.val ∧ A i ⟨j, hj⟩ ≠ 0 := by
  have hspec := findPivotRow_some_spec h
  have hboth := Bool.and_eq_true_iff.mp hspec.2.2
  exact ⟨Eq.mp (Nat.ble_eq (x := r) (y := i.val)) hboth.1, ne_zero_of_pivotBool hboth.2⟩

-- Reference: Mines–Richman–Ruitenburg 2008, Pt. II Ch. 6 (completeness of the
-- pivot search, specialized to the loop's column predicate).
/-- If no pivot is found in column `j`, that column is zero at or below
row `r`. -/
theorem rrefAux_pivot_none {A : FreeMatrix K m n} {r j : ℕ} {hj : j < n}
    (h : findPivotRow
        (fun i => Nat.ble r i.val && (if A i ⟨j, hj⟩ ≠ 0 then true else false)) m r = none)
    (a : Fin m) (hle : r ≤ a.val) :
    A a ⟨j, hj⟩ = 0 := by
  have hspec := findPivotRow_none_spec h a hle
    (Nat.lt_of_lt_of_le a.isLt (Nat.le_add_left m r))
  rcases Bool.and_eq_false_iff.mp hspec with hb | ht
  · have hb' : Nat.ble r a.val = true := Eq.mpr (Nat.ble_eq (x := r) (y := a.val)) hle
    -- Eq.subst with named rule `hb` at `hb'`: fully instantiated; the unique
    -- occurrence is the LHS of `hb'` (motive `fun v => v = true`); gives `false = true`.
    have hb'' : false = true := Eq.subst (motive := fun v => v = true) hb hb'
    exact absurd hb'' Bool.false_ne_true
  · exact eq_zero_of_pivotBool ht

-- Reference: Mines–Richman–Ruitenburg 2008, Pt. II Ch. 6 (skipping an
-- all-zero column preserves the invariant).
/-- If column `j` is zero at or below row `r`, advancing to column `j+1`
preserves the loop invariant. -/
theorem rrefState_step_none {r j : ℕ} {A : FreeMatrix K m n} (hj : j < n)
    (hs : RrefState r j A) (hcol : ∀ a : Fin m, r ≤ a.val → A a ⟨j, hj⟩ = 0) :
    RrefState r (j+1) A := by
  rcases hs with ⟨hR1, hR2, hR3, hR4, hR5, hR6⟩
  refine ⟨?_, hR2, ?_, hR4, hR5, hR6⟩
  · intro a ha c hc
    rcases Nat.lt_or_ge c.val j with hc' | hc'
    · exact hR1 a ha c hc'
    · have hval : c.val = j := Nat.le_antisymm (Nat.le_of_lt_succ hc) hc'
      have hceq : c = ⟨j, hj⟩ := Fin.eq_of_val_eq hval
      -- Eq.subst with named rule `hceq`, used symmetrically: fully instantiated;
      -- the unique `c` in the goal is the motive's target instance.
      refine Eq.subst (motive := fun x => A a x = 0) hceq.symm ?_
      exact hcol a ha
  · intro a ha
    exact Nat.lt_of_lt_of_le (hR3 a ha) (Nat.le_succ j)

-- Reference: Mines–Richman–Ruitenburg 2008, Pt. II Ch. 6 (the pivot search
-- returns the first row of the searched range where the predicate holds).
/-- If the predicate holds at `i` and fails at every earlier row of the
searched range, the search returns `i`. -/
theorem findPivotRow_eq_some_of_first {m : ℕ} {p : Fin m → Bool} {t lo : ℕ} {i : Fin m}
    (hle : lo ≤ i.val) (hib : i.val < lo + t) (hp : p i = true)
    (hfirst : ∀ i' : Fin m, lo ≤ i'.val → i'.val < i.val → p i' = false) :
    findPivotRow p t lo = some i := by
  induction t generalizing lo with
  | zero => exact absurd (Nat.lt_of_le_of_lt hle hib) (Nat.lt_irrefl lo)
  | succ t ih =>
      -- Eq.subst with named rule `findPivotRow_succ p t lo` (sym.): fully
      -- instantiated; the unique occurrence is the goal's LHS.
      refine Eq.subst (motive := fun v => v = some i) (findPivotRow_succ p t lo).symm ?_
      rcases Nat.lt_or_ge lo m with hlt | hge
      · -- Eq.subst with named rule `dite_eq_left hlt` (sym.): `lo < m` holds;
        -- the single `dite` occurrence is the goal's LHS.
        refine Eq.subst (motive := fun v => v = some i) (dite_eq_left hlt).symm ?_
        cases (inferInstance : Decidable (p ⟨lo, hlt⟩ = true)) with
        | isTrue hp0 =>
            -- Eq.subst with named rule `ite_eq_left hp0` (sym.): single `ite`
            -- occurrence, the goal's LHS; the hit is at `lo`.
            refine Eq.subst (motive := fun v => v = some i) (ite_eq_left hp0).symm ?_
            rcases Nat.lt_or_ge lo i.val with hlt2 | hge2
            · exfalso
              have hf := hfirst ⟨lo, hlt⟩ (Nat.le_refl lo) hlt2
              -- Eq.subst with named rule `hp0` at `hf`: fully instantiated; the
              -- unique `p ⟨lo, hlt⟩` is the LHS of `hf`; gives `true = false`.
              have hf' : true = false := Eq.subst (motive := fun v => v = false) hp0 hf
              exact absurd hf'.symm Bool.false_ne_true
            · -- `lo = i.val`, hence `⟨lo, hlt⟩ = i`.
              have heq : (⟨lo, hlt⟩ : Fin m) = i :=
                Fin.eq_of_val_eq (Nat.le_antisymm hle hge2)
              -- congrArg with named rule `heq`: the unique `⟨lo, hlt⟩` sits
              -- under `some _` in the goal.
              exact congrArg some heq
        | isFalse hp0 =>
            -- Eq.subst with named rule `ite_eq_right hp0` (sym.): single `ite`
            -- occurrence, the goal's LHS; recurse from `lo+1`.
            refine Eq.subst (motive := fun v => v = some i) (ite_eq_right hp0).symm ?_
            rcases Nat.lt_or_ge lo i.val with hlt2 | hge2
            · refine ih (lo := lo+1) ?_ ?_ ?_
              · exact Nat.succ_le_of_lt hlt2
              · have h2 : lo+(t+1) = (lo+1)+t := Nat.add_right_comm lo t 1
                -- Eq.subst with named rule `h2` at `hib`: fully instantiated;
                -- the unique `lo+(t+1)` is inside `hib`.
                have hib' : i.val < (lo+1)+t :=
                  Eq.subst (motive := fun v => i.val < v) h2 hib
                exact hib'
              · intro i' hle' hlt'
                exact hfirst i' (Nat.le_trans (Nat.le_succ lo) hle') hlt'
            · exfalso
              have heq : (⟨lo, hlt⟩ : Fin m) = i :=
                Fin.eq_of_val_eq (Nat.le_antisymm hle hge2)
              -- Eq.subst with named rule `heq` at `hp0`: the unique `⟨lo, hlt⟩`
              -- is inside `hp0`'s predicate.
              have hp0' : p i = true → False :=
                Eq.subst (motive := fun x => p x = true → False) heq hp0
              exact hp0' hp
      · -- `m ≤ lo`: then `i.val < m ≤ lo ≤ i.val` is absurd.
        -- Eq.subst with named rule `dite_eq_right …` (sym.): single `dite`
        -- occurrence, the goal's LHS.
        refine Eq.subst (motive := fun v => v = some i)
          (dite_eq_right (Nat.not_lt.mpr hge)).symm ?_
        exact absurd (Nat.lt_of_le_of_lt hle (Nat.lt_of_lt_of_le i.isLt hge))
          (Nat.lt_irrefl lo)

-- Reference: Mines–Richman–Ruitenburg 2008, Pt. II Ch. 6 (the search reads
-- only the prefix of the range that it examines).
/-- If `p` and `q` agree on the rows of the searched range below `b`, and the
search for `p` hits `i` below `b` within its fuel, the search for `q` hits
the same `i`. -/
theorem findPivotRow_congr_before {m : ℕ} {p q : Fin m → Bool} {t lo b : ℕ}
    (h : ∀ i' : Fin m, lo ≤ i'.val → i'.val < b → p i' = q i')
    {i : Fin m} (hi : findPivotRow p t lo = some i) (hib : i.val < b)
    (hbt : b ≤ lo + t) :
    findPivotRow q t lo = some i := by
  induction t generalizing lo with
  | zero =>
      -- Eq.subst with named rule `findPivotRow_zero p lo` at `hi`: fully
      -- instantiated; unique occurrence; gives `none = some i`, which is absurd.
      have hi' : none = some i :=
        Eq.subst (motive := fun v => v = some i) (findPivotRow_zero p lo) hi
      cases hi'
  | succ t ih =>
      have hspec := findPivotRow_some_spec hi
      -- Eq.subst with named rule `findPivotRow_succ …` at `hi` and, symmetrically,
      -- in the goal: fully instantiated; one occurrence in each.
      have hi1 := Eq.subst (motive := fun v => v = some i) (findPivotRow_succ p t lo) hi
      refine Eq.subst (motive := fun v => v = some i) (findPivotRow_succ q t lo).symm ?_
      rcases Nat.lt_or_ge lo m with hlt | hge
      · -- Eq.subst with named rule `dite_eq_left hlt` at `hi1` and, symmetrically,
        -- in the goal: `lo < m` holds; single `dite` occurrence in each.
        have hi2 : (if p ⟨lo, hlt⟩ then some ⟨lo, hlt⟩ else findPivotRow p t (lo+1))
            = some i := Eq.subst (motive := fun v => v = some i) (dite_eq_left hlt) hi1
        refine Eq.subst (motive := fun v => v = some i) (dite_eq_left hlt).symm ?_
        have hlob : lo < b := Nat.lt_of_le_of_lt hspec.1 hib
        cases (inferInstance : Decidable (p ⟨lo, hlt⟩ = true)) with
        | isTrue hp0 =>
            -- Eq.subst with named rule `ite_eq_left hp0` at `hi2`: single `ite`
            -- occurrence in `hi2`.
            have hi3 : some ⟨lo, hlt⟩ = some i :=
              Eq.subst (motive := fun v => v = some i) (ite_eq_left hp0) hi2
            injection hi3 with hval
            subst hval
            -- Eq.subst with named rule `h ⟨lo, hlt⟩ …`: the unique `p ⟨lo, hlt⟩`
            -- is the LHS of `hp0`; transports it to `q ⟨lo, hlt⟩`.
            have hq : q ⟨lo, hlt⟩ = true :=
              Eq.subst (motive := fun v => v = true) (h ⟨lo, hlt⟩ (Nat.le_refl lo) hlob) hp0
            -- named rule `ite_eq_left hq` is exactly the (substituted) goal.
            exact ite_eq_left hq
        | isFalse hp0 =>
            -- Eq.subst with named rule `ite_eq_right hp0` at `hi2`: single `ite`
            -- occurrence in `hi2`.
            have hi3 : findPivotRow p t (lo+1) = some i :=
              Eq.subst (motive := fun v => v = some i) (ite_eq_right hp0) hi2
            -- congrArg with named rule `h ⟨lo, hlt⟩ …` (sym.): the unique
            -- `q ⟨lo, hlt⟩` is the goal's `ite` condition.
            have hqp : (if q ⟨lo, hlt⟩ then some ⟨lo, hlt⟩ else findPivotRow q t (lo+1))
                = (if p ⟨lo, hlt⟩ then some ⟨lo, hlt⟩ else findPivotRow q t (lo+1)) :=
              congrArg (fun v => if v then some ⟨lo, hlt⟩ else findPivotRow q t (lo+1))
                (h ⟨lo, hlt⟩ (Nat.le_refl lo) hlob).symm
            refine Eq.subst (motive := fun v => v = some i) hqp.symm ?_
            -- Eq.subst with named rule `ite_eq_right hp0` (sym.): single `ite`
            -- occurrence in the goal.
            refine Eq.subst (motive := fun v => v = some i) (ite_eq_right hp0).symm ?_
            have h2 : lo+(t+1) = (lo+1)+t := Nat.add_right_comm lo t 1
            -- Eq.subst with named rule `h2` at `hbt`: fully instantiated; unique
            -- occurrence.
            have hbt' : b ≤ (lo+1)+t := Eq.subst (motive := fun v => b ≤ v) h2 hbt
            have h' : ∀ i' : Fin m, (lo+1) ≤ i'.val → i'.val < b → p i' = q i' :=
              fun i' hle' hlt' => h i' (Nat.le_trans (Nat.le_succ lo) hle') hlt'
            exact ih h' hi3 hbt'
      · -- `m ≤ lo`: the search for `p` finds nothing, contradicting `hi`.
        -- Eq.subst with named rule `dite_eq_right …` at `hi1`: single occurrence.
        have hi2 : none = some i :=
          Eq.subst (motive := fun v => v = some i)
            (dite_eq_right (Nat.not_lt.mpr hge)) hi1
        cases hi2

-- Reference: definitional peel of `matLeadingCol` at a `some` search result.
/-- If the leading-column search of row `a` finds column `c`, the leading
column is `c.val`. -/
theorem matLeadingCol_eq_some {A : FreeMatrix K m n} {a : Fin m} {c : Fin n}
    (h : findPivotRow (fun c => if A a c ≠ 0 then true else false) n 0 = some c) :
    matLeadingCol A a = c.val := by
  -- unfold matLeadingCol: explicit constant; congrArg with named rule `h`: the
  -- unique `findPivotRow …` scrutinee is abstracted by the match motive, and
  -- `match some c …` reduces to `c.val` definitionally.
  unfold matLeadingCol
  exact congrArg (fun v => match v with | some c' => c'.val | none => n) h

-- Reference: definitional peel of `matLeadingCol` at a `none` search result.
/-- If the leading-column search of row `a` finds nothing, the row is zero
and the leading column is `n`. -/
theorem matLeadingCol_eq_none {A : FreeMatrix K m n} {a : Fin m}
    (h : findPivotRow (fun c => if A a c ≠ 0 then true else false) n 0 = none) :
    matLeadingCol A a = n := by
  -- unfold matLeadingCol: explicit constant; congrArg with named rule `h`: the
  -- unique `findPivotRow …` scrutinee is abstracted by the match motive, and
  -- `match none …` reduces to `n` definitionally.
  unfold matLeadingCol
  exact congrArg (fun v => match v with | some c' => c'.val | none => n) h

-- Reference: Mines–Richman–Ruitenburg 2008, Pt. II Ch. 6 (a leading column
-- inside a prefix is found by the search).
/-- If the leading column of row `a` lies below `j ≤ n`, the leading-column
search returns the corresponding column. -/
theorem matLeadingCol_some_of_lt {A : FreeMatrix K m n} {a : Fin m} {j : ℕ}
    (hj : j ≤ n) (h : matLeadingCol A a < j) :
    ∃ c : Fin n, findPivotRow (fun c => if A a c ≠ 0 then true else false) n 0 = some c ∧
      c.val = matLeadingCol A a := by
  cases hp : findPivotRow (fun c => if A a c ≠ 0 then true else false) n 0 with
  | none =>
      have hn : matLeadingCol A a = n := matLeadingCol_eq_none hp
      -- Eq.subst with named rule `hn` at `h`: fully instantiated; the unique
      -- `matLeadingCol A a` is the LHS of `h`; gives `n < j`.
      have h' : n < j := Eq.subst (motive := fun v => v < j) hn h
      exact absurd h' (Nat.not_lt.mpr hj)
  | some c => exact ⟨c, Eq.refl _, (matLeadingCol_eq_some hp).symm⟩

-- Reference: Mines–Richman–Ruitenburg 2008, Pt. II Ch. 6 (the leading column
-- is determined by the prefix of columns below it).
/-- If `A` and `B` agree on row `a` at every column below `j`, and the leading
column of `A a` is below `j ≤ n`, then `B a` has the same leading column. -/
theorem matLeadingCol_eq_of_agree_before {A B : FreeMatrix K m n} {a : Fin m} {j : ℕ}
    (hj : j ≤ n) (h : ∀ c : Fin n, c.val < j → A a c = B a c)
    (hk : matLeadingCol A a < j) :
    matLeadingCol B a = matLeadingCol A a := by
  obtain ⟨c, hc, hcv⟩ := matLeadingCol_some_of_lt hj hk
  have hcvj : c.val < j := by
    -- Eq.subst with named rule `hcv` (sym.): the unique `c.val` is the goal's LHS.
    exact Eq.subst (motive := fun v => v < j) hcv.symm hk
  have hcong : ∀ i : Fin n, 0 ≤ i.val → i.val < j →
      (if A a i ≠ 0 then true else false) = (if B a i ≠ 0 then true else false) := by
    intro i _ hi
    have heqi := h i hi
    -- congrArg with named rule `heqi`: the unique `A a i` is the LHS `ite`
    -- condition; both sides become syntactically identical.
    exact congrArg (fun v => if v ≠ 0 then true else false) heqi
  have hbt : j ≤ 0 + n := by
    -- Eq.subst with named rule `Nat.zero_add n` (sym.): the unique `0 + n` is
    -- the goal's RHS.
    exact Eq.subst (motive := fun v => j ≤ v) (Nat.zero_add n).symm hj
  have hhit := findPivotRow_congr_before hcong hc hcvj hbt
  -- Eq.subst with named rule `matLeadingCol_eq_some hhit` (sym.): unique
  -- occurrence of `matLeadingCol B a`, the goal's LHS.
  refine Eq.subst (motive := fun v => v = matLeadingCol A a)
    (matLeadingCol_eq_some hhit).symm ?_
  -- named rule `matLeadingCol_eq_some hc`, symmetric, is exactly the goal.
  exact (matLeadingCol_eq_some hc).symm

-- Reference: Mines–Richman–Ruitenburg 2008, Pt. II Ch. 6 (a row vanishing
-- before column `j` and nonzero at `j` has leading column `j`).
/-- If row `a` vanishes at every column below `j < n` and is nonzero at
column `j`, its leading column is `j`. -/
theorem matLeadingCol_eq_of_zero_before {A : FreeMatrix K m n} {a : Fin m} {j : ℕ}
    (hj : j < n) (hzero : ∀ c : Fin n, c.val < j → A a c = 0)
    (hne : A a ⟨j, hj⟩ ≠ 0) :
    matLeadingCol A a = j := by
  have hp : (fun c => if A a c ≠ 0 then true else false) ⟨j, hj⟩ = true :=
    pivotBool_true hne
  have hfirst : ∀ i' : Fin n, 0 ≤ i'.val → i'.val < j →
      (fun c => if A a c ≠ 0 then true else false) i' = false := by
    intro i' _ hi'
    exact pivotBool_false (hzero i' hi')
  have hib : (⟨j, hj⟩ : Fin n).val < 0 + n := by
    -- Eq.subst with named rule `Nat.zero_add n` (sym.): the unique `0 + n` is
    -- the goal's RHS.
    exact Eq.subst (motive := fun v => (⟨j, hj⟩ : Fin n).val < v) (Nat.zero_add n).symm hj
  have hsearch : findPivotRow (fun c => if A a c ≠ 0 then true else false) n 0
      = some ⟨j, hj⟩ :=
    findPivotRow_eq_some_of_first (Nat.zero_le j) hib hp hfirst
  have hs := matLeadingCol_eq_some hsearch
  -- named rule `hs`: the unique `matLeadingCol A a` is the goal's LHS, and the
  -- residual `↑⟨j, hj⟩ = j` is the definitional `Fin.val` projection.
  exact hs

