/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringMath.CombinatorialGames.Sum
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Fold
import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Embedding.Basic

/-!
# Multi-heap Nim and Bouton's theorem

CombinatorialGames ticket #465 (GitHub #374). **Nim with `k` heaps** is the
impartial game on heap vectors `f : Fin k → ℕ` in which a move changes exactly
one coordinate to a strictly smaller value.  By induction on `k`, identifying
`Fin (k+1) → ℕ` with `ℕ × (Fin k → ℕ)` via `finConsEquiv`, the game is the
disjoint sum of a single Nim heap with the `k`-heap game; the Sprague-Grundy
xor theorem (`ImpartialGame.grundy_sum`, proved in `Sum.lean` (ticket #463))
then gives that the Grundy value of a position is the nim-sum (xor-fold) of
the heap sizes, and the Sprague-Grundy outcome theorem gives **Bouton's
theorem**: a position is a P-position iff the xor of its heap sizes is `0`.

## References
* [Bouton] C. L. Bouton, "Nim, a game played with a pile of objects",
  Ann. of Math. (2) 2 (1901), 35-39.
* [BCG] E. R. Berlekamp, J. H. Conway, R. K. Guy, *Winning Ways for Your
  Mathematical Plays*, vol. 1, ch. 2 (Nim and the xor of heap sizes).
* mathlib pin v4.35.0-rc3: `measure` (core `Init/WF`), `Fin.consEquiv`,
  `Fin.univ_succAbove`, `Fin.zero_succAbove`, `Finset.fold`,
  `Std.Commutative`/`Std.Associative`, `Equiv.toEmbedding`.
* Program register: BoringMath #463 (grundy_sum, used), #465 (this file).
-/

namespace BoringMath

-- The moves of `ImpartialGame.sum` (`Sum.lean`, under `open scoped Classical`)
-- carry the classical `DecidableEq (ℕ × (Fin k → ℕ))` instance; provide it
-- locally at high priority so instance synthesis here agrees with it.
open Classical in
noncomputable local instance (priority := 2000) instDecidableEqProdNatFinFun (k : ℕ) :
    DecidableEq (ℕ × (Fin k → ℕ)) :=
  @instDecidableEqProd ℕ (Fin k → ℕ) (Classical.decEq ℕ) (Classical.decEq (Fin k → ℕ))

/-! ## The ambient well-founded order on heap vectors -/

-- Reference: mathlib pin v4.35.0-rc3, `measure` (core `Init/WF`, the `invImage`
-- construction); [Conway] ch. 3 (finite game trees).
/-- The well-founded relation on heap vectors `Fin k → ℕ` given by the total
heap size: `f` precedes `g` when `∑ i, f i < ∑ i, g i` (proved). -/
instance instWellFoundedRelationFinFun (k : ℕ) : WellFoundedRelation (Fin k → ℕ) :=
  measure (fun f => ∑ i, f i)

/-! ## The cons equivalence `Fin (k+1) → ℕ ≃ ℕ × (Fin k → ℕ)` -/

-- Reference: [BCG] vol. 1, ch. 2 (splitting a tuple into head and tail);
-- mathlib pin v4.35.0-rc3, `Fin.consEquiv`.
/-- The equivalence identifying a heap vector of length `k+1` with its first
heap and the vector of the remaining `k` heaps (proved). -/
def finConsEquiv (k : ℕ) : (Fin (k + 1) → ℕ) ≃ ℕ × (Fin k → ℕ) :=
  (Fin.consEquiv (fun _ : Fin (k + 1) => ℕ)).symm

-- Reference: mathlib pin v4.35.0-rc3, `Fin.consEquiv_symm_apply`.
/-- The first component of `finConsEquiv k f` is the heap `f 0` (proved). -/
theorem finConsEquiv_fst {k : ℕ} (f : Fin (k + 1) → ℕ) : (finConsEquiv k f).1 = f 0 :=
  congrArg Prod.fst (Fin.consEquiv_symm_apply (fun _ : Fin (k + 1) => ℕ) f)

-- Reference: mathlib pin v4.35.0-rc3, `Fin.consEquiv_symm_apply`.
/-- The second component of `finConsEquiv k f` is the tail `Fin.tail f`
(proved). -/
theorem finConsEquiv_snd {k : ℕ} (f : Fin (k + 1) → ℕ) :
    (finConsEquiv k f).2 = Fin.tail f :=
  congrArg Prod.snd (Fin.consEquiv_symm_apply (fun _ : Fin (k + 1) => ℕ) f)

-- Reference: mathlib pin v4.35.0-rc3, `Fin.consEquiv_apply` (pointwise) and
-- `funext`, the named extensionality axiom.
/-- The inverse of `finConsEquiv k` rebuilds a heap vector by `Fin.cons`
(proved). -/
theorem finConsEquiv_symm_apply {k : ℕ} (p : ℕ × (Fin k → ℕ)) :
    (finConsEquiv k).symm p = Fin.cons p.1 p.2 := by
  change (Fin.consEquiv (fun _ : Fin (k + 1) => ℕ)) p = Fin.cons p.1 p.2
  exact funext (Fin.consEquiv_apply (fun _ : Fin (k + 1) => ℕ) p)

/-! ## The xor-fold of the heap sizes -/

-- Reference: mathlib pin v4.35.0-rc3, `Std.Commutative` (core `Init/Core`);
-- commutativity of the nim-sum from `nimSum_comm`.
/-- The nim-sum is a commutative operation, as `Finset.fold` requires
(proved). -/
instance instStdCommutativeNimSum : Std.Commutative nimSum :=
  ⟨fun a b => nimSum_comm a b⟩

-- Reference: mathlib pin v4.35.0-rc3, `Std.Associative` (core `Init/Core`);
-- associativity of the nim-sum from `nimSum_assoc`.
/-- The nim-sum is an associative operation, as `Finset.fold` requires
(proved). -/
instance instStdAssociativeNimSum : Std.Associative nimSum :=
  ⟨fun a b c => nimSum_assoc a b c⟩

-- Reference: [Bouton] 1901; [BCG] vol. 1, ch. 2 (the xor of the heap sizes).
/-- The **xor-fold** (nim-sum) of the heap sizes `f i` over all coordinates
`i : Fin k`: `nimXor k f = (Finset.univ).fold nimSum 0 f`. -/
def nimXor (k : ℕ) (f : Fin k → ℕ) : ℕ := (Finset.univ : Finset (Fin k)).fold nimSum 0 f

-- Reference: mathlib pin v4.35.0-rc3, `Finset.univ_eq_empty`, `Finset.fold_empty`.
/-- The xor-fold over `Fin 0` is `0` (proved). -/
theorem nimXor_zero (f : Fin 0 → ℕ) : nimXor 0 f = 0 :=
  Eq.subst (motive := fun s : Finset (Fin 0) => Finset.fold nimSum 0 f s = 0)
    (Finset.univ_eq_empty (α := Fin 0)).symm Finset.fold_empty

-- Reference: primitive definitional lemma (STYLE §5); mathlib pin v4.35.0-rc3,
-- `Fin.tail` unfolds to evaluation at `i.succ`.
/-- `Fin.tail f` evaluated at `i` is `f i.succ` (proved by `rfl`). -/
theorem fin_tail_apply {k : ℕ} (f : Fin (k + 1) → ℕ) (i : Fin k) :
    Fin.tail f i = f i.succ := rfl

-- Reference: mathlib pin v4.35.0-rc3, `Fin.zero_succAbove` (`0.succAbove i =
-- i.succ`, by `rfl`); `funext` is the named extensionality axiom.
/-- Composing with the embedding `Fin.succAboveEmb 0` is the tail (proved). -/
theorem comp_succAboveEmb_zero {k : ℕ} (f : Fin (k + 1) → ℕ) :
    f ∘ Fin.succAboveEmb 0 = Fin.tail f :=
  funext fun i =>
    Eq.subst (motive := fun x : Fin (k + 1) => f x = Fin.tail f i)
      (Fin.zero_succAbove i).symm (fin_tail_apply f i).symm

-- Reference: mathlib pin v4.35.0-rc3, `Fin.univ_succAbove`, `Finset.fold_cons`,
-- `Finset.fold_map`, `Finset.fold_congr`; [BCG] vol. 1, ch. 2.
/-- The xor-fold over `Fin (k+1)` peels off the first heap (proved). -/
theorem nimXor_succ {k : ℕ} (f : Fin (k + 1) → ℕ) :
    nimXor (k + 1) f = nimSum (f 0) (nimXor k (Fin.tail f)) := by
  have hmain : (Finset.univ : Finset (Fin (k + 1))).fold nimSum 0 f
      = nimSum (f 0) (nimXor k (Fin.tail f)) :=
    Eq.subst (motive := fun s : Finset (Fin (k + 1)) =>
        Finset.fold nimSum 0 f s = nimSum (f 0) (nimXor k (Fin.tail f)))
      (Fin.univ_succAbove k 0).symm
      ((Finset.fold_cons _).trans (congrArg (nimSum (f 0)) (Finset.fold_map.trans
        (Finset.fold_congr (fun i _ => congrFun (comp_succAboveEmb_zero f) i)))))
  exact hmain

-- Reference: [Bouton] 1901; `nimSum_eq_zero_iff` (xor is `0` iff the two
-- summands agree) applied to `nimXor_succ`.
/-- The xor-fold over `Fin (k+1)` is `0` iff the first heap equals the xor-fold
of the tail, the "balance the heaps" reading of Bouton's criterion (proved). -/
theorem nimXor_succ_eq_zero_iff {k : ℕ} (f : Fin (k + 1) → ℕ) :
    nimXor (k + 1) f = 0 ↔ f 0 = nimXor k (Fin.tail f) :=
  (Iff.of_eq (congrArg (fun n => n = 0) (nimXor_succ f))).trans
    (nimSum_eq_zero_iff (f 0) (nimXor k (Fin.tail f)))

/-! ## Sums of heap vectors -/

-- Reference: mathlib pin v4.35.0-rc3, `Fin.sum_univ_succ` (with `Fin.tail`
-- definitionally `fun i => f i.succ`).
/-- The total heap size of `f : Fin (k+1) → ℕ` is `f 0` plus the total of the
tail (proved). -/
theorem sum_univ_succ_tail {k : ℕ} (f : Fin (k + 1) → ℕ) :
    ∑ i : Fin (k + 1), f i = f 0 + ∑ i : Fin k, Fin.tail f i :=
  Fin.sum_univ_succ f

-- Reference: `finConsEquiv_fst`, `finConsEquiv_snd`, `Equiv.symm_apply_apply`
-- and `Fin.sum_univ_succ`; mathlib pin v4.35.0-rc3.
/-- The total heap size of `(finConsEquiv k).symm p` is `p.1 + ∑ p.2`
(proved). -/
theorem sum_finConsEquiv_symm {k : ℕ} (p : ℕ × (Fin k → ℕ)) :
    ∑ i : Fin (k + 1), (finConsEquiv k).symm p i = p.1 + ∑ i : Fin k, p.2 i := by
  have h := Fin.sum_univ_succ ((finConsEquiv k).symm p)
  have h0 : ((finConsEquiv k).symm p) 0 = p.1 :=
    (finConsEquiv_fst ((finConsEquiv k).symm p)).symm.trans
      (congrArg Prod.fst (Equiv.apply_symm_apply (finConsEquiv k) p))
  have ht : Fin.tail ((finConsEquiv k).symm p) = p.2 :=
    (finConsEquiv_snd ((finConsEquiv k).symm p)).symm.trans
      (congrArg Prod.snd (Equiv.apply_symm_apply (finConsEquiv k) p))
  have hs : (∑ i : Fin k, ((finConsEquiv k).symm p) i.succ) = ∑ i : Fin k, p.2 i :=
    congrArg (Finset.sum Finset.univ) ht
  exact Eq.subst
    (motive := fun v =>
        ∑ i : Fin (k + 1), (finConsEquiv k).symm p i = v + ∑ i : Fin k, p.2 i)
    h0 (Eq.subst
      (motive := fun w => ∑ i : Fin (k + 1), (finConsEquiv k).symm p i =
        ((finConsEquiv k).symm p) 0 + w) hs h)

/-! ## Pulling a game back along an equivalence of positions -/

-- Reference: [BCG] vol. 1, ch. 2 (renaming the positions of a game);
-- mathlib pin v4.35.0-rc3, `Finset.mem_map`, `Equiv.toEmbedding`.
/-- The **pullback** of an impartial game along an equivalence `e : β ≃ α` of
position types: a position `b : β` has the moves that `e b` has in `G`,
transported back along `e.symm` (proved). -/
def ImpartialGame.comap {β : Type*} [WellFoundedRelation β] {α : Type*}
    [WellFoundedRelation α] (e : β ≃ α) (G : ImpartialGame α)
    (hwf : ∀ b a, a ∈ G.moves (e b) → WellFoundedRelation.rel (e.symm a) b) :
    ImpartialGame β where
  moves b := (G.moves (e b)).map e.symm.toEmbedding
  wf b c hc := by
    obtain ⟨a, ha, hca⟩ := Finset.mem_map.mp hc
    exact Eq.subst (motive := fun x => WellFoundedRelation.rel x b) hca (hwf b a ha)

-- Reference: [Sprague] 1935 / [Grundy] 1939; the Grundy recursion unfolds via
-- `ImpartialGame.grundy_eq` and the option sets correspond under `e`.
/-- The Grundy value is invariant under renaming positions along an
equivalence (proved by well-founded induction on `β`). -/
theorem ImpartialGame.grundy_comap {β : Type*} [WellFoundedRelation β] {α : Type*}
    [WellFoundedRelation α] (e : β ≃ α) (G : ImpartialGame α)
    (hwf : ∀ b a, a ∈ G.moves (e b) → WellFoundedRelation.rel (e.symm a) b) (b : β) :
    (G.comap e hwf).grundy b = G.grundy (e b) :=
  WellFounded.induction WellFoundedRelation.wf
    (C := fun b => (G.comap e hwf).grundy b = G.grundy (e b)) b
    (fun b ih =>
      have h1 : (G.comap e hwf).grundy b
          = mex (((G.comap e hwf).moves b).attach.image
              fun q => (G.comap e hwf).grundy q.1) :=
        (G.comap e hwf).grundy_eq b
      have himg : (((G.comap e hwf).moves b).attach.image
              fun q => (G.comap e hwf).grundy q.1)
          = (G.moves (e b)).attach.image fun q => G.grundy q.1 := by
        apply Finset.ext
        intro x
        refine ⟨?_, ?_⟩
        · intro hx
          obtain ⟨q, hq, hxq⟩ := Finset.mem_image.mp hx
          obtain ⟨a, ha, hqa⟩ := Finset.mem_map.mp q.2
          have e1 : (G.comap e hwf).grundy (e.symm a) = G.grundy a :=
            Eq.subst (motive := fun x => (G.comap e hwf).grundy (e.symm a) = G.grundy x)
              (Equiv.apply_symm_apply e a) (ih (e.symm a) (hwf b a ha))
          have e2 : (G.comap e hwf).grundy q.1 = G.grundy a :=
            Eq.subst (motive := fun y => (G.comap e hwf).grundy y = G.grundy a) hqa e1
          refine Eq.subst hxq (Finset.mem_image.mpr
            ⟨⟨a, ha⟩, Finset.mem_attach _ _, e2.symm⟩)
        · intro hx
          obtain ⟨q, hq, hxq⟩ := Finset.mem_image.mp hx
          have e1 : (G.comap e hwf).grundy (e.symm q.1) = G.grundy q.1 :=
            Eq.subst (motive := fun x =>
                (G.comap e hwf).grundy (e.symm q.1) = G.grundy x)
              (Equiv.apply_symm_apply e q.1) (ih (e.symm q.1) (hwf b q.1 q.2))
          refine Eq.subst hxq (Finset.mem_image.mpr ⟨⟨e.symm q.1,
            Finset.mem_map.mpr ⟨q.1, q.2, rfl⟩⟩, Finset.mem_attach _ _, e1⟩)
      have hfin : mex (((G.comap e hwf).moves b).attach.image
          fun q => (G.comap e hwf).grundy q.1) = G.grundy (e b) :=
        Eq.subst (motive := fun s => mex s = G.grundy (e b)) himg.symm
          (G.grundy_eq (e b)).symm
      h1.trans hfin)

/-! ## Multi-heap Nim -/

-- Reference: [BCG] vol. 1, ch. 2 (a move in a sum changes one component);
-- mathlib pin v4.35.0-rc3, `Finset.mem_union`, `Finset.mem_image`,
-- `Finset.mem_range`, `Nat.add_lt_add_left`, `Nat.add_lt_add_right`.
/-- Well-foundedness of the pulled-back sum: a move of `nimGame.sum H` at
`finConsEquiv k f`, transported back, strictly decreases the total heap size
(proved). -/
theorem comap_sum_wf {k : ℕ} (H : ImpartialGame (Fin k → ℕ)) (f : Fin (k + 1) → ℕ)
    (a : ℕ × (Fin k → ℕ)) (ha : a ∈ (nimGame.sum H).moves (finConsEquiv k f)) :
    WellFoundedRelation.rel ((finConsEquiv k).symm a) f := by
  change ∑ i : Fin (k + 1), (finConsEquiv k).symm a i < ∑ i : Fin (k + 1), f i
  have h2 : ∑ i : Fin (k + 1), f i
      = (finConsEquiv k f).1 + ∑ i : Fin k, (finConsEquiv k f).2 i :=
    Eq.subst (motive := fun g : Fin (k + 1) → ℕ =>
        ∑ i, g i = (finConsEquiv k f).1 + ∑ i : Fin k, (finConsEquiv k f).2 i)
      (Equiv.symm_apply_apply (finConsEquiv k) f) (sum_finConsEquiv_symm (finConsEquiv k f))
  rcases Finset.mem_union.mp ha with h | h
  · obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp h
    have hlt : a' < (finConsEquiv k f).1 := Finset.mem_range.mp ha'
    calc ∑ i : Fin (k + 1), (finConsEquiv k).symm (a', (finConsEquiv k f).2) i
        = a' + ∑ i : Fin k, (finConsEquiv k f).2 i := sum_finConsEquiv_symm _
      _ < (finConsEquiv k f).1 + ∑ i : Fin k, (finConsEquiv k f).2 i :=
          Nat.add_lt_add_right hlt _
      _ = ∑ i : Fin (k + 1), f i := h2.symm
  · obtain ⟨b', hb', rfl⟩ := Finset.mem_image.mp h
    have hlt : ∑ i : Fin k, b' i < ∑ i : Fin k, (finConsEquiv k f).2 i :=
      H.wf (finConsEquiv k f).2 b' hb'
    calc ∑ i : Fin (k + 1), (finConsEquiv k).symm ((finConsEquiv k f).1, b') i
        = (finConsEquiv k f).1 + ∑ i : Fin k, b' i := sum_finConsEquiv_symm _
      _ < (finConsEquiv k f).1 + ∑ i : Fin k, (finConsEquiv k f).2 i :=
          Nat.add_lt_add_left hlt _
      _ = ∑ i : Fin (k + 1), f i := h2.symm

-- Reference: [Bouton] 1901; [BCG] vol. 1, ch. 2 (Nim with `k` heaps: a move
-- changes exactly one heap to a strictly smaller size).
/-- **Multi-heap Nim**: the impartial game on heap vectors `Fin k → ℕ` in
which a move changes exactly one coordinate to a strictly smaller value.
Defined by induction on `k`: `nimHeaps 0` is the trivial game (no moves), and
`nimHeaps (k+1)` is `nimGame` summed with `nimHeaps k`, pulled back along
`finConsEquiv k`. -/
-- noncomputable: depends on `ImpartialGame.sum`, whose moves use the classical
-- `DecidableEq` instance (`open scoped Classical` in `Sum.lean`).
noncomputable def nimHeaps : (k : ℕ) → ImpartialGame (Fin k → ℕ)
  | 0 => { moves := fun _ => ∅, wf := fun _ q h => absurd h (Finset.notMem_empty q) }
  | k + 1 =>
    ImpartialGame.comap (finConsEquiv k) (nimGame.sum (nimHeaps k))
      (comap_sum_wf (nimHeaps k))

-- Reference: [Sprague] 1935 / [Grundy] 1939 xor theorem (`grundy_sum`,
-- proved in `Sum.lean` (ticket #463)) plus `grundy_nimGame`;
-- [Bouton] 1901; [BCG] vol. 1, ch. 2.
/-- **Grundy value of multi-heap Nim**: the Grundy value of the heap vector
`f : Fin k → ℕ` is the xor-fold of the heap sizes over `Finset.univ`
(proved by induction on `k`, via `grundy_comap`, `grundy_sum`,
`grundy_nimGame` and `nimXor_succ`). -/
theorem nimHeaps_grundy (k : ℕ) (f : Fin k → ℕ) :
    (nimHeaps k).grundy f = (Finset.univ : Finset (Fin k)).fold nimSum 0 f := by
  induction k with
  | zero =>
    have h1 : (nimHeaps 0).grundy f
        = mex (((nimHeaps 0).moves f).attach.image fun q => (nimHeaps 0).grundy q.1) :=
      (nimHeaps 0).grundy_eq f
    have h2 : ((nimHeaps 0).moves f).attach.image
        (fun q => (nimHeaps 0).grundy q.1) = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro x hx
      obtain ⟨q, _, _⟩ := Finset.mem_image.mp hx
      exact Finset.notMem_empty q.1 q.2
    have h3 : (nimHeaps 0).grundy f = 0 :=
      (Eq.subst (motive := fun s : Finset ℕ => (nimHeaps 0).grundy f = mex s) h2 h1).trans
        ((mex_eq_zero_iff _).mpr (Finset.notMem_empty 0))
    exact h3.trans (nimXor_zero f).symm
  | succ k ih =>
    have h1 : (nimHeaps (k + 1)).grundy f
        = (nimGame.sum (nimHeaps k)).grundy (finConsEquiv k f) :=
      ImpartialGame.grundy_comap (finConsEquiv k) (nimGame.sum (nimHeaps k))
        (comap_sum_wf (nimHeaps k)) f
    have h2 : (nimGame.sum (nimHeaps k)).grundy (finConsEquiv k f)
        = nimSum (nimGame.grundy (finConsEquiv k f).1)
            ((nimHeaps k).grundy (finConsEquiv k f).2) :=
      ImpartialGame.grundy_sum nimGame (nimHeaps k) (finConsEquiv k f).1
        (finConsEquiv k f).2
    have h3 : nimGame.grundy (finConsEquiv k f).1 = f 0 :=
      (grundy_nimGame _).trans (finConsEquiv_fst f)
    have h4 : (nimHeaps k).grundy (finConsEquiv k f).2 = nimXor k (Fin.tail f) :=
      (ih _).trans (congrArg (nimXor k) (finConsEquiv_snd f))
    calc (nimHeaps (k + 1)).grundy f
        = (nimGame.sum (nimHeaps k)).grundy (finConsEquiv k f) := h1
      _ = nimSum (nimGame.grundy (finConsEquiv k f).1)
            ((nimHeaps k).grundy (finConsEquiv k f).2) := h2
      _ = nimSum (f 0) (nimXor k (Fin.tail f)) := congrArg₂ nimSum h3 h4
      _ = (Finset.univ : Finset (Fin (k + 1))).fold nimSum 0 f := (nimXor_succ f).symm

-- Reference: [Bouton] 1901 (P-position iff the xor of the heap sizes is `0`);
-- [Sprague] 1935 / [Grundy] 1939 outcome theorem
-- (`outcome_eq_p_iff_grundy_eq_zero`) applied to `nimHeaps_grundy`; the
-- two-heap special case is `nimSum_eq_zero_iff` (xor `0` iff equal heaps).
/-- **Bouton's theorem**: a multi-heap Nim position `f : Fin k → ℕ` is a
P-position (previous player wins) iff the xor-fold of its heap sizes over
`Finset.univ` is `0` (proved). -/
theorem nimHeaps_outcome_eq_p_iff (k : ℕ) (f : Fin k → ℕ) :
    (nimHeaps k).outcome f = Outcome.p
      ↔ (Finset.univ : Finset (Fin k)).fold nimSum 0 f = 0 :=
  ((nimHeaps k).outcome_eq_p_iff_grundy_eq_zero f).trans
    (Iff.of_eq (congrArg (fun n => n = 0) (nimHeaps_grundy k f)))

end BoringMath
