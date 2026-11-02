/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringMath.CombinatorialGames.Mex
import Mathlib.Order.WellFounded

/-!
# Finite impartial games and Grundy values (Sprague–Grundy, first slice)

CombinatorialGames ticket #332 (CGT.2). A **finite impartial game** is a type
of positions with, for each position, a finite set of options, and a
well-foundedness axiom saying options are always smaller (game trees are
finite). The **Grundy value** of a position is the mex of the Grundy values of
its options; the Sprague–Grundy theorem says the Grundy value completely
determines the outcome under normal play. This module defines the Grundy
recursion and proves: Grundy `0` iff every option has nonzero Grundy
(P-positions), and the Nim computation `grundy (Nim heap n) = n`.

## References
* [Sprague] 1935; [Grundy] 1939 (the mex recursion).
* [Conway] *On Numbers and Games*, ch. 3; [Berlekamp–Conway–Guy] *Winning
  Ways*, vol. 1, ch. 2.
* [Bouton] 1901 (Nim: the Grundy value of a heap of size `n` is `n`).
* Program register: BoringMath #331–#334; consumers BoringLab #276–#279.
-/

namespace BoringMath

variable {α : Type*} [WellFoundedRelation α]

-- Reference: [Conway] ch. 3 (a game = positions + option sets, trees finite).
/-- A **finite impartial game**: positions `α` with a well-founded order, each
position having a finite set of options, all strictly smaller. -/
structure ImpartialGame (α : Type*) [WellFoundedRelation α] where
  /-- The options of a position. -/
  moves : α → Finset α
  /-- Options are strictly smaller (finite game trees). -/
  wf : ∀ p q, q ∈ moves p → WellFoundedRelation.rel q p

-- Reference: [Sprague]/[Grundy] (the mex recursion on the game tree).
/-- The **Grundy value** of a position: the mex of the Grundy values of its
options, by well-founded recursion. -/
def ImpartialGame.grundy (G : ImpartialGame α) (p : α) : ℕ :=
  WellFounded.fix WellFoundedRelation.wf
    (fun p ih => mex ((G.moves p).attach.image (fun q => ih q.1 (G.wf p q.1 q.2)))) p

-- Reference: `WellFounded.fix_eq` (unfolding of the recursion); [Sprague]/[Grundy].
/-- **Fixpoint unfolding** of the Grundy recursion (proved). -/
theorem ImpartialGame.grundy_eq (G : ImpartialGame α) (p : α) :
    G.grundy p = mex ((G.moves p).attach.image (fun q => G.grundy q.1)) :=
  WellFounded.fix_eq WellFoundedRelation.wf _ p

-- Reference: mex_eq_of_not_mem_and_forall + Nat.not_lt_zero.
/-- The mex of a finset is `0` iff `0` is not a member (proved). -/
theorem mex_eq_zero_iff (s : Finset ℕ) : mex s = 0 ↔ 0 ∉ s :=
  ⟨fun h h0 => mex_not_mem s (Eq.subst (motive := fun n => n ∈ s) h.symm h0),
   fun h0 => mex_eq_of_not_mem_and_forall h0 (fun n hn => absurd hn (Nat.not_lt_zero n))⟩

-- Reference: [Sprague]/[Grundy]; P-positions are exactly the Grundy-0 ones.
/-- **P-position criterion**: a position has Grundy value `0` iff every option
has nonzero Grundy value (proved). -/
theorem grundy_eq_zero_iff (G : ImpartialGame α) (p : α) :
    G.grundy p = 0 ↔ ∀ q ∈ G.moves p, G.grundy q ≠ 0 := by
  refine ⟨?_, ?_⟩
  · intro h q hq h0
    exact (mex_eq_zero_iff _).mp ((G.grundy_eq p).symm.trans h)
      (Finset.mem_image.mpr ⟨⟨q, hq⟩, Finset.mem_attach _ _, by exact h0⟩)
  · intro h
    refine (G.grundy_eq p).trans ((mex_eq_zero_iff _).mpr ?_)
    intro h0
    obtain ⟨q, _, hq0⟩ := Finset.mem_image.mp h0
    exact h q.1 q.2 hq0

-- Reference: [Sprague]/[Grundy]; `mem_of_lt_mex` applied to `grundy_eq`.
/-- **Attainment lemma**: every natural strictly below the Grundy value of `p`
is the Grundy value of some option of `p` (proved). -/
theorem ImpartialGame.exists_move_grundy_eq_of_lt (G : ImpartialGame α) (p : α) {m : ℕ}
    (h : m < G.grundy p) : ∃ q ∈ G.moves p, G.grundy q = m := by
  have hlt : m < mex ((G.moves p).attach.image (fun q => G.grundy q.1)) :=
    Eq.subst (motive := fun n => m < n) (G.grundy_eq p) h
  obtain ⟨q, _, hq⟩ := Finset.mem_image.mp (mem_of_lt_mex hlt)
  exact ⟨q.1, q.2, hq⟩
-- Reference: [Conway] ch. 3 (Nim: a heap of size `n` moves to any smaller heap).
/-- **Nim**: the impartial game on `ℕ` where a heap of size `n` moves to any
smaller heap. -/
def nimGame : ImpartialGame ℕ where
  moves n := Finset.range n
  wf _ _ h := Finset.mem_range.mp h

-- Reference: [Bouton] 1901; mex (range n) = n since n ∉ range n and every
-- m < n is in range n.
/-- The mex of `range n` is `n` (proved). -/
theorem mex_range (n : ℕ) : mex (Finset.range n) = n :=
  mex_eq_of_not_mem_and_forall (Finset.notMem_range_self)
    (fun _ hm => Finset.mem_range.mpr hm)

-- Reference: [Bouton] 1901 (the Grundy value of a Nim heap of size `n` is
-- `n`), by strong induction: the options of `n` are exactly `0, …, n-1`.

-- Reference: [Bouton] 1901 (the Grundy value of a Nim heap of size `n` is
-- `n`), by strong induction: the options of `n` are exactly `0, …, n-1`.
/-- **Grundy value of a Nim heap of size `n` is `n`** (proved). -/
theorem grundy_nimGame (n : ℕ) : nimGame.grundy n = n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have himg : ((nimGame.moves n).attach.image (fun q => nimGame.grundy q.1))
        = Finset.range n :=
      (Finset.image_congr (fun q _ => ih q.1 (nimGame.wf n q.1 q.2))).trans
        (Finset.attach_image_val.trans rfl)
    exact (nimGame.grundy_eq n).trans
      (Eq.subst (motive := fun s => mex s = n) himg.symm (mex_range n))

end BoringMath
