/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringMath.CombinatorialGames.Impartial

/-!
# Outcome classes of finite impartial games under normal play

CombinatorialGames ticket #332 (CGT.2, outcome half). Under **normal play**
(the player unable to move loses), every position of a finite impartial game
is either an **N-position** (next player wins: some option is a P-position)
or a **P-position** (previous player wins: every option is an N-position).
This module defines the outcome by well-founded recursion and proves the
Sprague–Grundy outcome theorem: `P` iff Grundy value `0`.

## References
* [Sprague] 1935; [Grundy] 1939; [Conway] ch. 3; [Berlekamp–Conway–Guy]
  vol. 1, ch. 2.
* Program register: BoringMath #331–#334; consumers BoringLab #276–#279
  (face-down card = hidden P/N choice).
-/

namespace BoringMath

open scoped Classical

variable {α : Type*} [WellFoundedRelation α]

-- Reference: [Conway] ch. 3 (the two outcome classes of normal play).
/-- The **outcome class** of a position under normal play. -/
inductive Outcome
  /-- **N**: the next player wins. -/
  | n
  /-- **P**: the previous player wins. -/
  | p
  deriving DecidableEq

-- Reference: [Sprague]/[Grundy] (outcome recursion on the game tree).
/-- The **outcome** of a position under normal play, by well-founded recursion:
N if some option is P, else P. -/
noncomputable def ImpartialGame.outcome (G : ImpartialGame α) (p : α) : Outcome :=
  WellFounded.fix WellFoundedRelation.wf
    (fun p ih =>
      if _ : ∃ q : {x // x ∈ G.moves p}, ih q.1 (G.wf p q.1 q.2) = Outcome.p
      then Outcome.n else Outcome.p)
    p

-- Reference: `WellFounded.fix_eq` (unfolding of the outcome recursion).
/-- **Fixpoint unfolding** of the outcome recursion (proved). -/
theorem ImpartialGame.outcome_eq (G : ImpartialGame α) (p : α) :
    G.outcome p =
      if _ : ∃ q : {x // x ∈ G.moves p}, G.outcome q.1 = Outcome.p
      then Outcome.n else Outcome.p :=
  WellFounded.fix_eq WellFoundedRelation.wf _ p

-- Reference: [Sprague] 1935 / [Grundy] 1939 — the Sprague–Grundy outcome
-- theorem.
/-- **Sprague–Grundy outcome theorem**: a position is a P-position iff its
Grundy value is `0` (proved by well-founded induction, unfolding `outcome` via
`outcome_eq` and `grundy_eq_zero_iff`). -/
theorem ImpartialGame.outcome_eq_p_iff_grundy_eq_zero (G : ImpartialGame α) (p : α) :
    G.outcome p = Outcome.p ↔ G.grundy p = 0 :=
  WellFounded.induction WellFoundedRelation.wf
    (C := fun p => G.outcome p = Outcome.p ↔ G.grundy p = 0) p (fun p ih => by
    refine ⟨?_, ?_⟩
    · intro h
      refine (grundy_eq_zero_iff G p).mpr fun q hq h0 => ?_
      have hqp : G.outcome q = Outcome.p := (ih q (G.wf p q hq)).mpr h0
      have ho : G.outcome p = Outcome.n :=
        (G.outcome_eq p).trans (ite_eq_left ⟨⟨q, hq⟩, hqp⟩)
      exact Outcome.noConfusion (ho.symm.trans h)
    · intro h
      refine (G.outcome_eq p).trans (ite_eq_right ?_)
      intro hex
      obtain ⟨q, hqo⟩ := hex
      exact ((grundy_eq_zero_iff G p).mp h) q.1 q.2 ((ih q.1 (G.wf p q.1 q.2)).mp hqo))

-- Reference: [Conway] ch. 3 (N-positions: some option is a P-position).
/-- **N-position criterion**: a position is an N-position iff some option is a
P-position (proved by unfolding `outcome_eq`). -/
theorem ImpartialGame.outcome_eq_n_iff (G : ImpartialGame α) (p : α) :
    G.outcome p = Outcome.n ↔ ∃ q ∈ G.moves p, G.outcome q = Outcome.p := by
  refine ⟨?_, ?_⟩
  · intro h
    have hnn : ¬¬ ∃ q : {x // x ∈ G.moves p}, G.outcome q.1 = Outcome.p := by
      intro hno
      exact Outcome.noConfusion (h.symm.trans ((G.outcome_eq p).trans (ite_eq_right hno)))
    obtain ⟨q, hq⟩ := not_not.mp hnn
    exact ⟨q.1, q.2, hq⟩
  · intro h
    obtain ⟨q, hq, hqo⟩ := h
    exact (G.outcome_eq p).trans (ite_eq_left ⟨⟨q, hq⟩, hqo⟩)

end BoringMath
