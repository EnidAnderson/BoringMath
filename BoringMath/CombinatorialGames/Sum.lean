/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringMath.CombinatorialGames.Outcome
import Mathlib.Data.LawfulXor.Basic
import Mathlib.Data.Nat.Bitwise

/-!
# Disjoint sums of impartial games — the Sprague–Grundy xor theorem

CombinatorialGames ticket #333 (CGT.3). The **disjoint sum** `G + H` of two
finite impartial games has positions `(a, b)` and moves changing exactly one
component. The **Sprague–Grundy theorem** says the Grundy value of a sum is
the nim-sum (xor) of the Grundy values: `grundy (a, b) = grundy a ^^^ grundy b`.
Together with `outcome_eq_p_iff_grundy_eq_zero` this gives the full outcome
theorem for sums: `G + H` is a P-position iff `grundy G a = grundy H b`.

## References
* [Sprague] 1935; [Grundy] 1939; [Conway] ch. 3; [Berlekamp–Conway–Guy]
  vol. 1, ch. 2 (the xor theorem).
* mathlib pin v4.35.0-rc3: `LawfulXor Nat` (xor_comm/assoc/self/zero/
  eq_zero_iff), `Nat.xor_bit`, `Nat.xor_trichotomy`.
* Program register: BoringMath #331–#334.
-/

namespace BoringMath

open scoped Classical

variable {α β : Type*} [WellFoundedRelation α] [WellFoundedRelation β]

-- Reference: mathlib pin v4.35.0-rc3, `LawfulXor Nat` instance.
/-- Nim-sum is commutative (proved). -/
theorem nimSum_comm (a b : ℕ) : nimSum a b = nimSum b a := xor_comm a b

/-- Nim-sum is associative (proved). -/
theorem nimSum_assoc (a b c : ℕ) : nimSum (nimSum a b) c = nimSum a (nimSum b c) :=
  xor_assoc a b c

/-- `a ^^^ a = 0` (proved). -/
theorem nimSum_self (a : ℕ) : nimSum a a = 0 := xor_self a

/-- `a ^^^ 0 = a` (proved). -/
theorem nimSum_zero (a : ℕ) : nimSum a 0 = a := xor_zero a

/-- `a ^^^ b = 0 ↔ a = b` (proved). -/
theorem nimSum_eq_zero_iff (a b : ℕ) : nimSum a b = 0 ↔ a = b := xor_eq_zero_iff

-- Reference: mathlib pin v4.35.0-rc3, `LawfulXor Nat` (`xor_cancel_right`).
/-- Nim-sum cancels on the right: `(a ^^^ b) ^^^ b = a` (proved). -/
theorem nimSum_cancel_right (a b : ℕ) : nimSum (nimSum a b) b = a := xor_cancel_right a b

-- Reference: mathlib pin v4.35.0-rc3, `LawfulXor Nat` (`xor_cancel_left`).
/-- Nim-sum cancels on the left: `a ^^^ (a ^^^ b) = b` (proved). -/
theorem nimSum_cancel_left (a b : ℕ) : nimSum a (nimSum a b) = b := xor_cancel_left a b

/-- The **disjoint sum** of two finite impartial games: a move changes exactly
one component. -/
noncomputable def ImpartialGame.sum (G : ImpartialGame α) (H : ImpartialGame β) :
    ImpartialGame (α × β) where
  moves p := (G.moves p.1).image (fun a' => (a', p.2)) ∪
    (H.moves p.2).image (fun b' => (p.1, b'))
  wf p q h := by
    rcases Finset.mem_union.mp h with h | h
    · obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp h
      exact Prod.Lex.left _ _ (G.wf p.1 a' ha')
    · obtain ⟨b', hb', rfl⟩ := Finset.mem_image.mp h
      exact Prod.Lex.right p.1 (H.wf p.2 b' hb')

-- Reference: [Sprague] 1935 / [Grundy] 1939 — the xor theorem.
/-- **Sprague–Grundy theorem**: the Grundy value of a disjoint sum is the
nim-sum of the Grundy values (proved by well-founded induction on `(a, b)`
under `Prod.Lex`, via `mex_eq_of_not_mem_and_forall`: non-membership by
xor-cancellation against `mex_not_mem`; attainment of every
`m < g(a) ^^^ h(b)` by `Nat.lt_xor_cases` (mathlib pin v4.35.0-rc3,
`Mathlib/Data/Nat/Bitwise.lean:296`) plus `exists_move_grundy_eq_of_lt`). -/
theorem ImpartialGame.grundy_sum (G : ImpartialGame α) (H : ImpartialGame β)
    (a : α) (b : β) :
    (G.sum H).grundy (a, b) = nimSum (G.grundy a) (H.grundy b) :=
  WellFounded.induction WellFoundedRelation.wf
    (C := fun p : α × β => (G.sum H).grundy p = nimSum (G.grundy p.1) (H.grundy p.2))
    (a, b) (fun p ih => by
      rcases p with ⟨a, b⟩
      change (G.sum H).grundy (a, b) = nimSum (G.grundy a) (H.grundy b)
      have hnot : nimSum (G.grundy a) (H.grundy b) ∉
          ((G.sum H).moves (a, b)).attach.image (fun q => (G.sum H).grundy q.1) := by
        intro hmem
        obtain ⟨q, _, hq⟩ := Finset.mem_image.mp hmem
        have hqm : q.1 ∈ (G.moves a).image (fun a' => (a', b)) ∪
            (H.moves b).image (fun b' => (a, b')) := q.2
        rcases Finset.mem_union.mp hqm with hl | hr
        · obtain ⟨a', ha', haeq⟩ := Finset.mem_image.mp hl
          have hih : (G.sum H).grundy (a', b) = nimSum (G.grundy a') (H.grundy b) :=
            ih (a', b) (Prod.Lex.left b b (G.wf a a' ha'))
          have hq' : (G.sum H).grundy (a', b) = nimSum (G.grundy a) (H.grundy b) :=
            Eq.subst (motive := fun x => (G.sum H).grundy x = nimSum (G.grundy a) (H.grundy b))
              haeq.symm hq
          have heq : nimSum (G.grundy a') (H.grundy b) = nimSum (G.grundy a) (H.grundy b) :=
            hih.symm.trans hq'
          have hcan : G.grundy a' = G.grundy a :=
            (nimSum_cancel_right (G.grundy a') (H.grundy b)).symm.trans
              ((congrArg (fun n => nimSum n (H.grundy b)) heq).trans
                (nimSum_cancel_right (G.grundy a) (H.grundy b)))
          have hmem' : G.grundy a ∈ ((G.moves a).attach.image (fun q => G.grundy q.1)) :=
            Finset.mem_image.mpr ⟨⟨a', ha'⟩, Finset.mem_attach _ _, by exact hcan⟩
          have hnotmem : G.grundy a ∉ ((G.moves a).attach.image (fun q => G.grundy q.1)) := by
            intro hga
            have h2 : mex ((G.moves a).attach.image (fun q => G.grundy q.1)) ∈
                ((G.moves a).attach.image (fun q => G.grundy q.1)) :=
              Eq.subst (motive := fun n => n ∈ ((G.moves a).attach.image (fun q => G.grundy q.1)))
                (G.grundy_eq a) hga
            exact mex_not_mem _ h2
          exact (hnotmem hmem').elim
        · obtain ⟨b', hb', hbeq⟩ := Finset.mem_image.mp hr
          have hih : (G.sum H).grundy (a, b') = nimSum (G.grundy a) (H.grundy b') :=
            ih (a, b') (Prod.Lex.right a (H.wf b b' hb'))
          have hq' : (G.sum H).grundy (a, b') = nimSum (G.grundy a) (H.grundy b) :=
            Eq.subst (motive := fun x => (G.sum H).grundy x = nimSum (G.grundy a) (H.grundy b))
              hbeq.symm hq
          have heq : nimSum (G.grundy a) (H.grundy b') = nimSum (G.grundy a) (H.grundy b) :=
            hih.symm.trans hq'
          have hcan : H.grundy b' = H.grundy b :=
            (nimSum_cancel_left (G.grundy a) (H.grundy b')).symm.trans
              ((congrArg (nimSum (G.grundy a)) heq).trans
                (nimSum_cancel_left (G.grundy a) (H.grundy b)))
          have hmem' : H.grundy b ∈ ((H.moves b).attach.image (fun q => H.grundy q.1)) :=
            Finset.mem_image.mpr ⟨⟨b', hb'⟩, Finset.mem_attach _ _, by exact hcan⟩
          have hnotmem : H.grundy b ∉ ((H.moves b).attach.image (fun q => H.grundy q.1)) := by
            intro hgb
            have h2 : mex ((H.moves b).attach.image (fun q => H.grundy q.1)) ∈
                ((H.moves b).attach.image (fun q => H.grundy q.1)) :=
              Eq.subst (motive := fun n => n ∈ ((H.moves b).attach.image (fun q => H.grundy q.1)))
                (H.grundy_eq b) hgb
            exact mex_not_mem _ h2
          exact (hnotmem hmem').elim
      have hforall : ∀ m, m < nimSum (G.grundy a) (H.grundy b) →
          m ∈ ((G.sum H).moves (a, b)).attach.image (fun q => (G.sum H).grundy q.1) := by
        intro m hm
        have hm' : m < G.grundy a ^^^ H.grundy b := hm
        rcases Nat.lt_xor_cases hm' with h | h
        · obtain ⟨a', ha', hav⟩ := G.exists_move_grundy_eq_of_lt a h
          have hih : (G.sum H).grundy (a', b) = nimSum (G.grundy a') (H.grundy b) :=
            ih (a', b) (Prod.Lex.left b b (G.wf a a' ha'))
          have hmeq : m = nimSum (G.grundy a') (H.grundy b) :=
            calc m = nimSum (nimSum m (H.grundy b)) (H.grundy b) :=
                  (nimSum_cancel_right m (H.grundy b)).symm
              _ = nimSum (G.grundy a') (H.grundy b) :=
                  (congrArg (fun n => nimSum n (H.grundy b)) hav).symm
          have hmem : (a', b) ∈ (G.sum H).moves (a, b) := by
            change (a', b) ∈ (G.moves a).image (fun a' => (a', b)) ∪
              (H.moves b).image (fun b' => (a, b'))
            exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ ha')
          refine Finset.mem_image.mpr ⟨⟨(a', b), hmem⟩, Finset.mem_attach _ _, ?_⟩
          change (G.sum H).grundy (a', b) = m
          exact hih.trans hmeq.symm
        · obtain ⟨b', hb', hbv⟩ := H.exists_move_grundy_eq_of_lt b h
          have hih : (G.sum H).grundy (a, b') = nimSum (G.grundy a) (H.grundy b') :=
            ih (a, b') (Prod.Lex.right a (H.wf b b' hb'))
          have hmeq : m = nimSum (G.grundy a) (H.grundy b') :=
            calc m = nimSum (nimSum m (G.grundy a)) (G.grundy a) :=
                  (nimSum_cancel_right m (G.grundy a)).symm
              _ = nimSum (H.grundy b') (G.grundy a) :=
                  (congrArg (fun n => nimSum n (G.grundy a)) hbv).symm
              _ = nimSum (G.grundy a) (H.grundy b') := nimSum_comm _ _
          have hmem : (a, b') ∈ (G.sum H).moves (a, b) := by
            change (a, b') ∈ (G.moves a).image (fun a' => (a', b)) ∪
              (H.moves b).image (fun b' => (a, b'))
            exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hb')
          refine Finset.mem_image.mpr ⟨⟨(a, b'), hmem⟩, Finset.mem_attach _ _, ?_⟩
          change (G.sum H).grundy (a, b') = m
          exact hih.trans hmeq.symm
      exact ((G.sum H).grundy_eq (a, b)).trans (mex_eq_of_not_mem_and_forall hnot hforall))

-- Reference: [Sprague] 1935 / [Grundy] 1939 — the outcome theorem for sums.
/-- **Outcome theorem for sums**: `G + H` is a P-position at `(a, b)` iff the
Grundy values of the components agree (proved from
`outcome_eq_p_iff_grundy_eq_zero`, `grundy_sum`, and `nimSum_eq_zero_iff`). -/
theorem ImpartialGame.outcome_sum_eq_p_iff (G : ImpartialGame α) (H : ImpartialGame β)
    (a : α) (b : β) :
    (G.sum H).outcome (a, b) = Outcome.p ↔ G.grundy a = H.grundy b :=
  ((G.sum H).outcome_eq_p_iff_grundy_eq_zero (a, b)).trans
    ((Iff.of_eq (congrArg (fun n => n = 0) (G.grundy_sum H a b))).trans
      (nimSum_eq_zero_iff (G.grundy a) (H.grundy b)))

end BoringMath
