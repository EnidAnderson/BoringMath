/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringMath.CombinatorialGames.Outcome
import Mathlib.Data.LawfulXor.Basic

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
nim-sum of the Grundy values.

SANCTIONED SORRY — peeling plan: well-founded induction on `(a, b)` (lex).
By `grundy_eq`, `grundy (a,b) = mex S` where `S = {g(a') ^^^ h(b)} ∪
{g(a) ^^^ h(b')}` (using the IH on options). Show `mex S = g(a) ^^^ h(b)` via
`mex_eq_of_not_mem_and_forall`:
1. `g(a) ^^^ h(b) ∉ S`: else `g(a') = g(a)` (xor-cancel) contradicting
   `mex_not_mem`, resp. symmetric.
2. For `m < g(a) ^^^ h(b)`: let `k` be the top bit of `m ^^^ (g(a)^^^h(b))`
   (`Nat.log2`); since `m < c`, bit `k` of `c` is `1`. Case on whether bit
   `k` of `g(a)` is `1`: then `m ^^^ h(b) < g(a)` (top-bit argument), so
   `m ^^^ h(b) = g(a')` for some option `a'` (all values below the mex are
   attained), giving `m = g(a') ^^^ h(b) ∈ S`. Else bit `k` of `h(b)` is
   `1` and symmetrically `m ^^^ g(a) < h(b)` gives `m ∈ S`.
   Bit manipulations via `Nat.testBit_xor`, `Nat.lt_of_testBit`-style lemmas
   at the pin. -/
theorem ImpartialGame.grundy_sum (G : ImpartialGame α) (H : ImpartialGame β)
    (a : α) (b : β) :
    (G.sum H).grundy (a, b) = nimSum (G.grundy a) (H.grundy b) := by
  sorry

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
