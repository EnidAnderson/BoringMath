/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Lemmas
import Mathlib.Data.List.Count

/-!
# Chen words: the free monoid on a two-letter alphabet, as data

Data substrate of ticket #141 (TREE R.1.1): the two-letter alphabet
`{x0, x1}` as an inductive type, Chen words as lists of letters (the free
monoid on the alphabet, with `List.append` as the monoid multiplication and
`[]` as the empty word), the weight (length), the depth (number of `x1`
letters), and the reversal-with-swap involution `revSwap`.

## References
* [Mac Lane] S. Mac Lane, *Categories for the Working Mathematician*,
  2nd ed., Springer, 1998, Chapter VI, §4 "Words and Free Semigroups"
  (p. 79): the free monoid on a set `X` is the set `X*` of all words
  (finite lists of letters) over `X`, with concatenation as multiplication.
-/

namespace BoringMath

-- Reference: [Mac Lane], Chapter VI, §4 (the free monoid on `X` is the set of
-- words over the alphabet `X`).
-- REVIEW(citation): web check on 2026-11-01 confirmed the free monoid on a
-- set is constructed in CWM ch. VI §4 "Words and Free Semigroups" (2nd ed.,
-- p. 79); the ticket-suggested Lang ch. I §11 is "Categories and functors"
-- and CWM ch. VII is "Monoids" (monoids in monoidal categories), so this
-- section is cited instead.
/-- **The two-letter alphabet** `{x0, x1}` of Chen words, as data. -/
inductive Letter
  | x0
  | x1
  deriving DecidableEq, Repr

-- Reference: [Mac Lane], Chapter VI, §4 (a word over `X` is a finite list of
-- letters; concatenation of lists is the monoid multiplication, `[]` the unit).
-- REVIEW(citation): same web-verified section as for `Letter`.
/-- **Chen words**: elements of the free monoid on `{x0, x1}`, realized as
pure data — lists of letters, with `List.append` as the monoid `mul` and
`[]` as the empty word. -/
abbrev ChenWord := List Letter

-- Reference: [Mac Lane], Chapter VI, §4 (the length of a word is its number
-- of letters).
-- REVIEW(citation): same web-verified section as for `Letter`.
/-- **Weight** of a Chen word: its length, i.e. the number of letters. -/
def weight (w : ChenWord) : Nat := w.length

-- Reference: [Mac Lane], Chapter VI, §4 (the empty word has length `0`).
/-- The empty word has weight `0`. -/
theorem weight_nil : weight [] = 0 := List.length_nil

-- Reference: [Mac Lane], Chapter VI, §4 (length is additive under
-- concatenation of words).
/-- Weight is additive under concatenation: the weight of `w ++ v` is the
sum of the weights. -/
theorem weight_append (w v : ChenWord) : weight (w ++ v) = weight w + weight v :=
  List.length_append

-- Reference: [Mac Lane], Chapter VI, §4 (prepending a letter adds one to the
-- length of a word).
/-- Weight of a cons: prepending one letter raises the weight by `1`. -/
theorem weight_cons (a : Letter) (w : ChenWord) : weight (a :: w) = weight w + 1 :=
  List.length_cons

-- Reference: [Mac Lane], Chapter VI, §4 (words are counted letter by letter).
/-- Boolean test: is the letter `x1`? -/
def isX1 : Letter → Bool
  | Letter.x0 => false
  | Letter.x1 => true

-- Reference: [Mac Lane], Chapter VI, §4 (a word statistic: count the
-- occurrences of a chosen letter).
-- REVIEW(citation): the choice of `x1` as the counted letter (rather than
-- `x0`) is the documented convention of this module; the two are symmetric
-- under `letterSwap`.
/-- **Depth** of a Chen word: the number of `x1` letters it contains
(the counted letter is `x1` by convention, documented here; counting `x0`
would be symmetric under the letter swap). -/
def depth (w : ChenWord) : Nat := List.countP isX1 w

-- Reference: [Mac Lane], Chapter VI, §4 (permuting the alphabet letter by
-- letter defines a map on words).
/-- **Letter swap** on the alphabet: `x0 ↔ x1`. -/
def letterSwap : Letter → Letter
  | Letter.x0 => Letter.x1
  | Letter.x1 => Letter.x0

-- Reference: [Mac Lane], Chapter VI, §4 (a transposition of two letters is
-- an involution of the alphabet).
/-- The letter swap is an **involution**: swapping twice returns the letter.
This is a primitive definitional lemma (case split on `Letter`, each branch
definitional). -/
theorem letterSwap_involutive (l : Letter) : letterSwap (letterSwap l) = l := by
  cases l
  · rfl
  · rfl

-- Reference: [Mac Lane], Chapter VI, §4 (reversal of a word, combined with the
-- alphabet swap `x0 ↔ x1` applied letter by letter).
/-- **Reversal-with-swap** on Chen words: reverse the list of letters and swap
`x0 ↔ x1` in every letter. -/
def revSwap (w : ChenWord) : ChenWord := (w.reverse).map letterSwap

-- Reference: [Mac Lane], Chapter VI, §4 (definitional unfolding of `revSwap`).
/-- Definitional unfolding of `revSwap`. Primitive definitional lemma. -/
theorem revSwap_def (w : ChenWord) : revSwap w = (w.reverse).map letterSwap := rfl

-- Reference: [Mac Lane], Chapter VI, §4 (the empty word is fixed by reversal
-- and by the letter swap).
/-- The empty word is fixed by `revSwap`. Primitive definitional lemma. -/
theorem revSwap_nil : revSwap [] = [] := rfl

-- Reference: [Mac Lane], Chapter VI, §4 (a one-letter word reverses to itself;
-- the swap then acts on the single letter).
/-- A singleton word maps under `revSwap` to the swapped singleton. Primitive
definitional lemma. -/
theorem revSwap_singleton (a : Letter) : revSwap [a] = [letterSwap a] := rfl

-- Reference: [Mac Lane], Chapter VI, §4 (reversal is an anti-automorphism of
-- the free monoid: the reverse of a concatenation is the concatenation of the
-- reverses, in the opposite order — `List.reverse_append` — and `map` commutes
-- with concatenation — `List.map_append`).
/-- `revSwap` is an **anti-homomorphism** for concatenation:
`revSwap (w ++ v) = revSwap v ++ revSwap w`. -/
theorem revSwap_append (w v : ChenWord) : revSwap (w ++ v) = revSwap v ++ revSwap w :=
  calc revSwap (w ++ v)
      = ((w ++ v).reverse).map letterSwap := revSwap_def (w ++ v)
    _ = (v.reverse ++ w.reverse).map letterSwap :=
        congrArg (List.map letterSwap) (List.reverse_append (as := w) (bs := v))
    _ = v.reverse.map letterSwap ++ w.reverse.map letterSwap :=
        List.map_append (f := letterSwap) (l₁ := v.reverse) (l₂ := w.reverse)
    _ = revSwap v ++ w.reverse.map letterSwap :=
        congrArg (fun t => t ++ w.reverse.map letterSwap) (revSwap_def v).symm
    _ = revSwap v ++ revSwap w :=
        congrArg (fun t => revSwap v ++ t) (revSwap_def w).symm

-- Reference: [Mac Lane], Chapter VI, §4 (reversal is an involution of the
-- free monoid — `List.reverse_reverse` — and the letter swap is an
-- involution — `letterSwap_involutive`; combined via `List.map_reverse`,
-- `List.map_map`, and `List.map_id''`).
/-- `revSwap` is an **involution**: `revSwap (revSwap w) = w`. -/
theorem revSwap_involutive (w : ChenWord) : revSwap (revSwap w) = w :=
  calc revSwap (revSwap w)
      = ((revSwap w).reverse).map letterSwap := revSwap_def (revSwap w)
    _ = (((w.reverse).map letterSwap).reverse).map letterSwap :=
        congrArg (fun t => (t.reverse).map letterSwap) (revSwap_def w)
    _ = (((w.reverse).reverse).map letterSwap).map letterSwap :=
        congrArg (fun t => t.map letterSwap)
          (List.map_reverse (f := letterSwap) (l := w.reverse)).symm
    _ = ((w.reverse).reverse).map (letterSwap ∘ letterSwap) :=
        List.map_map (g := letterSwap) (f := letterSwap) (l := (w.reverse).reverse)
    _ = w.map (letterSwap ∘ letterSwap) :=
        congrArg (fun t => t.map (letterSwap ∘ letterSwap)) (List.reverse_reverse w)
    _ = w := List.map_id'' letterSwap_involutive w

-- Example evaluations (ticket #141(d)): `revSwap` on three example words,
-- together with their `weight` and `depth`.
#eval revSwap [Letter.x0, Letter.x1, Letter.x0]
#eval revSwap [Letter.x1, Letter.x1]
#eval revSwap [Letter.x0, Letter.x1, Letter.x1, Letter.x0]
#eval weight [Letter.x0, Letter.x1, Letter.x0]
#eval depth [Letter.x0, Letter.x1, Letter.x0]
#eval weight [Letter.x1, Letter.x1]
#eval depth [Letter.x1, Letter.x1]
#eval weight [Letter.x0, Letter.x1, Letter.x1, Letter.x0]
#eval depth [Letter.x0, Letter.x1, Letter.x1, Letter.x0]

end BoringMath
