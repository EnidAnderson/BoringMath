/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod

/-!
# Combinatorial species (Joyal) — the functor skeleton — ticket #293

A **species** is a functor `F : Type → Type` that assigns to every finite type
`X` a finite type `F X` of "structures on the label set `X`". This module lands
the definition, the counting function `card S n = |F(Fin n)|`, and the sum and
product species with their cardinality formulas proved.

## References
* [Bergeron–Labelle–Leroux] *Combinatorial Species and Tree-like Structures*,
  Cambridge 1998, ch. 1.
* mathlib pin v4.35.0-rc3: `Fintype.card_sum`, `Fintype.card_prod`.
-/

namespace BoringMath

-- Reference: [Bergeron–Labelle–Leroux], ch. 1, §1.1 (a species is a functor from
-- finite sets and bijections to finite sets).
/-- A **combinatorial species**: an endofunctor on types that is finitary on
finite carriers. -/
def Species : Type 1 := {F : Type → Type // ∀ X : Type, Fintype X → Fintype (F X)}

namespace Species

variable (S T : Species)

-- Reference: the subtype projection, with the finiteness instance supplied.
/-- The structure type of `S` on the label type `X`. -/
def F (S : Species) (X : Type) [Fintype X] : Type := S.1 X

-- Reference: `Fintype.card` of `F (Fin n)`.
/-- The **counting sequence** of a species: `card S n = |S(Fin n)|`. -/
def card (S : Species) (n : ℕ) : ℕ := Fintype.card (S.F (Fin n))

-- Reference: [Bergeron–Labelle–Leroux], ch. 1 (sum of species); `Fintype.card_sum`.
/-- The **sum** (disjoint union) of two species. -/
def sum (S T : Species) : Species :=
  ⟨fun X => S.1 X ⊕ T.1 X, fun X hX => by
    haveI := S.2 X hX
    haveI := T.2 X hX
    infer_instance⟩

-- Reference: `Fintype.card_sum`.
/-- The counting sequence of a sum is the sum of the counting sequences (proved). -/
theorem card_sum (S T : Species) (n : ℕ) : (S.sum T).card n = S.card n + T.card n :=
  Fintype.card_sum (S.F (Fin n)) (T.F (Fin n))

-- Reference: [Bergeron–Labelle–Leroux], ch. 1 (product of species); `Fintype.card_prod`.
/-- The **product** of two species. -/
def prod (S T : Species) : Species :=
  ⟨fun X => S.1 X × T.1 X, fun X hX => by
    haveI := S.2 X hX
    haveI := T.2 X hX
    infer_instance⟩

-- Reference: `Fintype.card_prod`.
/-- The counting sequence of a product is the product of the counting sequences
(proved). -/
theorem card_prod (S T : Species) (n : ℕ) : (S.prod T).card n = S.card n * T.card n :=
  Fintype.card_prod (S.F (Fin n)) (T.F (Fin n))

end Species

end BoringMath
