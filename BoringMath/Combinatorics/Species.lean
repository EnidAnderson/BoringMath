/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Basic.Finite.Sum
import Mathlib.Basic.Finite.Prod

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
def Species : Type 1 := {F : Type → Type // ∀ X : Type, Fintype X → Finite (F X)}

namespace Species

variable (S T : Species)

-- Reference: the subtype projection, with the finiteness instance supplied.
/-- The structure type of `S` on the label type `X`. -/
def F (S : Species) (X : Type) [Fintype X] : Type := S.1 X

-- Reference: `Fintype.card` of `F (Fin n)`; the `Finite` field of the species is
-- turned into an enumeration by `Fintype.ofFinite`, which forces `noncomputable`.
attribute [local instance] Fintype.ofFinite in
/-- The **counting sequence** of a species: `card S n = |S(Fin n)|`. -/
noncomputable def card (S : Species) (n : ℕ) : ℕ := by
  have hFin : Finite (S.F (Fin n)) := S.2 (Fin n) inferInstance
  exact Fintype.card (S.F (Fin n))

-- Reference: [Bergeron–Labelle–Leroux], ch. 1 (sum of species); `Fintype.card_sum`.
/-- The **sum** (disjoint union) of two species. -/
def sum (S T : Species) : Species :=
  ⟨fun X => S.1 X ⊕ T.1 X, fun X hX => by
    have hS : Finite (S.1 X) := S.2 X hX
    have hT : Finite (T.1 X) := T.2 X hX
    infer_instance⟩

-- Reference: mathlib pin v4.35.0-rc3: `Fintype.card_congr` with `Equiv.refl`, using
-- `Subsingleton (Fintype α)` — the cardinality of a type does not depend on the
-- chosen `Fintype` instance.
/-- `Fintype.card` is independent of the chosen `Fintype` instance. -/
theorem card_instance_independent (α : Type) (i j : Fintype α) :
    @Fintype.card α i = @Fintype.card α j :=
  @Fintype.card_congr α α i j (Equiv.refl α)

-- Reference: `Fintype.card_sum`.
attribute [local instance] Fintype.ofFinite in
/-- The counting sequence of a sum is the sum of the counting sequences (proved). -/
theorem card_sum (S T : Species) (n : ℕ) : (S.sum T).card n = S.card n + T.card n := by
  have hS : Finite (S.F (Fin n)) := S.2 (Fin n) inferInstance
  have hT : Finite (T.F (Fin n)) := T.2 (Fin n) inferInstance
  have hsum : (S.sum T).card n = Fintype.card (S.F (Fin n) ⊕ T.F (Fin n)) :=
    card_instance_independent _ _ _
  have hS' : Fintype.card (S.F (Fin n)) = S.card n := card_instance_independent _ _ _
  have hT' : Fintype.card (T.F (Fin n)) = T.card n := card_instance_independent _ _ _
  have hcs : Fintype.card (S.F (Fin n) ⊕ T.F (Fin n))
      = Fintype.card (S.F (Fin n)) + Fintype.card (T.F (Fin n)) :=
    Fintype.card_sum (α := S.F (Fin n)) (β := T.F (Fin n))
  calc (S.sum T).card n
      = Fintype.card (S.F (Fin n) ⊕ T.F (Fin n)) := hsum
    _ = Fintype.card (S.F (Fin n)) + Fintype.card (T.F (Fin n)) := hcs
    _ = S.card n + T.card n := congrArg₂ (fun a b : ℕ => a + b) hS' hT'

-- Reference: [Bergeron–Labelle–Leroux], ch. 1 (product of species); `Fintype.card_prod`.
/-- The **product** of two species. -/
def prod (S T : Species) : Species :=
  ⟨fun X => S.1 X × T.1 X, fun X hX => by
    have hS : Finite (S.1 X) := S.2 X hX
    have hT : Finite (T.1 X) := T.2 X hX
    infer_instance⟩

-- Reference: `Fintype.card_prod`.
attribute [local instance] Fintype.ofFinite in
/-- The counting sequence of a product is the product of the counting sequences
(proved). -/
theorem card_prod (S T : Species) (n : ℕ) : (S.prod T).card n = S.card n * T.card n := by
  have hS : Finite (S.F (Fin n)) := S.2 (Fin n) inferInstance
  have hT : Finite (T.F (Fin n)) := T.2 (Fin n) inferInstance
  have hprod : (S.prod T).card n = Fintype.card (S.F (Fin n) × T.F (Fin n)) :=
    card_instance_independent _ _ _
  have hS' : Fintype.card (S.F (Fin n)) = S.card n := card_instance_independent _ _ _
  have hT' : Fintype.card (T.F (Fin n)) = T.card n := card_instance_independent _ _ _
  have hcp : Fintype.card (S.F (Fin n) × T.F (Fin n))
      = Fintype.card (S.F (Fin n)) * Fintype.card (T.F (Fin n)) :=
    Fintype.card_prod (S.F (Fin n)) (T.F (Fin n))
  calc (S.prod T).card n
      = Fintype.card (S.F (Fin n) × T.F (Fin n)) := hprod
    _ = Fintype.card (S.F (Fin n)) * Fintype.card (T.F (Fin n)) := hcp
    _ = S.card n * T.card n := congrArg₂ (fun a b : ℕ => a * b) hS' hT'

end Species

end BoringMath
