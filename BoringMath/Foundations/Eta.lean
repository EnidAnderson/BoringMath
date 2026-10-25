/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Init

/-!
# Eta conversion, in the boring style

This module records the basic eta conversion laws, and doubles as the
reference specimen for the *boring style* (see `docs/STYLE.md`): every
declaration is named after its standard mathematical designation, every
declaration carries an inline literature reference, proofs are exact and
explicit, and any proof not yet honestly instantiated carries a well-typed
`sorry` together with a peeling plan.

Eta conversion is the identification of a function with its eta expansion;
in the lambda calculus literature it is the conversion rule
`η : (λ x. f x) → f`.

## References
* [Barendregt] H. P. Barendregt, *The Lambda Calculus: Its Syntax and
  Semantics*, North-Holland, 1984.
* [Mac Lane] S. Mac Lane, *Categories for the Working Mathematician*,
  2nd ed., Springer, 1998.
-/

universe u v w

namespace BoringMath

-- Reference: [Barendregt], Chapter 2 (eta conversion).
-- REVIEW(citation): pin down the exact section in review.
/-- **Eta conversion** for functions: every function is equal to its eta
expansion. -/
theorem eta {α : Type u} {β : Type v} (f : α → β) : (fun x => f x) = f := rfl

-- Reference: [Barendregt], Chapter 2 (eta conversion, symmetric form).
-- REVIEW(citation): pin down the exact section in review.
/-- **Eta conversion**, symmetric form: every function is equal to its eta
expansion, read from right to left. -/
theorem eta_symm {α : Type u} {β : Type v} (f : α → β) : f = fun x => f x :=
  Eq.symm (eta f)

-- Reference: [Mac Lane], Chapter III, §4 (the eta law for cartesian products).
-- REVIEW(citation): pin down the exact section in review.
/-- **Eta conversion for ordered pairs**: every ordered pair is equal to the
pair assembled from its components. -/
theorem eta_pair {α : Type u} {β : Type v} (p : α × β) : (p.1, p.2) = p := rfl

-- Reference: [Barendregt], Chapter 2 (eta conversion is a congruence).
-- REVIEW(citation): pin down the exact section in review.
/-- **Eta conversion respects composition**: eta expansion of the inner
factor inside a composition changes nothing. -/
theorem eta_comp {α : Type u} {β : Type v} {γ : Type w} (f : β → γ) (g : α → β) :
    (fun x => f ((fun y => g y) x)) = fun x => f (g x) := by
  -- TEMPORARY SORRY: the honest proof has not been instantiated yet.
  -- PEELING PLAN: eta-reduce the inner expansion via `rw [eta g]`, leaving a
  -- goal of the form `(fun x => f (g x)) = fun x => f (g x)`, which is the
  -- primitive eta lemma `eta (fun x => f (g x))` (permitted as `rfl` only
  -- because it is a primitive definitional lemma).
  sorry

end BoringMath
