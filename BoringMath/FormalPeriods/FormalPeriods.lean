/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringMath.FormalPeriods.FormalPeriods.FinSum
import BoringMath.FormalPeriods.FormalPeriods.LinearAbelian
import BoringMath.FormalPeriods.FormalPeriods.FreeModHomModule
import BoringMath.FormalPeriods.FormalPeriods.Dual
import BoringMath.FormalPeriods.FormalPeriods.BaseChange
import BoringMath.FormalPeriods.FormalPeriods.PairL
import BoringMath.FormalPeriods.FormalPeriods.Quadruple
import BoringMath.FormalPeriods.FormalPeriods.Symbols
import BoringMath.FormalPeriods.FormalPeriods.Quotient
import BoringMath.FormalPeriods.FormalPeriods.EvalSym
import BoringMath.FormalPeriods.FormalPeriods.Eval

/-!
# The formal-periods setting: the quadruple (𝒜, H_B, H_dR, ∫), P(𝒜) and eval_∫

This module formalizes Hörmann's formal-periods setting (ticket P.4,
definitions only; the theorems are P.5+).  Over an abstract abelian category
`𝒜` (carried by typeclass hypotheses, never axioms — and stated kernel-free,
because the `kernel`/`limit` family is `Classical.choice`-tainted at the pin,
see `docs/AUDITS/2026-10-30-axiom-lint-pin-run.md`), a **quadruple**
`(𝒜, H_B, H_dR, ∫)` consists of two fiber functors into P.1's basis-carrying
vector spaces (`FreeMod B (dim M)`, resp. `FreeMod K (dim M)` — the base fields
`B` (Hörmann's ℚ) and `K` (Hörmann's K ⊆ ℂ) are carried as variables, because
the concrete `Rat.instField` instance is choice-tainted at the pin) and a
natural isomorphism `∫ : H_B ⊗_B L ≅ H_dR ⊗_K L` after base change to a field
extension `L` of `K` (Hörmann takes `L = ℂ`; stated abstractly per the ticket).

The **space of formal periods** `P(𝒜)` is the quotient of the finitely-supported
direct sum `⨁_M H_B(M) ⊗_B H_dR(M)∨` by the morphism relations
`(σ ⊗ α∨(ω))_M = (α(σ) ⊗ ω)_N`.  Following the P.1 pattern, the direct sum is
the quotient of the free `B`-module on abstract symbols `sym M σ ω` by the
bilinearity relations, and the morphism relations are added as generators of a
witness-carrying inductive relation `PeriodChain` (a relation holds iff an
explicit chain exists — built here, not deferred to P.2.3).  `P(𝒜) = Quot` by
that relation; `P(M)` is the image of the `M`-summand in `P(𝒜)`.

Finite sums over `Fin n` are computed as `finSum n f = ((List.finRange n).map
f).sum`: the `Finset` induction/congruence lemmas are `Classical.choice`-tainted
at the pin (P.0.4 census), so the list lemmas used here are proved by hand by
`List` induction, which lints CLEAN.

The evaluation `eval_∫ : P(𝒜) → L`, `(σ ⊗ ω)_M ↦ ω(∫_M σ)`, is defined by
`Quot.lift`, and its well-definedness on the quotient — the main theorem of this
ticket — is proved by induction on the witness chain, the morphism-relation
case being exactly the naturality of `∫`.

## References
* F. Hörmann, *A note on formal periods*, arXiv:2106.03803 (verified against
  the arXiv HTML, v2): Def 2.1 (fiber functor: ℚ-linear, exact, faithful functor
  into f.d.-K-Vect), 2.2 (the quadruple and the natural isomorphism
  `∫ : H_B ⊗_ℚ ℂ ≅ H_dR ⊗_K ℂ`), Def 2.3 (P(𝒜) as the quotient of
  `⨁_M H_B(M) ⊗_ℚ H_dR(M)∨` by the relations (2), and `P(M)` as the image of
  `H_B(M) ⊗_ℚ H_dR(M)∨` in `P(𝒜)`), Def 2.5 (the period conjecture;
  `eval_∫ : P(𝒜) → ℂ`, `(σ⊗ω)_M ↦ ω(∫_M(σ))`).
* S. Mac Lane, *Categories for the Working Mathematician*, 2nd ed., Ch. VIII
  §1 (abelian categories — stated here kernel-free: kernels/cokernels via
  their universal properties, monics are kernels, epics are cokernels) and
  Ch. VIII (exact functors; in abelian categories exactness is equivalent to
  preserving monomorphisms and epimorphisms).
* D. Dummit & R. Foote, *Abstract Algebra*, 3rd ed., §10.4 (tensor products by
  generators and relations; the universal property used for `Quot.lift`).
* S. Axler, *Linear Algebra Done Right*, 4th ed., Ch. 2 (the standard basis of
  `F^n`: every vector is a linear combination of the standard basis).
* Lean 4 core, `Init/Prelude.lean` (`Quot`, `Quot.mk`, `Quot.sound`,
  `Quot.lift`, `Quot.inductionOn`); mathlib, `Mathlib/Data/Quot.lean`
  (`Quot.map₂`, `Quot.map₂_mk`, `Quot.lift_mk`).
-/
