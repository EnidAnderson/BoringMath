/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringMath.FormalPeriods.FreeTensor.Basic
import BoringMath.FormalPeriods.FreeTensor.Relations
import BoringMath.FormalPeriods.FreeTensor.Universal

/-!
# The constructive tensor product of basis-carrying free modules

`FreeTensor K m n` is the tensor product of `FreeMod K m` and `FreeMod K n`
over a field `K` (concretely usable at `K = ℚ`), constructed the way
Hörmann's Key Lemma 3.2 proof constructs `H_B(M) ⊗_ℚ H_dR(M)∨`: the quotient
of the free module on abstract symbols `σ ⊗ ω` modulo the bilinearity
relations (i)–(iv).  Equality of formal sums is proof-relevant: a witness
chain (`TensorChain`) is data, and two formal sums are identified precisely
when a chain exists.

Because the P.0.4 pin-run census found `Finsupp.single` CHOICE-TAINTED at the
pin (see `docs/AUDITS/2026-10-30-axiom-lint-pin-run.md`), the free module on
symbols is built by hand as the inductive `TensorSym` (constructors `nil`,
`add`, `sym`, `smul`), not via `Finsupp`.  The only quotient axiom used is
`Quot.sound`, which is in the lint's clean set, so every declaration of this
module lints CLEAN (`{propext, Quot.sound}` only).

## References
* F. Hörmann, *A note on formal periods*, arXiv:2106.03803, proof of Key
  Lemma 3.2 (verified against the arXiv HTML): the tensor product as the
  quotient of the (free) monoid on abstract symbols `σ⊗ω` modulo the
  relations (i) `x+σ⊗0 ∼ x+0⊗ω ∼ x`, (ii) `x+σ₁⊗ω+σ₂⊗ω ∼ x+(σ₁+σ₂)⊗ω`,
  (iii) `x+σ⊗ω₁+σ⊗ω₂ ∼ x+σ⊗(ω₁+ω₂)`, (iv) `x+σ⊗(λω) ∼ x+(λσ)⊗ω`.
* D. Dummit & R. Foote, *Abstract Algebra*, 3rd ed., §10.4 (tensor products
  of modules: generators-and-relations construction and the universal
  property — bilinear maps factor uniquely through `M ⊗ N`).
* Lean 4 core, `Init/Prelude.lean` and `Init/Core.lean` (`Quot`, `Quot.mk`,
  `Quot.sound`, `Quot.lift`, `Quot.ind`, `Quot.inductionOn`).
-/
