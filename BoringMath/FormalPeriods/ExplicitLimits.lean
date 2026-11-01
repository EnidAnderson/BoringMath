/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringMath.FormalPeriods.ExplicitLimits.Basic
import BoringMath.FormalPeriods.ExplicitLimits.Quotient
import BoringMath.FormalPeriods.ExplicitLimits.Products
import BoringMath.FormalPeriods.ExplicitLimits.Limits
import BoringMath.FormalPeriods.ExplicitLimits.Pushouts
import BoringMath.FormalPeriods.ExplicitLimits.Colimit
import BoringMath.FormalPeriods.ExplicitLimits.ColimLift
import BoringMath.FormalPeriods.ExplicitLimits.ColimWitness
import BoringMath.FormalPeriods.ExplicitLimits.ColimRel

/-!
# Explicit finite (co)limits for the chase layer + an explicit filtered colimit

Ticket P.3 (issue #95), leaf of the FORMAL PERIODS line. The P.0.4 pin-run
confirmed that mathlib's chosen-limits API (`HasLimit`, `pullback`,
`equalizer`, `HasFiniteLimits`, ...) is `Classical.choice`-backed at the pin
`v4.35.0-rc3` (see `docs/AUDITS/2026-10-30-axiom-lint-pin-run.md`), so this
module builds the computable replacements as DATA-parameterized
constructions (STYLE §2.3: data taken explicitly, never instance-chosen):

* a general explicit linear map `VecHom` between arbitrary carriers of
  vector-space operations (generalizing the P.1 `FreeModHom` to subtype and
  quotient carriers);
* subspaces as data (`Subspace`), and quotients of carriers by subspaces as
  an explicit `Quot` (witness-carrying, `Quot.sound` only — the `FreeTensor`
  precedent);
* the finite (co)limit shapes Hörmann's chase consumes: terminal object and
  binary products (hence finite products, Mac Lane III.5), equalizers
  (kernels of `f - g`), pullbacks of monos (intersections — Key Lemma 3.2,
  Prop 3.6), images (`N' := p(L')`), quotients, pushouts (Prop 3.6), and
  biproducts;
* ONE explicit filtered colimit over a small filtered category of
  basis-carrying spaces: the quotient of the hand-built finitely-supported
  direct sum (an inductive, since `Finsupp.single` is CHOICE-TAINTED at the
  pin) by the diagram-arrow relations — the shape of Theorem 4.1's colimit
  over the span-category `Q̃A`.

Each construction is a named explicit definition plus its universal-property
lemma. The filtered-colimit injection-preservation lemma
(`colimLeg_injective_of_transition_injective`) carries its dies-in-colimit
witness as a finite chain (proof-relevant data, `ColimChain`), per the
constructive form of "filtered colimits preserve injections".

Everything lints CLEAN (`{propext, Quot.sound}` only) — see the
`#lint_axioms` block at the end of this file.

## References
* F. Hörmann, *A note on formal periods*, arXiv:2106.03803 — Key Lemma 3.2
  (pullbacks of monos / intersections `N' ∩ M^n`, images `N' := p(L')`, the
  `(1,…,1,λ)` automorphism), Prop 3.6 (monomorphisms of exact sequences,
  pushouts), Lemma 3.5 (`Q̃A` filtered) and Theorem 4.1 (the colimit over
  `Q̃A`; morphisms map to injections) — verified against the arXiv HTML
  <https://arxiv.org/html/2106.03803>.
* S. Mac Lane, *Categories for the Working Mathematician*, 2nd ed., Springer,
  1998 — Ch. III §3–§4 (p. 62/68: coproducts/colimits, products/limits,
  equalizers, pullbacks, pushouts), Ch. III §5 (p. 72: categories with finite
  products), Ch. V §2 (p. 112: limits by products and equalizers), Ch. VIII
  §1 and §4 (p. 191, 202: kernels/cokernels, the diagram lemmas of the chase),
  Ch. IX §1 (p. 211: filtered (co)limits in Set — the dies-in-colimit
  description of elements). Section titles/pages verified against the book's
  own table of contents <https://d-nb.info/955028914/04>.
  -- REVIEW(citation): pin the exact theorem number inside Mac Lane IX.1 for
  the elementwise description of filtered colimits in Set in review.
* S. Axler, *Linear Algebra Done Right*, 4th ed., Ch. 1 (linear maps,
  subspaces, quotients).
* D. Dummit & R. Foote, *Abstract Algebra*, 3rd ed., §10.4 (generators and
  relations; the quotient construction used by `FreeTensor`).
-/
