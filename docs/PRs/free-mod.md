# Candidate PR: basis-carrying free modules (`pr/formal-periods-free-mod`)

Ticket: P.1.1 (#106), leaf of P.1 (#93). P.0's gate is satisfied on branch
`feat/formal-periods-axiom-lint` (lint + ledger + pin-run report; the
pin-run confirmed `Module.Free.chooseBasis` is `Classical.choice`-extracted
— see `docs/AUDITS/2026-10-30-axiom-lint-pin-run.md`).

## Statement

One new module `BoringMath/FormalPeriods/FreeMod.lean`:

* `BoringMath.FreeMod K n` — abbrev for `Fin n → K`, the basis-carrying
  finite free module (vectors in the standard basis; dimension is data).
* Module-law peels `freeMod_add`, `freeMod_zero`, `freeMod_smul`,
  `freeMod_add_zero`, `freeMod_zero_add`, `freeMod_one_smul`,
  `freeMod_smul_assoc` — one-liners over the pointwise `Pi` instances.
* `freeModDim n : ℕ` — dimension as data.
* `FreeModHom K m n` — morphisms as explicit structure (function +
  linearity proofs), with `freeModHomId` and `freeModHomComp`.
* `FreeModDual K n` — abbrev for `FreeModHom K n 1` (Hom into the ground
  field).
* `freeModDecidableEq` — constructive decidable equality.
* Two smoke `example`s exercising the API.

## Literature

* F. Hörmann, *A note on formal periods*, arXiv:2106.03803, Definition 2.1 —
  verified against the arXiv HTML: a fiber functor over `K` is a
  `ℚ`-linear exact faithful functor into f.d.-`K`-Vect; this module models
  that target category. No `REVIEW(citation)` tag.
* S. Axler, *Linear Algebra Done Right*, 4th ed., Ch. 1 (definition of a
  vector space; the module laws are its axioms for a field).

## Where it would live in Mathlib

Not a Mathlib candidate in this form (Mathlib's `Module.Free` /
`chooseBasis` is the choice-backed version); this is the program-owned
constructive substrate in `BoringMath/FormalPeriods/`, drafted upstreamable
in style.

## Does Mathlib already have it?

Mathlib has `Fin n → K` with `Pi` module instances (used here) and
`Module.Free.chooseBasis` (choice-extracted — the pin-run CONFIRMED the [K]
grade). What Mathlib lacks is the basis-as-structure packaging with
lint-CLEAN decidable equality; note `Fintype.decidablePiFintype` itself is
CHOICE-TAINTED at the pin (its `by simp` proof reaches `Classical.choice`),
so `freeModDecidableEq` is built directly via `decidable_of_iff` +
`funext_iff.symm` over the pointwise-forall instance, which lints CLEAN.

## Verification (machine-checked at the pin, v4.35.0-rc3)

* `lake build BoringMath.FormalPeriods.FreeMod` — warning-clean;
  `scripts/check-style.sh` — 0 violations.
* `#lint_axioms` on every declaration of the module: all **CLEAN**
  (`[propext, Quot.sound]` or no axioms) — including `freeModDecidableEq`
  after the constructive rebuild. Zero `Classical.choice`, zero `sorryAx`:
  the P.1.1 acceptance criterion.

## Review notes

Human reviewer's decision pending.
