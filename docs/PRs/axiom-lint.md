# Candidate PR: axiom lint (`pr/formal-periods-axiom-lint`)

Tickets: P.0.1 (#102, the lint core) and P.0.2 (#103, the taint probes),
both leaves of P.0 (#92), both level-0.

## Statement

One new module `BoringMath/FormalPeriods/AxiomLint.lean`:

* `BoringMath.builtinAxioms` — the four built-in axioms
  (`propext`, `Quot.sound`, `Classical.choice`, `Lean.ofReduceBool`).
* `BoringMath.AxiomGrade` — the grade: `clean` / `sorryTainted` /
  `choiceTainted` / `banned`.
* `BoringMath.AxiomGrade.ofAxioms` — the three-grade decision on an axiom
  set, precedence `banned` > `sorryTainted` > `choiceTainted` > `clean`.
* `BoringMath.lintAxioms` — collect the axioms of one declaration
  (`Lean.collectAxioms`) and grade them.
* `#lint_axioms <name>` — the command form: prints grade + axiom set,
  errors on `banned`.

Plus one quarantined probe file `probes/AxiomLintProbes.lean` (outside the
`BoringMath.+` glob, so excluded from the build target; run by hand with
`lake env lean`): a deliberate `sorry` probe, a `Classical.em` probe, a
user-`axiom` probe, and a clean control, each linted at the bottom.

## Literature

* R. Diaconescu, *Axiom of Choice and Complementation*, Proc. Amer. Math.
  Soc. 51 (1975), 176–178 (DOI 10.2307/2039513) — verified against the
  published paper: the routing `Classical.choice ⟹ Classical.em`, so the
  single choice-lint enforces both the choice and the LEM ban. No
  `REVIEW(citation)` tag.
* `#print axioms` / `Lean.collectAxioms`, `Lean.Elab.Print` (Lean 4 core,
  v4.35.0-rc3).
* Mathlib's `Mathlib/Util/AssertNoSorry.lean` — the `assert_no_sorry`
  command this lint generalizes (read at the pin).
* Program notes §§169–172 (the choice-free / LEM-free law, 2026-10-30) —
  internal, not literature.

## Where it would live in Mathlib

Not a Mathlib candidate — this is program infrastructure (ticket owner tag
`[mathlib]` refers to the P line's placement in `BoringMath/FormalPeriods/`).
A lint harness would live in Mathlib's CI tooling (`scripts/`), which is
out of scope for a content PR.

## Does Mathlib already have it?

Partially: `assert_no_sorry` (`Mathlib/Util/AssertNoSorry.lean`) checks
only `sorryAx`. The three-grade decision and the ban check are new.

## Verification (machine-checked at the pin, v4.35.0-rc3, 2026-10-30)

`lake build BoringMath.FormalPeriods.AxiomLint` builds warning-clean;
`scripts/check-style.sh` on the new files reports 0 violations;
`lake env lean probes/AxiomLintProbes.lean` prints (exit 1 is the
deliberate BANNED error on the axiom probe):

* `probeSorry : sorryTainted`, axioms `[sorryAx]`;
* `probeClassicalEm : choiceTainted`, axioms `[propext, Classical.choice,
  Quot.sound]` — the Diaconescu routing is visible at the pin;
* `probeAxiom : banned`, and `#lint_axioms probeAxiom` raises the BANNED
  error;
* `probeClean : CLEAN`, axioms `[]`; `BoringMath.AxiomGrade.ofAxioms :
  CLEAN`, axioms `[propext]`.

Honest finding: `BoringMath.lintAxioms` itself grades `choiceTainted`
(axioms `[propext, Classical.choice, Quot.sound]`) because
`Lean.collectAxioms` is choice-backed in its *meta* code at the pin. This
is harmless for the lint's purpose — meta-code choice never enters proof
terms — and the decision function `AxiomGrade.ofAxioms`, the part that
matters, lints CLEAN.

## Pin-run evidence (feeds P.0.4 / #105, run 2026-10-30 via `#print axioms`)

* CHOICE-TAINTED at the pin (grade [K] stands), all depending on
  `[propext, Classical.choice, Quot.sound]`: `CategoryTheory.Limits.HasLimit`,
  `HasColimit`, `limit`, `kernel`, `cokernel`, `HasKernels`,
  `kernel.condition`, `HasPullbacks`, `pullback`, `HasEqualizers`,
  `equalizer`, `HasFiniteLimits`, `Module.Free.chooseBasis`,
  `Module.Free.exists_basis`, `Module.Free.of_divisionRing`,
  `Finsupp.single`, `DirectSum.of`, `DFinsupp.sum`, `LinearMap.range`,
  `Submodule.Quotient.mk`.
* CLEAN at the pin: `LinearMap.ker` and `Submodule.span`
  (`[propext, Quot.sound]`), `TensorProduct.tmul` (`[propext, Quot.sound]`),
  `LinearMap.id` and `Nat.one_add` (no axioms).

So both architecture claims of P.0 are CONFIRMED: mathlib's
`HasLimit`/`HasColimit` (and the whole `HasFiniteLimits`/`pullback`/
`equalizer` family) extract their data through `Classical.choice`, and
`Module.Free.chooseBasis` is choice-extracted. The constructive
replacements (P.1 basis-as-structure, explicit finite (co)limits in P.3)
are needed, not optional. Also confirmed: at v4.35.0-rc3 `native_decide`
mints a per-declaration axiom `<decl>._native.native_decide.ax_…`, which
the grader's non-builtin-axiom rule bans automatically.

## Review notes

Human reviewer's decision pending.
