# Pin-run report: axiom grades of mathlib declarations the P line touches (2026-10-30)

Ticket: P.0.4 (#105), leaf of P.0 (#92). Evidence: `#print axioms` and
`#lint_ledger` (the new lint, `BoringMath/FormalPeriods/AxiomLint.lean` +
`AxiomLedger.lean`, branch `feat/formal-periods-axiom-lint`) run at the pin
`leanprover/lean4:v4.35.0-rc3`, mathlib `v4.35.0-rc3` (checkout
`c55e6e78`). Grades: CLEAN = axioms ⊆ {propext, Quot.sound};
CHOICE-TAINTED = reaches `Classical.choice`; SORRY-TAINTED = reaches
`sorryAx`; BANNED = `native_decide` minted axiom or user axiom.

## Claim 1 — `HasLimit`/`HasColimit` extract cone data via `Classical.choice`

**CONFIRMED — the [K] grade stands.** All of these depend on exactly
`[propext, Classical.choice, Quot.sound]`:

`CategoryTheory.Limits.HasLimit`, `HasColimit`, `limit`, `kernel`,
`cokernel`, `HasKernels`, `kernel.condition`, `HasPullbacks`, `pullback`,
`HasEqualizers`, `equalizer`, `HasFiniteLimits`.

So the whole chosen-limits family is choice-backed at the pin; the P.3
explicit finite (co)limits must not route through it.

## Claim 2 — `Module.Free.chooseBasis` is choice-extracted

**CONFIRMED — the [K] grade stands.** `Module.Free.chooseBasis`,
`Module.Free.exists_basis`, `Module.Free.of_divisionRing` all depend on
`[propext, Classical.choice, Quot.sound]`. The ledger makes the mechanism
visible: `chooseBasis`'s dependency set contains `Exists.choose` and
`Nonempty.some` — the basis is literally `Classical.choice` applied to
`Nonempty`. P.1's basis-as-structure replacement is needed, not optional.

## Claim 3 — taint census of the P-line import paths

CHOICE-TAINTED (`[propext, Classical.choice, Quot.sound]`):
`LinearMap.range`, `Submodule.Quotient.mk`, `Finsupp.single`,
`DirectSum.of`, `DFinsupp.sum`.

CLEAN: `LinearMap.ker` and `Submodule.span` and `TensorProduct.tmul`
(`[propext, Quot.sound]`); `LinearMap.id`, `Nat.one_add` (no axioms).

## Mechanism note — `native_decide` at this pin

A `native_decide` proof does NOT depend on a fixed `ofReduceBool` axiom at
v4.35.0-rc3; it mints a per-declaration axiom
`<decl>._native.native_decide.ax_…` (verified: `ndTest` depends on
`[ndTest._native.native_decide.ax_1_1]`). The grader's rule "any non-builtin
axiom other than `sorryAx` is BANNED" catches these automatically.

## Diaconescu routing check (§169.1b)

Verified at the pin: a proof of `p ∨ ¬p` via `Classical.em` grades
CHOICE-TAINTED with axiom set `[propext, Classical.choice, Quot.sound]` —
the `Classical.em` proof term routes through `Classical.choice`, so the
single choice-lint enforces the LEM ban too. Reference: R. Diaconescu,
*Axiom of Choice and Complementation*, Proc. Amer. Math. Soc. 51 (1975),
176–178 (DOI 10.2307/2039513), verified against the published paper.

## Consequence for the P line

P.1 (basis-as-structure finite vector spaces) and P.3 (explicit finite
(co)limits + filtered colimit) cannot consume the chosen-data mathlib
API; they must build the constructive replacements narrowly, taking data
explicitly (STYLE §2.3). Nothing collapses; both [K] grades stand.
