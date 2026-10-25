# AGENTS.md — BoringMath

`BoringMath` holds candidate extensions to Mathlib, organized exactly as if
they were pull requests one could realistically submit. **We never actually
push or pull-request anything public**; this is purely the organization of our
code.

## Binding rules

1. **The boring style is mandatory.** Read and follow `docs/STYLE.md` before
   writing any code. Never use a banned tactic, even "just this once". Never
   close a `sorry` by weakening a statement.
2. **Human review is mandatory.** Every commit on a `pr/*` branch is a
   *candidate commit*: the human reviews and may revise each one. `main`
   advances only by the human reviewer's decision. Agents must never push
   to any remote.
3. Every declaration: named after its standard mathematical theorem, inline
   literature reference (chapter and section), explicit exact proof or a
   well-typed `sorry` with a peeling plan.
4. Every eta reduction is peeled into its own named, typed lemma.

## Commands

```bash
lake update          # refresh dependencies (rare; pinned to v4.35.0-rc3)
lake exe cache get   # fetch/refresh prebuilt mathlib oleans
lake build           # build (must be warning-clean except deliberate sorries)
scripts/check-style.sh   # style backstop
```

## Layout

- `BoringMath/<Area>/<Topic>.lean` — candidate mathlib modules; one
  mathematical topic per module, importable as `BoringMath.<Area>.<Topic>`.
- `docs/STYLE.md` — the binding style rules.
- `docs/PRs/<topic>.md` — one note per candidate PR: statement, literature,
  where it would live in Mathlib, whether Mathlib already has it.
- `scripts/` — tooling (style backstop).

## Environment facts

- Toolchain pinned to `leanprover/lean4:v4.35.0-rc3` in `lean-toolchain`.
- `.lake/packages` is a **directory junction** shared with `BoringLab` and
  the pre-existing `EnidsMathMadness` project (`C:\Users\enida\Documents\
  Lean\EnidsMathMadness`), which owns the single mathlib checkout and its
  built oleans. Do not delete `EnidsMathMadness`. Do not bump the mathlib
  revision casually: all three projects share the checkout, so mathlib is
  bumped only in lockstep across all of them.
- Git identity is not configured globally; the repos use the local identity
  `Enid <enid@localhost>`. Change it in each repo with `git config` if
  desired.
