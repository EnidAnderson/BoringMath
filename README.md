# BoringMath

Candidate extensions to Mathlib, organized exactly as if they were pull
requests one could realistically submit (without ever actually submitting
anything). Written strictly in the **boring style**: exact, explicit proofs;
no search, normalization, clever simplification, or sledgehammer tactics;
every declaration named after its standard mathematical theorem; every
declaration carrying an inline literature reference; every eta reduction
peeled into its own named, typed lemma; `sorry` welcomed — with a peeling
plan — whenever an honest proof is not yet instantiated.

The binding style rules are [`docs/STYLE.md`](docs/STYLE.md); agent
instructions are in [`AGENTS.md`](AGENTS.md).

## Build

```bash
lake exe cache get   # prebuilt mathlib oleans (shared, see AGENTS.md)
lake build
```

Requires the `leanprover/lean4:v4.35.0-rc3` toolchain (installed via elan).
