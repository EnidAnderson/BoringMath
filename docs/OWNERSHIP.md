# Ownership map

The directory tree names each file's **owner**: the upstream community or
program layer that would review it. A candidate PR is "realistic" precisely
when it lives in the directory of its owner, mirroring the owner's own
tree. When in doubt about where a proof naturally lives, ask: *whose
reviewer reads this directory?*

## BoringMath

- `BoringMath/CategoryTheory/...`, `BoringMath/Algebra/...`,
  `BoringMath/Algebra/Field/Subfield/...`, ... — **Mathlib-owned
  territory**: candidate Mathlib PRs. The directory mirrors Mathlib's
  tree exactly: `CategoryTheory/Sites/CdStructure.lean` would land in
  `Mathlib/CategoryTheory/Sites/CdStructure.lean`;
  `Algebra/Field/Subfield/MemCancel.lean` belongs to the Subfield area
  (`Mathlib/Algebra/Field/Subfield/`, whose membership API lives in
  `Defs.lean` at the pin). One mathematical topic per file; the file is
  the extracted diff against its owner area.
- `BoringMath/CombinatorialGames/...` — **combinatorial-games-owned
  territory** (the A-lines: thermography, cooling, misère quotients,
  outcome classes): candidate PRs to the external library
  `vihdzp/combinatorial-games` (Apache-2.0); directories mirror that
  library's tree (`CombinatorialGames/Game/...`). Pending the
  toolchain/pin comparison gate recorded in the depth audit.
- `BoringMath/Foundations/...` — **program-owned primitives**: the
  boring-style foundation lemmas (the eta discipline) on which the lab
  depends. Not candidates; these are ours, and they stay small.
- `docs/STYLE.md`, `docs/PR-WORKFLOW.md`, `docs/OWNERSHIP.md`,
  `docs/AUDITS/`, `docs/PRs/`, `scripts/` — **protocol-owned**: shared
  mutable files; the modular fast-forward protocol's serialization rule
  governs them.

## BoringLab

- `BoringLab/<Area>/...` — **program-owned experimental territory**: the
  dictionary layer, the conjecture layer, the computational harnesses. No
  upstream mirroring; idiosyncrasy is permitted here.
- `BoringLab/Games/Basic.lean` is slated for supersession by the external
  `combinatorial-games` dependency (pending the toolchain gate): its
  hand-rolled game structure duplicates externally-owned territory and
  will be superseded, never revised.

## Rules

1. A new module goes in the directory of its owner; if no owner directory
   exists in our tree, create the mirror path.
2. Never place a file where a different owner would review it.
3. When ownership is genuinely shared or uncertain (a lemma both Mathlib
   and the CGT library could own), the PR note must record the ownership
   decision and its reason.
4. Module names follow file paths exactly (Lean's rule), so a move is an
   API rename: do moves as serialized, human-ordered restructure PRs.
