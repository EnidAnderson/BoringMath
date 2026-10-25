# Candidate PR: subfield membership cancellation across an inclusion

Branch: `pr/algebra-subfield-mem-cancel`
Module: `BoringMath/Algebra/SubfieldMemCancel.lean`

## Statement

`Subfield.add_mem_cancel_right_of_le`: if `K ≤ K'` are subfields of a
division ring `L`, `a + b ∈ K'`, and `b ∈ K`, then `a ∈ K'`.

The PR as opened carries the statement with a well-typed `sorry` and a
peeling plan (STYLE §7); the proof is to be completed by the coding agent
and reviewed per PR-WORKFLOW before any merge.

## Literature

- N. Jacobson, *Basic Algebra I*, 2nd ed., W. H. Freeman, 1985, Chapter 2,
  §1 (closure of subfields under the field operations).
  REVIEW(citation): pin down the exact section.

## Where it would live in Mathlib

`Mathlib/Algebra/Field/Subfield/Basic.lean`, alongside the derived
membership API (`Subfield.add_mem`, `Subfield.sub_mem`, ...).

## Does Mathlib already have it?

Checked at the pinned revision `v4.35.0-rc3` (2026-10-25):

- `Mathlib/Algebra/Field/Subfield/{Defs,Basic}.lean` read in full: the
  membership API is present (`add_mem`, `sub_mem`, `neg_mem`, ...), but
  there is **no membership-cancellation lemma** and **no membership transfer
  across an inclusion `K ≤ K'`**.
- `add_mem_cancel_right` exists only for `Submodule`
  (`Mathlib/Algebra/Module/Submodule/Defs.lean`) and inside
  `Mathlib/Analysis/SpecialFunctions/Elliptic/Weierstrass.lean`: single
  subobject, no inclusion transfer.
- Nearest neighbor in `Subfield/Basic.lean`: `Subfield.notMem_of_notMem_closure`
  (different shape: closure vs. subset, not sums).

Conclusion: **not in Mathlib**; the two-subfield transfer form is new.

## Program context

This is the formal seed of the register's `paid_of_escape` reduction
(Section 63, PEEL G): `rho + Ci(2π) = E` with `E ∈ K1`, so `Ci(2π) ∈ K0`
would force `rho ∈ K1`; contrapositive: `rho ∉ K1 → Ci(2π) ∉ K0` (L1).
It is the first compilable edge of the reduction graph of the weight-3
clause (Section 62, FINDING 1: the reduction layer is pure subfield algebra).

## Review notes

- Naming follows the `Submodule`/`AddSubgroup` cancel convention with an
  `_of_le` transfer suffix; reviewer to confirm.
- The `sorry` is deliberate (statement-only candidate; fidelity test of
  the PR workflow): the coding agent completes the proof on this branch.
- Line budget: the honest proof is expected at ≤ 6 lines under the tactic
  whitelist (task bound: 20).
