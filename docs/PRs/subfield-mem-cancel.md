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
- **Proof instantiated** (coding agent, 2026-10-25): the sorry is replaced
  by a single direct term — no tactic is used at all, per the direct-proof
  preference of the boring style:

  ```lean
  Eq.subst (add_sub_cancel_right a b)
    (Subfield.sub_mem K' h (mem_of_le_of_mem hle hb))
  ```

  The proof is linear: each input (`hle`, `h`, `hb`) is used exactly once.
- **Mathlib lemmas used** (all verified against the pinned `v4.35.0-rc3`):
  - `mem_of_le_of_mem` — `Mathlib/Data/SetLike/Basic.lean:268`, an alias
    of `IsConcreteLE.le_iff`: membership transfer along `K ≤ K'`.
  - `Subfield.sub_mem` — `Mathlib/Algebra/Field/Subfield/Defs.lean:236`:
    closure of subtraction. (Precision found in review: in this revision
    the Subfield membership API lives in `Defs.lean`, not `Basic.lean`.)
  - `add_sub_cancel_right` — the `to_additive` form of
    `mul_div_cancel_right`, `Mathlib/Algebra/Group/Defs.lean:81`:
    `a + b - b = a`.
  - `Eq.subst` — Leibniz substitutivity of equality, the primitive through
    which all equality-based rewriting is done here.
- **Verification** (both outputs, per the work order):
  - `lake build`: `Build completed successfully (996 jobs)`; no warnings
    for `BoringMath.Algebra.SubfieldMemCancel` (its sorry is gone; the
    build's only warnings are the pre-existing deliberate sorries in
    `BoringMath/Foundations/Eta.lean`).
  - `scripts/check-style.sh`: `0 violation(s)` (after fixing a checker
    false positive found in review — declaration detection now ignores
    docstring prose; the fix ships with this PR).
