# Candidate PR: specialization in open subspaces

Ticket: BoringMath issue #16 (C.0 clause 3: the generic-point transfer —
the locality of specialization, an input of the scheme-level
specialization lifting for flat morphisms). Branch: `feat/opens-specializes`.
Module: `BoringMath/Topology/Order/Opens.lean`
(owner directory: Mathlib's `Topology/Order.lean` at the pin, where
`Specializes` and `closure_induced` live; see `docs/OWNERSHIP.md`).

## Statement

* `TopologicalSpace.Opens.specializes_iff` — **specialization in an open
  subspace is specialization in the ambient space**, and conversely: for
  two points of an open `U`, `x' ⤳ x` in `U` iff `x' ⤳ x` in the ambient
  space. The closure in the induced topology of the subtype is the ambient
  closure of the image (`closure_induced`), and the image of a singleton
  is a singleton.

## Notes

* The consumer is the scheme-level specialization lifting for flat
  morphisms: the lifted specialization is produced in an affine open and
  transported to the ambient scheme, and the specialization hypothesis is
  imported from the ambient scheme into the affine open.

## Verification

* `lake build` clean (2741 jobs, zero warnings).
* `scripts/check-style.sh` zero violations, zero sorries.
