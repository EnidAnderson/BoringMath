# Candidate PR: the residue field tower (C.0 trace-formula gate)

Ticket: BoringMath issue #16 (C.0: the trace formula's gate). Branch:
`feat/residue-field-tower`.
Module: `BoringMath/AlgebraicGeometry/ResidueField/Tower.lean` (owner
directory: Mathlib's `AlgebraicGeometry/ResidueField.lean` at the pin;
the tower extends that file's residue field API; see `docs/OWNERSHIP.md`).

## Statement

* `Scheme.Hom.residueFieldAlgebra` — the residue field of a point is an
  algebra over the residue field of its image, via the residue field map
  (`RingHom.toAlgebra`). Noncomputable: the residue field of a point is
  the residue field of a stalk.
* `Scheme.Hom.residueFieldAlgebra_comp` — the same algebra, indexed at
  the composite: the residue field of the middle point is an algebra over
  the residue field of the image under the composite (the point of the
  composite is the image of the middle point).
* `Scheme.Hom.residueFieldMap_comp_apply` — the residue field map of a
  composite is the composite of the residue field maps, at elements.
* `Scheme.Hom.residueFieldIsScalarTower` — the residue fields along a
  composite form a scalar tower (scalar multiplication by the top
  residue field factors through the middle one). Stated with explicit
  scalar-multiplication structures; the tower is the transport of
  `residueFieldMap_comp` along the algebra structures.
* `Scheme.Hom.residueDegree_comp` — **the tower law for residue
  degrees**: the residue degree of a composite is the product of the
  residue degrees along the tower,
  `(g ≫ h).residueDegree x = h.residueDegree (g x) * g.residueDegree x`
  (via `Module.finrank_mul_finrank`, the tower law for the ranks of free
  modules: every residue field is a free module over a subfield).

## Notes

* The substrate constructs the algebra of a residue field map ad hoc
  (`letI := (f.residueFieldMap x).hom.toAlgebra` inside
  `Hom.residueDegree`); the instances here are the same algebras,
  declared once. The compatibility instance
  `residueFieldAlgebra_comp` exists because the point of a composite and
  the image of the middle point are definitionally equal but not
  syntactically equal, and instance resolution works syntactically.
* This retires the trace-formula obstruction recorded in
  `docs/PRs/algebraic-cycle-pushforward.md`: the residue-field
  `IsScalarTower` now exists. The trace formula
  `degree h (g_* D) = degree (g ≫ h) D` additionally needs the
  fiber re-indexing of the degree sums (finsum over fibers against the
  containing set) — the next peel on the ticket.

## Literature

* S. Lang, *Algebra*, revised 3rd ed., Springer, 2002 (the tower law:
  the degree of a tower of field extensions is the product of the
  degrees; scalar multiplication by the top field factors through the
  middle one). REVIEW(citation): exact section to be pinned by the human
  referee.
* Stacks Project, *Chow Homology*, tag 02R4 (the residue degree as the
  weight of the pushforward). REVIEW(citation): exact tag to be pinned.
