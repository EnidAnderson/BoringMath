# Candidate PR: zero-cycles and the degree (C.0)

Ticket: BoringMath issue #16 (C.0, AlgebraicCycle buildout). Branch:
`pr/algebraic-cycle-zero`.
Module: `BoringMath/AlgebraicGeometry/AlgebraicCycle/Zero.lean` (owner
directory: Mathlib's `AlgebraicGeometry/AlgebraicCycle/`, mirroring the
upstream placement of `Basic.lean` at the pin; see `docs/OWNERSHIP.md`).

**Revision (2026-10-26, peeling and naming decree):** per the human
referee's standing rules — every eta reduction peeled into its own
short, named, non-idiosyncratic theorem, named as the mathematical
literature names the construction — the module was restructured around
two standard notions:

* the **multiplicity** of a point in a cycle (the coefficient: Fulton
  ch. 1; `multiplicity_add`, `multiplicity_single`);
* the **local degree** of a cycle at a point (the multiplicity weighted
  by the residue degree — the local degree of an extension in algebraic
  number theory, and the local multiplicity of a finite morphism:
  `localDegree`, `localDegree_add`, `localDegree_zero`,
  `localDegree_single`, `localDegree_eq_zero_of_notMem_support`).

The degree is now literally the sum of the local degrees, and
`degree_add` is a three-line calculation: pointwise additivity of the
local degrees (`Finset.sum_congr`), linearity of the summation
(`Finset.sum_add_distrib`), and termwise addition of the two
restrictions (`congrArg₂` over `HAdd.hAdd`, with the restrictions by
`Finset.sum_subset` and vanishing off the support). All
substitution-under-context steps are `congrArg₂` over the named global
multiplication `HMul.hMul` (Leibniz substitutivity into the first
factor); no anonymous mathematical lambda remains. Statements are
unchanged; `degree` keeps its signature (the body is now the sum of
`localDegree`).

## Statement

The zero-cycle layer on top of `Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic`
(at the pin: `AlgebraicCycle X R` as `Function.locallyFinsupp X R`,
`stacks 02QR`):

* `AlgebraicCycle.IsFinite D : Prop` — the support of `D` is a finite set
  (a zero-cycle is a finitely-supported cycle).
* `isFinite_zero`, `IsFinite.add`, `isFinite_single` — the empty formal
  sum, sums, and point cycles `[x]` are finitely supported.
* `multiplicity_add`, `multiplicity_single` — the multiplicity of a
  point in a sum of cycles is the sum of the multiplicities; the point
  cycle `r · [x]` has multiplicity `r` at `x`.
* `localDegree g D x : ℤ` — the local degree at `x`: the multiplicity
  of `x` weighted by the residue degree `[κ(x) : κ(g x)]`. With
  `localDegree_add`, `localDegree_zero`, `localDegree_single`,
  `localDegree_eq_zero_of_notMem_support` (vanishing off the support).
* `degree g D s _hs : ℤ` — the degree (trace): the sum of the local
  degrees over an explicitly given finite set `s` containing the
  support. The containing set is carried as explicit data
  (`Set.Finite.toFinset` is noncomputable at the pin), and the value is
  independent of the choice because local degrees vanish off the
  support (`Function.notMem_support`).
* `degree_zero`, `degree_single`, `degree_add` — the degree of the zero
  cycle is zero; the degree of `r · [x]` is `r · [κ(x) : κ(g x)]`; the
  degree is additive.
* `support_add_subset_union` — the support of a sum of cycles is
  contained in the union of any two finite sets containing the
  summands' supports (the witness needed to sum `D + E` over `s ∪ t`).

All proofs are direct terms or `calc` chains over named lemmas
(`Eq.subst`/`Eq.subset`, `congrArg`, `Finset.sum_congr`,
`Finset.sum_add_distrib`, `Finset.sum_subset`, `Pi.add_apply`,
`add_mul`, `zero_mul`, `Function.notMem_support`, `Function.support_add`,
`Pi.support_single_subset`, `ite_eq_left`); no sorry, no banned tactics,
no `rw`, zero warnings, `lake build` and `check-style.sh` clean.

## Computability note (STYLE §2.3)

`degree` is `noncomputable`, and this is content-forced: the residue
degree `Hom.residueDegree` is `Module.finrank` of a field extension, and
the rank of a field extension is nonconstructive in general (no finite
basis is given by the data). The finiteness predicate and its laws carry
no computability cost. Flagged in the module as a mathemathical remark
on the degree, per the referee's standing computability preference.

## Named obstructions (recorded, not in this module)

* Trace formula `deg (f_* c) = deg c` for the pushforward
  (`AlgebraicCycle.map`, `stacks 02R3`): `map` is defined against
  weight functions `wx : X → N` and its `mapCoeff` sums over the fiber
  over each point `z`; the trace identity requires re-indexing the sum
  over the fiber and needs a fiber-finiteness hypothesis not yet stated
  in the substrate. Needs its own module and a GOLD read of
  `Mathlib/Topology/LocallyFinsupp/Pushforward.lean` beyond the surface
  API.
* Flat pullback on cycles: needs the flat-morphism API (`Flat`) and the
  local-finiteness of preimages under flat morphisms; separate GOLD
  reads required before staking statements.
* Well-definedness of `degree` in the containing set `s` (degree is
  independent of the choice of `s`): provable from
  `Function.notMem_support` by the same vanishing computation as in
  `degree_add`; deliberately not declared here to keep the module
  minimal — it belongs with the trace-formula module where it is
  consumed.

## Clause (4) verification (ticket B-line note)

Normal forms for cycles are already free at the pin:
`Function.locallyFinsuppWithin.ext` (pointwise equality of cycles
implies equality) plus the pointwise defeq coercions
(`coe_zero`, `coe_add` proved by `rfl`) give pointwise normal forms;
nothing was rebuilt.

## Literature

* W. Fulton, *Intersection Theory*, ch. 1, §1 (cycles as finite formal
  sums; point cycles; degrees). REVIEW(citation): exact section to be
  pinned by the human referee.
* Stacks Project, *Chow Homology*, tags 02QR–02R9 (algebraic cycles,
  pushforward, residue degrees).
