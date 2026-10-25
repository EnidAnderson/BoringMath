# Candidate PR: pushforward of zero-cycles (C.0)

Ticket: BoringMath issue #16 (C.0 remaining scope: pushforward layer).
Branch: `feat/algebraic-cycle-pushforward`.
Module: `BoringMath/AlgebraicGeometry/AlgebraicCycle/Pushforward.lean`
(owner directory: Mathlib's `AlgebraicGeometry/AlgebraicCycle/`,
mirroring `Basic.lean` at the pin; see `docs/OWNERSHIP.md`).

## Statement

* `AlgebraicCycle.pushforward g D : AlgebraicCycle Y ℤ` — the pushforward
  of a zero-cycle along a quasicompact morphism `g : X ⟶ Y`:
  `AlgebraicCycle.map` with constant weights, so that the coefficient at
  `z` is the sum over the fiber of `z` of the coefficients weighted by
  the residue degrees (Fulton, ch. 1). Noncomputable: the fiber sums
  are enumerated by choice.
* `pushforward_apply` — the coefficient of the pushforward at a point is
  the fiber sum of the residue-degree-weighted coefficients
  (`∑ᶠ x ∈ g⁻¹' {z}, D x · [κ(x) : κ(g x)]`). Definitional (`rfl`): with
  constant weights, `mapCoeff` reduces to the residue degree.
* `support_pushforward_subset_image` — the support of the pushforward is
  contained in the image of the support (via the substrate's
  `Function.locallyFinsupp.support_map_subset_of_forall_mem`).
* `IsFinite.pushforward` — the pushforward of a finitely supported cycle
  is finitely supported (the image of a finite support is finite).
* `pushforward_single` — the pushforward of a point cycle is the point
  cycle at the image point, with the coefficient weighted by the residue
  degree: `g_* (r · [x]) = (r · [κ(x) : κ(g x)]) · [g x]` (Fulton, ch. 1).
  The fiber sum is reduced to a singleton sum via
  `finsum_cond_eq_sum_of_cond_iff`; only the point of the cycle
  contributes, by `eq_of_multiplicity_ne_zero`.
* `pushforward_zero` — the pushforward of the zero cycle is the zero
  cycle (the fiber sums vanish termwise:
  `finsum_mem_of_eqOn_zero`, `zero_mul`).
* `pushforward_id` — the pushforward along the identity is the identity
  on cycles (the substrate's `AlgebraicCycle.map_id`; the constant
  weights agree on both sides).
* Support lemmas in the zero-cycle module: `support_single_subset` (the
  support of a point cycle is contained in the singleton of its point;
  now also used by `isFinite_single`), `eq_of_multiplicity_ne_zero` (a
  point of nonzero multiplicity for a point cycle is its point).

## Trace formula findings (GOLD, at the pin)

* The tower law exists: `Module.finrank_mul_finrank (F K A) : finrank F K
  * finrank K A = finrank F A` (`Mathlib/LinearAlgebra/Dimension/Free.lean`),
  with hypotheses `[Module F K] [Module K A] [Module F A]
  [IsScalarTower F K A] [StrongRankCondition F K] [Module.Free F K]
  [Module.Free K A]`. For the residue fields the module-freeness holds
  over fields; the missing piece is the `IsScalarTower` of residue fields
  from the substrate's `residueFieldMap`-composition
  (`residueFieldMap_comp`) — the algebra structures are constructed
  ad-hoc (`letI := (f.residueFieldMap x).hom.toAlgebra`) inside
  `residueDegree`, not as instances.
* Finsum reduction: `finsum_eq_finsetSum_of_support_subset (f) (s)
  (h : support f ⊆ ↑s) : ∑ᶠ i, f i = ∑ i ∈ s, f i` — the same
  explicit-containing-set discipline as `degree`.
* Named next peels: the trace formula `degree h (g_* D) = degree (g ≫ h) D`
  (tower law + fiber re-indexing; the `IsScalarTower` of residue fields
  is the missing construction).

## Literature

* W. Fulton, *Intersection Theory*, ch. 1 (pushforward of zero-cycles:
  `f_* [x] = [κ(x) : κ(f x)] · [f x]`). REVIEW(citation): exact section
  to be pinned by the human referee.
* Stacks Project, *Chow Homology*, tag 02R3 (pushforward of cycles).
