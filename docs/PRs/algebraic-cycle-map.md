# Candidate PR: the weight-general ring on `AlgebraicCycle.map` (C.0.b)

Ticket: BoringMath issue #88 (TREE C.0.b, the weight-general remainder of the
C.0.a split of #34). Tier 0 (pure locallyFinsupp bookkeeping).
Branch: `feat/formal-periods-axiom-lint` (worktree branch; the content PR is
purely additive).
Module: `BoringMath/AlgebraicGeometry/AlgebraicCycle/Map.lean`
(owner directory: Mathlib's `AlgebraicGeometry/AlgebraicCycle/`, mirroring
`Basic.lean` at the pin; a future
`Mathlib/AlgebraicGeometry/AlgebraicCycle/Map.lean`; see `docs/OWNERSHIP.md`).

## Statement

All lemmas are over mathlib's `AlgebraicCycle.map` with **arbitrary weight
functions** `wx : X → N`, `wy : Y → N` (`[DecidableEq N]`) and general
coefficients `{R : Type*} [Semiring R]`, matching `map`'s own signature.

* `map_apply` — the coefficient at `z` is
  `∑ᶠ x ∈ f ⁻¹' {z}, c x * (mapCoeff f wx wy x : R)`. Definitional (`rfl`),
  via mathlib's `Function.locallyFinsupp.map_apply`.
* `finite_support_inter_fiber_of_coeff` — the support of a cycle meets a fiber
  of a quasicompact morphism in a finite set (general coefficients; the landed
  `finite_support_inter_fiber` in `Pushforward.lean` is the `ℤ` instance and is
  not duplicated — different name, no clash). Compact-open basis of the
  prespectral space of points +
  `LocallyFiniteSupport.finite_inter_support_of_isCompact`.
* `map_zero` — `map f wx wy 0 = 0`; pointwise `locallyFinsuppWithin.ext` +
  `finsum_mem_of_eqOn_zero` (the landed `pushforward_zero` pattern).
* `map_add` — `map f wx wy (c + d) = map f wx wy c + map f wx wy d`; pointwise:
  `multiplicity_add`, `add_mul`, `finsum_mem_add_distrib'` with the fiber
  finiteness (the landed `pushforward_add` pattern).
* `map_single` — `map f wx wy (single x r) = single (f.base x) (r * (mapCoeff f wx wy x : R))`;
  the fiber sum reduces to a singleton/empty sum via
  `finsum_cond_eq_sum_of_cond_iff` (the landed `pushforward_single` pattern).
* `mapHom` — the bundled `AddMonoidHom` over the weight pair
  (`toFun := map f wx wy`, `map_zero'`, `map_add'`); data explicit per
  STYLE §2.3. Noncomputable: the fiber sums in `map` are enumerated by choice.
* `mapHom_apply` — `mapHom f wx wy c = map f wx wy c` (definitional, `rfl`).
* `mapCoeff_comp` — **the weight law along a tower**: under the weight
  compatibility `wy (g.base x) = wz ((g ≫ h).base x)`,
  `mapCoeff (g ≫ h) wx wz x = mapCoeff g wx wy x * mapCoeff h wy wz (g.base x)`.
  Pure `ite` case split (`ite_eq_left`/`ite_eq_right`) + the landed
  `Scheme.Hom.residueDegree_comp` (Tower.lean) — the residue degrees multiply
  along the tower.
* `map_comp` — **the composition law**:
  `map (g ≫ h) wx wz c = map h wy wz (map g wx wy c)` under the same explicit
  weight-compatibility hypothesis. The landed `pushforward_comp` re-indexing
  skeleton (`Finset.sum_fiberwise_of_maps_to`, constant weight on each fiber,
  extension vanishing off the support), with the `tower` step now consuming
  `mapCoeff_comp`.
* `mapHom_comp` — `mapHom (g ≫ h) wx wz = (mapHom h wy wz).comp (mapHom g wx wy)`
  under the same hypothesis (`AddMonoidHom.ext` + `map_comp`).

## Findings (honest, per the ticket)

* **Mathlib already has it? No.** At the pin (v4.35.0-rc3),
  `Mathlib/AlgebraicGeometry/AlgebraicCycle/Basic.lean` defines
  `AlgebraicCycle.map` with the weight pair and only `map_id`;
  `Mathlib/Topology/LocallyFinsupp/Pushforward.lean`
  (`Function.locallyFinsupp.map`) carries only `map_apply`,
  `support_map_subset_of_forall_mem`, `map_id` — no
  `map_zero`/`map_add`/`map_comp` at either level. So the ring is proved here
  directly on `AlgebraicCycle.map` (not relined from the substrate).
* **Weight-compatibility finding (the ticket's expected FINDING):** the
  weight-free case (landed `pushforward_comp`) needed no weight bookkeeping, but
  the weight-general `map_comp` genuinely requires the explicit clause
  `wy (g.base x) = wz ((g ≫ h).base x)` — without it, `mapCoeff (g≫h)` can be
  nonzero while the product of the step weights vanishes. This is exactly what
  mathlib's `map` docstring says the weights are for ("to make the pushforward
  operation functorial"). Stated explicitly in the theorem, not papered over.
* Citations verified online at stacks.math.columbia.edu:
  02QR = Chow Homology Def. 42.8.1 (cycles); 02R3 = §42.12 Proper pushforward
  (incl. "the proper pushforward of cycles is a homomorphism of abelian
  groups"); 02R4 = Def. 42.12.1 (weight `deg(Z/f(Z)) [f(Z)]`);
  02R5 = Lemma 42.12.2 (`g_* ∘ f_* = (g ∘ f)_*`);
  02RB = Def. 42.14.1 flat pullback (the weight-based pullback analogue, §42.14 —
  not used in this module, recorded because the ticket asked to verify it).
  Fulton pins follow the 2026-10-30 citation audit correction (ch. 1 §1.3) and
  keep `REVIEW(citation)` as in the landed C.0 files.

## Literature

* Stacks Project, *Chow Homology*, tags 02QR, 02R3, 02R4, 02R5
  (https://stacks.math.columbia.edu/tag/02QR etc.; all opened and verified).
* W. Fulton, *Intersection Theory*, ch. 1, §1.3 (push-forward and its
  functoriality). REVIEW(citation): exact section to be pinned by the human
  referee (per the 2026-10-30 audit, ch. 1 §1.3).

## Review notes

* `lake build BoringMath.AlgebraicGeometry.AlgebraicCycle.Map` — success,
  warning-clean (0 warnings, 0 sorries). `scripts/check-style.sh` on the file:
  0 violations.
* No existing file was edited; the only new files are the module and this note.
* The weight-free clauses of C.0.a (`pushforward_zero`/`pushforward_add`/
  `pushforward_comp`/`pushforwardHom*` in `Pushforward.lean`) are not duplicated:
  this module is the weight-general ring over arbitrary `wx`/`wy` and general
  `[Semiring R]` coefficients; it imports `Zero.lean` (`multiplicity_add`,
  `support_single_subset`) and `ResidueField/Tower.lean` (`residueDegree_comp`).
* NONLINEAR: the hypothesis `hwt x` is used twice in the positive branch of
  `mapCoeff_comp`; flagged per STYLE §2.2.
