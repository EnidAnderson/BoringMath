# Candidate PR: over-sites from arbitrary precoverages — the Mathlib TODO resolves negatively (`pr/sites-over-precoverage`)

Issue #45 (TREE H.11): generalize
`over_toGrothendieck_eq_toGrothendieck_comap_forget` (Mathlib
`CategoryTheory/Sites/Over.lean`, above the TODO "Generalize this section to
arbitrary precoverages.") to arbitrary precoverages `K`, i.e. drop
`[K.HasPullbacks] [K.IsStableUnderBaseChange]`.

## Verdict (first-class FINDING)

**The generalization is FALSE as stated.** The identity
`K.toGrothendieck.over X = (K.comap (Over.forget X)).toGrothendieck` does not
hold for arbitrary precoverages; only one of the two inequalities survives
without the base-change hypotheses. The module below proves the surviving
inequality and *refutes* the other with a machine-checked counterexample.

### Counterexample shape (formalized in the module)

* Category: the poset `C` on four objects `W, Z, Zp, X` with relations
  `W ≤ Z`, `Zp ≤ Z`, `W ≤ X` and no others (`OverPrecoverageCounterexample.Ob`).
* Precoverage `K`: the only covering presieve is the **empty presieve** `⊥` at
  `Z` (precoverages impose no conditions, so this is legitimate).
* `Over Ob.X` has only the objects `(W ⟶ X)` and `(X ⟶ X)`; no object of it
  has left component `Z` (`Z ≰ X`), so `K.comap (Over.forget Ob.X)` is the
  empty precoverage, and `(K.comap (Over.forget Ob.X)).toGrothendieck` is the
  **bottom** topology (only `⊤` covering).
* But `Sieve.generate ⊥ = ⊥` is covering for `K.toGrothendieck` at `Z`
  (`Saturate.of`), so its pullback along `a : W ⟶ Z` — the empty sieve at
  `W` — is covering at `W` (`Saturate.pullback`). Hence, by the over-topology
  criterion (SGA 4 III 5.2.1), the empty sieve at `V = Over.mk v` is covering
  for `K.toGrothendieck.over Ob.X`.
* The bottom topology does not contain the empty sieve (`⊥ ≠ ⊤`), so the two
  topologies on `Over Ob.X` differ:
  `OverPrecoverageCounterexample.over_toGrothendieck_ne_comap_forget_toGrothendieck`,
  and universally
  `OverPrecoverageCounterexample.not_forall_over_toGrothendieck_eq_comap_forget_toGrothendieck`.

### Where the Mathlib hypotheses enter

In `Over.lean` the `≤` direction (LHS ≤ comap-generated) is proved by
induction on `Coverage.mem_toGrothendieck` after rewriting with
`Precoverage.toGrothendieck_toCoverage`, which *requires*
`[J.HasPullbacks] [J.IsStableUnderBaseChange]`; that conversion is exactly what
turns the `pullback` constructor of `Precoverage.Saturate` into the
pullback-free `Coverage.Saturate`. The counterexample exploits precisely that
constructor: a pullback of a covering sieve along an arrow with no pullbacks
can produce sieves (here `⊥`) that the comap precoverage cannot generate.
The other inequality never needed the hypotheses.

## Statement (one new module `BoringMath/CategoryTheory/Sites/OverPrecoverage.lean`)

* `CategoryTheory.Sieve.overEquiv_apply_eq_functorPushforward_forget` —
  definitional peel: `Sieve.overEquiv Y S = S.functorPushforward (Over.forget X)`.
* `CategoryTheory.GrothendieckTopology.mem_over_toPrecoverage_iff_comap_forget` —
  for a topology `J`, `Q ∈ (J.over X).toPrecoverage V ↔
  Q ∈ (J.toPrecoverage).comap (Over.forget X) V` (the precoverage-level identity
  underlying the unconditional inequality).
* `CategoryTheory.Precoverage.comap_forget_toGrothendieck_le_over_toGrothendieck` —
  **the surviving inequality, no hypotheses**: for arbitrary `K`,
  `(K.comap (Over.forget X)).toGrothendieck ≤ K.toGrothendieck.over X`.
  Proved via the Galois connection `toGrothendieck_le_iff_le_toPrecoverage`.
* `CategoryTheory.OverPrecoverageCounterexample.*` — the counterexample poset,
  the precoverage `K`, and the two refutation theorems above. Sorry-free.

## Literature

* SGA 4, Exposé III (Verdier, *Fonctorialité des catégories de faisceaux*),
  §5.2.1 — the topology on `C/X`: a sieve of `Y : C/X` is covering iff its
  image under the forgetful functor is. Cited by mathlib's `Over.lean`
  docstring; `REVIEW(citation)` tags in the file record that web mirrors of
  SGA 4 Exposé III (normalesup.org / orgogozo / cmls.polytechnique.fr)
  confirm §5 treats the induced topology on `C/X` ("site induit C/X",
  III 5.1, and "cribles de la catégorie C/X"), while the literal proposition
  number 5.2.1 could not be quoted verbatim from searchable text — pin in
  review (W5/#13 owns citation pins).
* J. Riou, `Mathlib/CategoryTheory/Sites/Over.lean` — the hypothesis-bound
  identity and the TODO, read in full at the pin (GOLD).
* B. Guillemet–A. Topaz, `Mathlib/CategoryTheory/Sites/PrecoverageToGrothendieck.lean`
  — `Precoverage.Saturate`, `toGrothendieck`, the Galois connection, read in
  full at the pin (GOLD).

## Where it would live in Mathlib

`Mathlib/CategoryTheory/Sites/Over.lean` itself, as the resolution of its
TODO: the surviving inequality would replace the second bullet of the proof of
`over_toGrothendieck_eq_toGrothendieck_comap_forget` (which needs no
hypotheses), and the counterexample documents why the first bullet cannot be
weakened. Upstream may then deprecate the hypothesis-bound lemma in favour of
the inequality — noted here, never executed by us.

## Does Mathlib already have it?

Partially. Mathlib has the full identity only under `[K.HasPullbacks]
[K.IsStableUnderBaseChange]` (`over_toGrothendieck_eq_toGrothendieck_comap_forget`,
Over.lean). The unconditional inequality
`comap_forget_toGrothendieck_le_over_toGrothendieck` and the precoverage-level
iff `mem_over_toPrecoverage_iff_comap_forget` are NOT in mathlib at the pin
(grepped `Sites/`), and the negative result (counterexample) is new.

## Review notes

* All external names GOLD-verified against the checkout at
  `EnidsMathMadness/.lake/packages/mathlib` (pin v4.35.0-rc3) before use:
  `Sieve.overEquiv`, `Sieve.generate_map_eq_functorPushforward`,
  `Sieve.functorPushforward_bot`, `Sieve.generate_bot`, `Sieve.pullback_bot`,
  `GrothendieckTopology.mem_over_iff`, `GrothendieckTopology.bot_covering`,
  `GrothendieckTopology.toPrecoverage` / `mem_toPrecoverage_iff`,
  `Precoverage.comap` / `mem_comap_iff` / `comap_monotone`,
  `Precoverage.Saturate` (constructors `of`/`top`/`pullback`/`transitive`),
  `Precoverage.toGrothendieck`, `mem_toGrothendieck_iff`,
  `generate_mem_toGrothendieck`, `toGrothendieck_bot`,
  `toGrothendieck_monotone`, `le_toPrecoverage_toGrothendieck`,
  `toGrothendieck_le_iff_le_toPrecoverage`, `Preorder.smallCategory`,
  `homOfLE`, `bot_ne_top`, `ite_eq_left`/`ite_eq_right` (non-deprecated
  names at this toolchain), `Set.mem_singleton_iff`, `Set.mem_empty_iff_false`.
* `lake build BoringMath.CategoryTheory.Sites.OverPrecoverage`:
  **warning-clean, zero sorries**. `scripts/check-style.sh` on the file:
  **0 violations**. File is 100-col clean.
* Tactic whitelist respected: no simp/rw/decide/etc.; rewriting done by
  fully-instantiated `Eq.subst` with explicit motives; `rfl` only in the
  primitive definitional peel `overEquiv_apply_eq_functorPushforward_forget`.
* The counterexample was found by attempting the direct `Saturate` induction
  for the `≤` direction without base-change: the `pullback` case is exactly
  where an arrow `Z ⟶ X` would be needed to lift the induction hypothesis to
  the over-category, and none exists in general.
