# Candidate PR: K₀ of an abelian category (TREE K.0, statement layer)

Ticket: BoringMath issue #31 (TREE K.0 [mathlib], statement-layer).
Branch: `feat/formal-periods-axiom-lint` (work order executed here; content is
purely additive: one new module + this note).
Module: `BoringMath/CategoryTheory/Abelian/GrothendieckGroup.lean`
(would live upstream in `Mathlib/CategoryTheory/Abelian/`, next to
`GrothendieckCategory/`).

## Statement

For an abelian category `A` (all binders explicit; SES witnesses bundled, not
existential, per STYLE §2.3):

* `CategoryTheory.K0.ShortExactSequence A` — a bundled short exact sequence
  `0 → X₁ → X₂ → X₃ → 0`: a `ShortComplex A` together with a
  `ShortComplex.ShortExact` proof (exact, `f` mono, `g` epi).
* `K0.sesRel ses` — the relation element `[X₂] - [X₁] - [X₃]` in the free
  abelian group `FreeAbelianGroup (Quotient (isIsomorphicSetoid A))` on
  isomorphism classes (mathlib's own `isIsomorphicSetoid`).
* `K0.sesRelations` — the `AddSubgroup` closure of `Set.range sesRel`.
* `CategoryTheory.K0 A` — the Grothendieck group: the quotient
  `FreeAbelianGroup (Quotient (isIsomorphicSetoid A)) ⧸ sesRelations`
  (an `abbrev`, so the `AddCommGroup` instance of the quotient applies).
* `K0.of : A → K0 A` — the class map.
* `K0.of_eq_of_iso` — the class map is constant on isomorphism classes.
* `K0.of_shortExact` — **additivity on short exact sequences**:
  `of ses.sc.X₂ = of ses.sc.X₁ + of ses.sc.X₃` (honest proof via
  `QuotientAddGroup.mk'_eq_mk'` and the group identity `add_neg_sub_sub_eq`).
* Functoriality: `K0.isoClassesMap`, `K0.isoClassesMap_mk`, `K0.freeAbelianMap`,
  `K0.toK0`, `K0.toK0_of`, `K0.toK0_sesRel`, `K0.map`, `K0.map_of` — an exact
  functor `F : A ⥤ B` (hypotheses `[F.PreservesZeroMorphisms]` and
  `hF : ∀ S : ShortComplex A, S.ShortExact → (S.map F).ShortExact`, the shape
  mathlib itself uses in `ShortComplex/ExactFunctor.lean`) induces
  `K0.map F hF : K0 A →+ K0 B` with `map F hF (of X) = of (F.obj X)`.
* Universal property: `K0.AdditiveInvariant A G` (a function `A → G` constant
  on isomorphism classes and additive on short exact sequences),
  `AdditiveInvariant.toIsoClasses`, `.toIsoClasses_mk`, `.toFreeAbelian`,
  `.toFreeAbelian_sesRel`, `.lift : K0 A →+ G`, `.lift_of`,
  `AdditiveInvariant.ofHom`, `K0.hom_ext_freeAbelian`, and
  `K0.liftEquiv G : (K0 A →+ G) ≃ {f : A → G // iso-invariant ∧ ses-additive}`
  — the universal property as an `AddMonoidHom`-equiv (stated on the subtype
  of functions rather than on the `AdditiveInvariant` structure, so that
  `right_inv` is `Subtype.ext` + `funext` and no structure-eta `rfl` is needed).

All proofs are honest (no `sorry`): `lake build
BoringMath.CategoryTheory.Abelian.GrothendieckGroup` is warning-clean and
`sorry`-free; `scripts/check-style.sh` reports 0 violations, 0 sorries.

## Design decisions (per the ticket's prep questions)

* **Abelian, not exact, as the substrate** — as the ticket prescribes: mathlib
  has no exact-category typeclass at the pin, while `Abelian A`,
  `ShortComplex.Exact`/`ShortExact` are mature. Extension to exact categories
  is future node K.1.
* **Relations on the free abelian group**, as the task statement specifies:
  `K0 A` is the quotient of the free abelian group on isomorphism classes by
  `[X₂] - [X₁] - [X₃]` (not the two-step monoid-Grothendieck-group-then-quotient
  route). In an abelian category the split relations are instances of the SES
  relations, so the biproduct additivity is subsumed; the "biproduct descends"
  hard bit of the issue's route (i) does not arise in this shape.
* **SES data explicit** (bundled `ShortExactSequence`), per STYLE §2.3 and the
  enrichment note; the quotient is a named `AddSubgroup` closure, per mathlib's
  `FreeAbelianGroup`/quotient idioms at the pin.
* **`K0` is an `abbrev`** (like `Algebra.GrothendieckGroup`) so quotient
  instances (`AddCommGroup`) flow through.
* The exact-functor hypothesis is stated as `hF : ∀ S, S.ShortExact →
  (S.map F).ShortExact` plus `[F.PreservesZeroMorphisms]` (needed for
  `S.map F`); this matches the hypothesis shape mathlib uses in
  `Mathlib/Algebra/Homology/ShortComplex/ExactFunctor.lean`.

## Does Mathlib already have it? (GOLD, at pin v4.35.0-rc3)

**No.** Grepped the checkout at
`EnidsMathMadness/.lake/packages/mathlib` (rev `v4.35.0-rc3`):

* `GrothendieckGroup` occurs only in
  `GroupTheory/MonoidLocalization/GrothendieckGroup.lean` (plus uses in
  `AffineMonoid/Embedding.lean`, `MonoidLocalization/Finite.lean`) — all the
  **commutative-monoid** `Algebra.GrothendieckGroup M := Localization
  (⊤ : Submonoid M)`. Its own docstring flags exactly the gap this ticket
  closes, verbatim: "Note that 'Grothendieck group' also refers to the
  analogous construction in an abelian category obtained by formally making
  the last term of each short exact sequence invertible."
* No `KTheory`/`K-theory` directory exists; `K0`/`K_0` greps hit only
  unrelated algebra files. The "Grothendieck" hits in
  `Algebra/Category/{Grp,ModuleCat}/AB.lean` are `IsGrothendieckAbelian`
  (Grothendieck's AB axioms), unrelated.
* Substrate used and present at the pin: `CategoryTheory.isIsomorphicSetoid`
  (`CategoryTheory/IsomorphismClasses.lean`), `ShortComplex` / `ShortExact` /
  `ShortComplex.map` (`Algebra/Homology/ShortComplex/*`), `Abelian`
  (`CategoryTheory/Abelian/Basic.lean`), `FreeAbelianGroup` (`of`, `lift`,
  `map`, `lift_apply_of`, `map_of_apply`, `induction_on`;
  `GroupTheory/FreeAbelianGroup.lean`), `QuotientAddGroup` (`mk'`, `lift`,
  `lift_mk'`, `mk'_eq_mk'`, `mk'_apply`, `addMonoidHom_ext`;
  `GroupTheory/QuotientGroup/Defs.lean`), `AddSubgroup.closure/subset_closure/
  closure_le` (`Algebra/Group/Subgroup/Lattice.lean`).

## Literature

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, GSM 145,
  Amer. Math. Soc., 2013 — **Chapter II, "The Grothendieck group K₀"** (verified
  online: sites.math.rutgers.edu/~weibel/Kbook/Kbook.II.pdf; the book's
  introduction states that the exact-sequence-relations version of K₀ "is used
  for abelian categories as well as exact categories"). Covers the definition,
  functoriality, and the universal property. REVIEW(citation): pin the exact
  section number within Ch. II (routed to W5, issue #13).
* SGA 6, Exposé I (origins of the Grothendieck group). REVIEW(citation): pin
  the exposé (routed to W5, issue #13).
* In-tree substrate file `Mathlib/GroupTheory/MonoidLocalization/
  GrothendieckGroup.lean` (primary for the monoid-side vocabulary; its
  docstring TODO is the line this ticket closes).

## Review notes

* 0 sorries; every declaration carries `-- Reference:` + docstring; explicit
  binders throughout; tactic whitelist respected (`have`/`refine`/`exact`/
  `obtain`/`induction ... with` only; no `rw`/`show` — defeq unfoldings are
  done by `exact` against the expected type); ≤ 100 columns; copyright header
  from `Foundations/Eta.lean`.
* `lake build BoringMath.CategoryTheory.Abelian.GrothendieckGroup`: success,
  warning-clean (1051 jobs). `scripts/check-style.sh <file>`: 0 violations,
  0 sorries.
* Open question for the referee: the universal property is stated for plain
  functions `A → G` additive on SESs (equivalently, additive functors into
  `AddCommGrpCat` restricted to objects); a formulation via
  `A ⥤ AddCommGrpCat` + `AdditiveFunctor` would need an `Additive` instance
  argument and was left out of the statement layer.
