# Candidate PR: base change of commutative squares (TREE B.0)

Ticket: BoringMath issue #15 (TREE B.0). Branch: `pr/square-base-change`.
Module: `BoringMath/CategoryTheory/Limits/Shapes/Pullback/SquareBaseChange.lean`
(owner directory per `docs/OWNERSHIP.md`; see the ownership note below).

**Revision (2026-10-26, computability decree):** per the human referee's
standing rule ("keep everything computable rather than noncomputable"),
the module was redesigned on explicit pullback-cone data — see the
revision record at the end of this note.

## Statement

* `Square.baseChange` — the base change of a commutative square `sq`
  along `h : Y ⟶ sq.X₄`: the square over `Y` whose legs are the base
  changes of `sq.f₂₄` and `sq.f₃₄` along `h`, with corner the fiber
  product of the two new legs. Fully explicit construction,
  `noncomputable` (it uses the chosen pullback data).
* `Square.isPullback_baseChange` — the base change of any commutative
  square is a pullback square, *unconditionally* (the corner is the
  chosen fiber product by construction; the ticket's preservation clause
  — pullback squares are preserved — is the special case that consumes
  no hypothesis).
* `Square.baseChangeCompIso` — base change along `h₁ ≫ h₂` is base
  change along `h₂` then `h₁`, up to the canonical isomorphism of
  squares. Statement-only (sorry with peeling plan), per the sorry law.

## Clause (4) of the ticket: statability of the completeness predicate

The API makes the naive stability predicate statable as
`∀ ⦃sq : Square C⦄, sq ∈ D.squares → ∀ {Y : C} (h : Y ⟶ sq.X₄),
  sq.baseChange h ∈ D.squares`
— but Voevodsky's actual completeness condition weakens membership to
refinement, and is owned by ticket B.3 (#11), which consumes this API.
No predicate is declared in this module (avoiding a name/idiosyncrasy
that B.3 would then have to supersede).

## Ownership decision (OWNERSHIP.md rule 3)

The ticket's acceptance named the `CategoryTheory/Sites` owner
directory; GOLD evidence places the owner elsewhere:
`Square.IsPullback`, `Square.pullbackCone`, `Square.IsPushout` live in
`Mathlib/CategoryTheory/Limits/Shapes/Pullback/Square.lean` at the pin,
so a Square base-change API would land there — the module is placed in
the `Limits/Shapes/Pullback/` mirror. The decision and evidence are
recorded here per `docs/OWNERSHIP.md` rule 3.

## Literature

* V. Voevodsky, *cd-structures*, unpublished notes (2010) — the
  motivating consumer (completeness = stability under base change).
  `REVIEW(citation)`: sections unpinned.
* The construction is elementary base change; no Mac Lane lemma was
  needed (none used).

## Does Mathlib already have it?

Checked at the pin and upstream (search hygiene, 2026-10-25):
`Square.baseChange`-style API absent at the pin (`Square.lean` and
`Limits/Shapes/Pullback/Square.lean` read); upstream open-PR search
finds the "Categorical pullback squares" series (mathlib4 #27214,
#27391) — that is the **2-categorical** layer (`CatCommSq`,
`CatPullbackSquare`), not object-level base change of `Square C`; no
collision. `Square.pullback`-style names: 0 in-flight hits.

## Review notes

* Naming: `baseChange` rather than `pullback` — inside `namespace
  Square` the latter would shadow `Limits.pullback` in the definition's
  own body; `baseChange` also matches the schemes-layer terminology of
  the B.2 consumer.
* Elaboration notes (pin-specific, ledger items): `pullback.fst` /
  `pullback.snd` / `pullback.condition` take `f g` **explicitly** at
  this revision (named arguments used throughout);
  `Square.IsPullback.mk` needs its implicit `sq` supplied by name before
  its argument elaborates; `pullbackIsPullback` is the cone-limit
  witness (`IsLimit`), and our square's attached pullback cone is
  definitionally that cone.
* `baseChangeCompIso` peeling plan names `pullbackPullbackRightIsPullback`
  (Assoc.lean:127) and `pullbackAssoc` (Assoc.lean:143) as the
  associativity inputs; the Square Hom/iso assembly API still needs a
  pin-read when that proof is instantiated.

## Verification

* `lake build`: warning-clean except the module's single deliberate
  sorry (statement-only, per the sorry law).
* `scripts/check-style.sh`: 0 violations.

## Revision record (2026-10-26, computability decree)

Per the human referee's standing rule — keep everything computable
rather than noncomputable — the module was redesigned; codified as
STYLE §2.3 (computability discipline) in the same PR.

- `Square.baseChange` now takes its pullback data **explicitly** (three
  `PullbackCone` parameters: the two base-changed legs and the corner
  cone) instead of `[HasPullbacks C]` instance-chosen data. The
  construction is **computable** — the previous design depended on
  `Limits.pullback` (`Classical.choice`-backed) and was `noncomputable`.
  Callers holding a `HasPullbacks C` instance obtain cone data at their
  own call sites; the library bakes no choice in.
- `Square.isPullback_baseChange` restated on the data-explicit form:
  the corner cone's limit witness is now a hypothesis; the proof is a
  single direct term (`⟨⟨c₁.condition⟩, ⟨IsLimit.ofIsoLimit hc₁
  (PullbackCone.eta c₁)⟩⟩` — `Limits/IsLimit.lean:181`,
  `PullbackCone.lean:162`), linear, no tactics.
- `Square.baseChangeCompIso` (the statement-only composition law) is
  **retired with this revision**: its statement was phrased against the
  instance-chosen design. The data-explicit composition law is the
  cone-pasting law, which belongs with B.3's saturation work where it
  is consumed; re-scoped there (obstruction honestly recorded here, not
  silently dropped).

Protocol note: this is a revision (not supersession) of a landed module
under a direct human decree; no downstream consumers existed; recorded
as a protocol exception with the decree as authority.
