# Candidate PR: binary Zariski open covers are Mayer–Vietoris squares (`pr/sites-zariski-mayer-vietoris`)

Ticket: GitHub issue #35 (TREE B.6). Depends on B.1 (landed:
`BoringMath/CategoryTheory/Sites/CdStructure.lean`).

## Statement

One new module `BoringMath/CategoryTheory/Sites/ZariskiMayerVietoris.lean`
(plus this note). For `X : Scheme.{u}` and `U V : X.Opens` with
`U ⊔ V = ⊤`:

* **Clause (i), big site, proved.** `Scheme.openCoverSquare X U V :
  Square Scheme.{u}` — the square `U ×[X] V ⟶ U`, `U ×[X] V ⟶ V`,
  `U.ι`, `V.ι` packaged as data in `Scheme` (noncomputable: `Limits.pullback`
  in `Scheme` is choice-backed, flagged in the docstring).
  Peels: `Scheme.openCoverSquare_isPullback`
  (`Square.IsPullback.mk (pullbackIsPullback U.ι V.ι)`).
  Coverage: `Scheme.binaryOpenCover X U V hUV : Cover (precoverage
  IsOpenImmersion) X` (`Cover.mkOfCovers` over `WalkingPair`) and
  `Scheme.sieve_ofTwoArrows_mem_zariskiTopology_of_sup_eq_top`:
  `Sieve.ofTwoArrows U.ι V.ι ∈ Scheme.zariskiTopology X`
  (via `Cover.mem_grothendieckTopology`; `zariskiTopology` is the abbrev
  `grothendieckTopology IsOpenImmersion`).
* **Clause (ii), small site, proved.** `Scheme.smallZariskiTopology X :=
  Opens.grothendieckTopology X` (the small Zariski site `X.Opens`);
  `Scheme.openCoverSquareOpens U V : Square X.Opens` (corners
  `U ⊓ V, U, V, U ⊔ V`); `Scheme.exists_mayerVietorisSquare_of_openCover`
  (via Riou's `Opens.mayerVietorisSquare'`, i.e.
  `MayerVietorisSquare.mk_of_isPullback`: pullback + covering two-arrow
  sieve); `Scheme.zariskiCdStructure X : CdStructure X.Opens`
  (distinguished squares = open-cover squares with `U ⊔ V = ⊤`) and
  `Scheme.zariskiCdStructure_isMayerVietoris`:
  `(zariskiCdStructure X).IsMayerVietoris (smallZariskiTopology X)`.
  Bridge corollary (B.1):
  `Scheme.exists_mayerVietorisSquare_and_sheafCondition_of_mem_zariskiCdStructure`
  — every sheaf of types on the small Zariski site satisfies
  `MayerVietorisSquare.SheafCondition` on every binary open-cover square
  (this is where the landed `sheafCondition_of_sheaf` is consumed).
* **Clause (iii), proved, zero new content.**
  `Scheme.mayerVietoris_sequence_exact`: for `S : (smallZariskiTopology
  X).MayerVietorisSquare`, `F : Sheaf _ AddCommGrpCat.{u}`, the sequence
  `S.sequence F n₀ n₁ h` is exact — literally the in-tree
  `MayerVietorisSquare.sequence_exact` from
  `Mathlib/CategoryTheory/Sites/SheafCohomology/MayerVietoris.lean`
  (`toBiprod`/`fromBiprod`/`δ`/`sequence`), with the same `[HasExt.{w}]`
  binder that module itself assumes.
* **Clause (iv), not stated — obstruction, see below.**

## Literature

* J. Riou, `Mathlib.CategoryTheory.Sites.MayerVietorisSquare.lean`,
  `Mathlib.Topology.Sheaves.MayerVietoris.lean`,
  `Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris.lean` —
  primary, in-tree, read in full at the pin.
* Stacks Project, tag 08GL (elementary distinguished squares /
  Mayer–Vietoris squares; Cohomology of Algebraic Spaces, §75.9,
  Definition 75.9.1) — verified against the live tag page.
* R. Hartshorne, *Algebraic Geometry*, Springer GTM 52, 1977, Chapter II,
  §1 (sheaves on a topological space; gluing axiom, p. 61).
  `REVIEW(citation)` tag kept on the MV-sequence decl for the exact
  Hartshorne section (II.1/III.2) per the ticket.
* V. Voevodsky, *cd-structures*, unpublished notes (2010), §1 — Zariski
  cd-structure as the trivial case of the Nisnevich one;
  `REVIEW(citation)` tag as in the landed `CdStructure.lean`.

## Where it would live in Mathlib

Mathlib-owned territory (mirrors the upstream tree): the small-site parts
next to `Mathlib/Topology/Sheaves/MayerVietoris.lean` and Riou's
`Mathlib/CategoryTheory/Sites/MayerVietorisSquare.lean`; the big-site
coverage lemma (`sieve_ofTwoArrows_mem_zariskiTopology_of_sup_eq_top`) in
`Mathlib/AlgebraicGeometry/Sites/BigZariski.lean` territory. Our module sits
in `BoringMath/CategoryTheory/Sites/` next to the landed B.1 module it
builds on.

## Does Mathlib already have it?

Partially. For a plain topological space, **yes**: Riou's
`Opens.mayerVietorisSquare U V : (Opens.grothendieckTopology T)
.MayerVietorisSquare` (`Mathlib/Topology/Sheaves/MayerVietoris.lean`)
already constructs the MV square of two opens of `T`. What is **absent** at
the pin: (a) the scheme-level statement that a binary open cover sieve
`Sieve.ofTwoArrows U.ι V.ι` covers in `Scheme.zariskiTopology` (our
`binaryOpenCover` + sieve lemma); (b) the cd-structure packaging
(`CdStructure` + `IsMayerVietoris`) of these squares on the small Zariski
site of a scheme, with the B.1 bridge to `sheafCondition_of_sheaf`.

## Review notes

* Compiled at pin v4.35.0-rc3 with `lake env lean
  BoringMath/CategoryTheory/Sites/ZariskiMayerVietoris.lean`: exit 0,
  warning-clean (mathlibStandardSet linter on). `lake build` not run per
  ticket instructions. `scripts/check-style.sh` on the file: 0 violations,
  0 sorries (the single RESTRICTED `rw [hUV]` carries its inline
  uniqueness/instantiation comment per STYLE §2.1).
* **No sorries; no peeling plans needed.** Every lemma is a one-line term
  proof over GOLD-verified in-tree names: `Square`, `Square.IsPullback.mk`,
  `Limits.pullbackIsPullback`, `Scheme.Opens.ι` (`IsOpenImmersion` instance,
  `Scheme.Opens.ι_apply`, `Scheme.Opens.opensRange_ι`), `Scheme.Cover.mkOfCovers`,
  `Scheme.Cover.mem_grothendieckTopology`, `Scheme.zariskiTopology`
  (abbrev `grothendieckTopology IsOpenImmersion`), `Opens.grothendieckTopology`,
  `Opens.mayerVietorisSquare'` (+ `_toSquare`), `CdStructure.IsMayerVietoris`,
  `CdStructure.exists_mayerVietorisSquare_and_sheafCondition`,
  `MayerVietorisSquare.sequence`/`sequence_exact`, `HasWeakSheafify`/
  `HasSheafify` on `X.Opens` (both synthesize at `Type u` / `AddCommGrpCat.{u}`).
* **Universe obstruction on the big site (recorded honestly).**
  `GrothendieckTopology.MayerVietorisSquare J` requires
  `HasWeakSheafify J (Type v)` with `v` the morphism universe of the site.
  `Scheme.{u}` has `Category.{u}`, and at the pin only
  `HasWeakSheafify Scheme.zariskiTopology (Type (u+1))` synthesizes —
  `Type u` fails (covering sieves on the big site are not `u`-small), so the
  `MayerVietorisSquare` structure is **not formable** on `Scheme` at the
  pin. Hence clause (ii) is proved on the `u`-small site `X.Opens` (which is
  also the site clause (iii) names: "the small Zariski site"), while the
  big-site deliverable is clause (i) (square as data, pullback, and the
  covering two-arrow sieve in `Scheme.zariskiTopology`).
* **Clause (iv) not stated — two obstructions.** (a) Formability: as above,
  no `MayerVietorisSquare` on the big `Scheme` site at the pin, and on the
  small site `X.Opens` a closed subscheme `Z` is not an object, so the
  elementary distinguished square cannot even be packaged there. (b)
  Mathematics: the closed-complement square is *not* Mayer–Vietoris for the
  Zariski topology where it is formable — e.g. `X = A¹_k`, `Z = {0}`,
  `U = X ∖ Z`, `F = 𝒪_X`: `F(X) = k[x]` but `F(U) × F(Z) = k[x,x⁻¹] × k`,
  so the sheaf-condition pullback fails. The elementary distinguished
  square is MV for the **Nisnevich** topology — that is B.4 (#26), not this
  ticket. Stating a false proposition (even sorried) would violate the
  sorry law, so the clause is recorded here instead.
* Depth register (per the ticket's 2026-10-26 correction): DEPTH 0 clause
  (i) (square-as-data bookkeeping on the in-tree pullback API + the
  pretopology cover), DEPTH 1 clause (ii) (small-site MV via the in-tree
  constructor + B.1 bridge), DEPTH 1 clause (iii) (pure instantiation).

## Open questions for the human

1. Clause (iv): confirm it should stay out of the Zariski module (obstruction
   (b) above) and remain gated to B.4 (#26, Nisnevich).
2. The ticket asks for the square "packaged as a `CommSq` in `Scheme`"; we
   do that (clause (i)) but prove `IsMayerVietoris` on the small site
   `X.Opens` due to obstruction (a). If upstream ever provides
   `HasWeakSheafify Scheme.zariskiTopology (Type u)`, a big-site MV-square
   statement becomes formable and should be added as a new module
   (supersession, not revision).
3. `HasExt` for clause (iii) is taken as an explicit binder exactly as the
   in-tree `SheafCohomology/MayerVietoris.lean` does (`HasExt.standard`
   provides it for sheaves of abelian groups, but instance search times out
   at the default heartbeat budget, so we did not add a local instance).
