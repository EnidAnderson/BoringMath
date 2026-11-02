# CFSG roadmap — the classification of finite simple groups, as a ticket tree

Tracking ticket: **#214**. Master statement: `BoringMath.GroupTheory.Simple.Classification.classification_of_finite_simple_groups`
(currently a `sorry` with peeling plan, per STYLE §7). End-state (absolute): the
master theorem proved sorry-free in BoringMath.

Reading rule: each text below is close-read **in full, in chunks**, as its tickets
are worked; the PREP tickets produce the chapter-level sub-ticket tree. Nothing is
formalized from summaries.

## Reference texts and their status (refs live in `../refs/`, outside the repo)

| Text | Role | PDF status (files in `../refs/`) |
|---|---|---|
| Feit–Thompson, *Solvability of groups of odd order*, Pacific J. Math 13(3) (1963), 775–1029 | odd-order theorem (FT.0, #226) | **obtained** (open access, msp.org): `feit-thompson-1963-pjm-v13-n3-p01..p07.pdf` |
| Deligne–Lusztig, *Representations of reductive groups over finite fields*, Ann. Math. 103 (1976), 103–161 | character theory of G(F_q) (#218, #224) | **obtained** (author-hosted): `deligne-lusztig-1976-representations-reductive-groups.pdf` |
| GLS series, AMS Surveys 40: Numbers 1–6 (1994, 1996, 1998, 1999, 2002, 2005) of the projected 11-volume second-generation proof; with Aschbacher–Smith, *The Classification of Quasithin Groups* I–II (Surv 111, 2004) and Aschbacher–Lyons–Smith–Solomon Number 9 (2011), Number 10 (2022) | the proof roadmap + the reduction machinery (#219–#221) | **vol 1 endmatter/TOC obtained**: `gls-vol1-endmatter-ams-surv-40.1.pdf`; archive.org item `classificationof0000gore` is borrow-only (no unrestricted PDF found; inside-search needs a borrow session). Full text of Numbers 1–6 still needed from user (AMS purchase / archive.org borrow). Supplementary open notes obtained: `lyons-math555-notes.pdf` (Rutgers), `etsu-finite-simple-groups-notes.pdf` |
| ATLAS, Conway–Curtis–Norton–Parker–Wilson, OUP 1985 | sporadic data (#216, #222, #232, #233) | **obtained** (CNRS-hosted copy, user-supplied link): `atlas-of-finite-groups-1985.pdf` |
| Carter, *Simple Groups of Lie Type*, Wiley 1972 | Chevalley construction (#218, #223) | **tables obtained** (Utah math-library, user-supplied link): `carter-simple-groups-of-lie-type-tables.pdf`; full text still needed from user |
| Wilson, *The Finite Simple Groups*, Springer GTM 251 (2009) | graduate proofs, A_n and PSL via Iwasawa | **obtained** (user-supplied link): `wilson-gtm251-finite-simple-groups.pdf` |

mathlib pin v4.35.0-rc3 is the base layer (already has: `IsSimpleGroup`, A_n
simplicity, `PSL`, SL card formulas, Iwasawa criterion, Lie algebras/modules/
weights/root systems).

## Alternate / primary sources (the proof is NOT only in GLS)

GLS (Surveys 40, Numbers 1–6 of a projected 11) is the *second-generation rewrite*,
which stalled; the primary record is the original literature (~10–15k journal pages,
hundreds of authors). Parts are reproduced elsewhere:

- **Strategy/overview**: Gorenstein, *Classifying the finite simple groups*, Bull. AMS 14 (1982) 1–75; Gorenstein, *Finite Simple Groups: An Introduction to Their Classification* (1982 Harvard lecture notes; the "16-step program").
- **Characteristic-2 local analysis** (GLS vols 2–5 content): Gorenstein–Lyons, *The Local Structure of Finite Groups of Characteristic 2 Type*, AMS Memoir 42.276 (1983) — K-groups, trichotomy; and **Aschbacher, *The Classification of Finite Simple Groups: Groups of Characteristic 2 Type*, 2 vols, CUP 2011** — the modern replacement account.
- **Quasithin case**: Aschbacher–Smith, Surveys 111 (2004), 2 vols.
- **Minimal simple / N-groups**: Thompson's N-group papers (1968–71); Bender–Glauberman simplifications of odd-order/local analysis.
- **Lie type**: Steinberg, *Lectures on Chevalley Groups* (1967); Steinberg, *Endomorphisms of linear algebraic groups* (1968); Lusztig, *Characters of Reductive Groups over a Finite Field* (1984); Kleidman–Liebeck, *The Subgroup Structure of the Finite Classical Groups* (1990); + Carter/DL/Wilson/ATLAS (in refs).
- **Sporadic**: ATLAS (in refs) + original construction papers (Griess, *The Friendly Giant*, Invent. Math. 69 (1982) for the Monster; Fischer; Harada–Norton; …).
- **Odd order**: Feit–Thompson 1963 (in refs) + later simplifications.

Ticket **#234 CFSG.SRC** tracks obtaining the alternates. For formalization, the
reduction phase (Phase 1) will cite the original papers / Aschbacher 2011 wherever
GLS is unavailable; Phases 2–3 are covered by the refs we already hold.

## Sourcing & reconstruction policy (agreed with the human)

The end product is a single democratized Lean resource: anyone can explore the
proof details in Lean without buying books or hunting papers. Therefore:

* The **kernel-checked Lean proof is the authority**. Citations name and roadmap;
  they never license a step. Where a source is paywalled/inaccessible, we
  **reconstruct the argument from first principles in Lean** (the type checker
  is the guardrail — same safety argument as the rest of the repo).
* We cite only freely available sources (held in `../refs/`); paywalled
  originals are never cited directly — statements from them are verified via
  held secondary sources and flagged `REVIEW(citation)`.
* Demonstrated: `not_isSimpleGroup_alternatingGroup_fin4` in
  `BoringMath/GroupTheory/Simple/Classification.lean` — the A₄/PSL(2,3)
  exception reconstructed purely from pin lemmas, no external text.

## The CFSG library (`BoringMath/GroupTheory/CFSG/`, ticket #236 CFSG.LIB)

Special machinery beyond mathlib's pin (audited: pin HAS `Group.IsPerfect`, focal
subgroup/transfer, Frattini, class equation, Sylow/p-groups, Coxeter, Jordan and
multiple primitivity, characters; MISSING quasisimple, signalizers, J(P), K-groups,
fusion systems, BN-pairs, local analysis, blocks):

- `Quasisimple.lean` — landed: `IsQuasisimpleGroup`, `IsPerfect.of_surjective`
  (proved), `alternatingGroup_isPerfect` (consumed), center-quotient lemma.
- `Signalizer.lean` — landed: `SignalizerFunctor` structure (θ ≤ C_G(P),
  nontrivial, conjugation-invariant, complete). Next: balance theorem (#227).
- `ThompsonSubgroup.lean` — landed: `IsMaximalAbelian`, `thompsonSubgroup J(P)`,
  `thompsonSubgroup_le` (proved). Next: J(P) characteristic, Thompson factorization (#228).
- `Fusion.lean` — landed: `IsConjHom` + `IsConjHom.injective` (proved). Next: the
  fusion system of G on a Sylow p-subgroup, saturation, Alperin (#240).
- `ThreeTransposition.lean` — landed: `ThreeTranspositionGroup` +
  `orderOf_eq_two` (proved). Next: Fischer's classification (#245).
- `AlmostSimple.lean` — landed: `IsAlmostSimpleGroup` + `nontrivial` (proved).
  Next: socle/layer theory, Aut/Out, Schreier (#244).
- `PCore.lean` — landed: `oCore O_p(G)`, `oCore_normal`, `le_oCore`, and
  `oCore_isPGroup` (all proved, sorry-free; via `IsPGroup.of_normal_quotient` +
  `IsPGroup.sup_of_normal` + directed join). Next: `O_p` functoriality,
  `O_{p'}` disjointness (#241 remainder).
- Planned modules (each its own ticket, absolute end-states):
  - reduction core: signalizer #237, Thompson J #238, K-groups/trichotomy #239,
    fusion systems/Alperin #240, local analysis #241, factorizations #242,
    recognition (N-groups, Z*, Bender–Suzuki, Gorenstein–Walter) #243,
    almost-simple/layers/Schreier #244, 3-transpositions #245, quasithin #246,
    characteristic-2 #247, cohomology H¹/H² #248, blocks/Brauer #249,
    permutation actions/Jordan #250
  - Lie type: BN-pairs/buildings/Tits #251, Chevalley #252, reductive+DL #253,
    classical groups/subgroup structure #254
  - sporadic: constructions library #255; small groups/exceptional isos #256
  - assembly glue #257

## The motivic consumer (#260) — how CFSG gets consumed

Simple pure motives over k correspond (under the Tate/Hodge conjectures, stated
as labeled hypotheses) to irreducible ℓ-adic Galois representations ρ: G_k →
GL(V); the motive is simple iff ρ is irreducible, and the image of ρ has a
**simple socle S** — which by CFSG is one of the classified types. So
*simple motives ↔ (S in the CFSG list) + (irreducible rep datum of the
almost-simple group with socle S)* — the motivic mirror of CFSG's own
almost-simple reduction (#244). Artin motives (weight 0) are the finite
Galois-extension case: simple Artin motives ↔ irreducible characters of finite
Galois groups. The pro-unipotent/Lie part of the motivic Galois group
(MTM(ℤ), free Lie algebra on odd generators) is the Lie side (#218, #252,
#253) where CFSG does not enter. ∞-groupoid version: #259. Motivic-side
library tickets: #261 Tannakian/motivic Galois, #262 ℓ-adic reps + socle
reduction, #263 Artin motives, #264 realizations, #265 MTM/MZV, #266 purity.

## The lifted (motivic) library map (#267 CFSG.MOT.LIB, under #260)

Motivic analogs of the CFSG tools, filed as #268–#275. The "?" rows of the naive
dictionary resolve (see #267 comment) as: Sylow/p-local → decomposition &
inertia groups at places of k, local Galois representations (Weil–Deligne, wild
inertia), p-adic Hodge at the residue char (#270, #272); fusion systems →
class field theory / Chebotarev as the fusion theorem of G_k, via decomposition
groups at places above p (#272); signalizers → pro-p signalizers on the
pro-algebraic motivic Galois group, balance = free pro-p structure of the MTM
Lie algebra (#271); BN-pairs/buildings → Bruhat–Tits buildings of local Galois
groups and the Fargues–Fontaine curve / period domains (#270); sporadic groups →
Artin motives with sporadic Galois image (moonshine motive from the Monster's
196883-dim rep), not sporadic motives (#272, #274); alternating → generic
monodromy S_n/A_n of families (Hilbert irreducibility analog) (#272/#273);
characters/blocks → the four realizations + comparisons (#269); Lie type →
pro-unipotent MTM(ℤ) sector (#271/#265); CFSG → simple-mixed-motives
classification (#266); ∞-version → simple objects of DM (#275).

## The gameplay lift (#276 CFSG.GAMES.0, under the games-motives dictionary)

Simple groups as irreducible forms of choice/decision: a face-down card /
hidden token is a game position with an irreducible hidden choice
(`faceDown`, landed in BoringLab.Games.Hidden); alternating play is the game
structure; linear logic / ludics alternation (designs, daimon) is the
proof-as-play structure; the referee's conventions (Games.Referee) are the
symmetry group of the play. Dictionary rows filed: #277 alternating play ↔ A_n,
#278 face-down ↔ sporadic (26 irreducible hidden-choice types), #279 ludics/
referee ↔ motivic Galois (T2 bet). Each row proved or bet-labeled.

## Ticket tree (TOC of the proof, in formalization order)

### Phase 0 — foundations
- **#226 FT.0** — Feit–Thompson odd-order theorem (own program; refs obtained). Not in mathlib.
- (mathlib covers: Sylow, solvable groups, Hall; Burnside p^a q^b to be audited.)

### Phase 1 — the reduction (GLS vols 1–2)
- **#219 PREP** close-read GLS vol 1 ch 1–2 → sub-tickets.
- **#220 PREP** close-read GLS vol 2 (local analysis) → sub-tickets.
- **#227 CFSG.R.1** signalizer functors + balance theorem.
- **#228 CFSG.R.2** Thompson factorization + characteristic-p case.
- **#229 CFSG.R.3** N-group analysis: simple N-group ⇒ Lie type or sporadic.
- **#217 CFSG.R** master reduction (closes when R.1–R.3 land).

### Phase 2 — Lie type (GLS vol 3 + Carter + DL)
- **#221 PREP** GLS vol 3; **#223 PREP** Carter ch 1–6; **#224 PREP** DL 1976.
- **#215 CFSG.C** sector tracking; **#229->#230 CFSG.C.1** `PSL_isSimpleGroup` sorry-free
  (Iwasawa; sub-lemmas: SL perfect, projective action quasiprimitive, faithful mod center).
  STATUS: rank `n >= 3` LANDED sorry-free -- `SL_isPerfect` (SLPerfect.lean) via
  `transvection_mem_commutator_of_card_three` (SLTransvection.lean) +
  `hOf_eq_diag2n` / `diag2n_mem_commutator_of_card_three` (SLDiag.lean; torus identity
  `h_ij(u) = diag2n(i,j,u)` proved via basis-vector action), then
  `PSL_isSimpleGroup_rank_ge_three` (PSLSimpleRank.lean; Iwasawa structure on
  `PSL(i, F)` acting on the projective space, all general-i pin lemmas); finite-field
  corollaries `PSL_isSimpleGroup_galoisField_of_three_le` and
  `PSL_isSimpleGroup_zmod_of_three_le` (PSLSimple.lean). Rank `n = 2` consumed at the
  pin (`rank_two_simple`, PSLSimple.lean). REMAINING: wire into
  `Classification.PSL_isSimpleGroup` -- NOTE its statement needs `2 <= n`
  (`PSL(1,q)` is trivial, hence not simple; flag for review); the `(2,2)`, `(2,3)`
  exceptions are non-simple by order (Classification / OrderTwelve / SmallOrders);
  **#231 CFSG.C.2** the other 15 families.
- **#218 CFSG.BRIDGE** Chevalley ℤ-forms + Deligne–Lusztig + motivic dictionary row (bet).
- Code so far: `BoringMath/GroupTheory/Simple/Classification.lean` (sectors A/B consumed,
  PSL cardinality proved), `BoringMath/GroupTheory/Simple/LieAlgebraBridge.lean`
  (lieAlgA/B/C/D; `dim sl(n,K) = n²−1` proved).

### Phase 2 quick wins — small-order non-simplicity + PSL small orders (#280–#284)
- **#280 CFSG.SMALL** small-order census: no finite simple group of composite
  order `< 60` (smallest nonabelian simple is `A_5`, order 60). Sub-tickets:
  - **#280a** order `p * q`, primes `p < q` — Sylow `q` unique
    (`card_sylow_modEq_one` + `card_dvd_index`) — LANDED:
    `not_isSimpleGroup_of_card_eq_prime_mul_prime` in
    `BoringMath/GroupTheory/Simple/SmallOrders.lean`.
  - **#280b** order `p ^ 2` — `IsPGroup.isMulCommutative_of_card_eq_prime_sq` +
    Cauchy — LANDED: `not_isSimpleGroup_of_card_eq_prime_sq` (same file).
  - **#280c** order 12 (the `PSL(2,3) ≅ A_4` level) — sorry with peeling plan in
    `SmallOrders.lean`: `n_3 ∈ {1,4}`; if 4, conjugation on `Sylow 3 G` gives
    `φ : G →* Perm (Sylow 3 G)`, transitive image with `4 ∣ |im| ∣ 12`, so
    `|im| ∈ {4,12}`; `|im| = 4` → `ker φ` of order 3; `|im| = 12` → `G` embeds
    as an order-12 subgroup of `S_4`, i.e. `A_4` (census:
    `BoringMath/Symmetry/S4Census.lean`), pull back `kleinFour`.
  - **#280d** full census of composite orders `< 60` by per-order Sylow tables
    (12, 18, 20, 24, 28, 30, 36, 40, 42, 44, 45, 48, 50, 52, 54, 56, 58);
    general tool: Burnside `p^a q^b` (**#280e**, not in mathlib at the pin).
    LANDED so far: all prime powers `p^a`, `a ≥ 2` (pin's `IsPGroup.isSimpleGroup_iff_card_eq`,
    via `not_isSimpleGroup_of_isPGroup_of_card_ne`), order 18 (`n_3 ∣ 2 < 3` ⇒ `n_3 = 1`;
    `not_isSimpleGroup_of_card_eq_eighteen`), and the shared Sylow-counting helper
    `card_sylow_eq_one_of_card_dvd_of_lt` (SmallOrders.lean); order 12 in OrderTwelve.lean;
    #280a/#280f cover `p*q` and `m*q` (`1 < m < q`). Remaining: 24, 30, 36, 45, 48, 50, 54
    (two-prime-factor orders; need element counting or Burnside #280e).
  - **#280f** generalization of #280a: `Nat.card G = m * q` with `q` prime and
    `1 < m < q` forces the Sylow `q`-subgroup to be normal (`n_q ∣ m < q`,
    `n_q ≡ 1 [MOD q]` ⇒ `n_q = 1`) — covers 18, 20, 28, 44, 45, … in one lemma.
    LANDED: `not_isSimpleGroup_of_card_eq_mul_prime_of_lt` in
    `BoringMath/GroupTheory/Simple/SmallOrders.lean` (sorry-free).
- **#281 CFSG.C.1a** close the `(2,3)` exception at group level — LANDED so far
  in `Classification.lean`: `card_rootsOfUnity_two_zmod3 = 2`,
  `card_center_SL_2_3 = 2`, `card_PSL_2_3 = 12`; remaining:
  `not_isSimpleGroup_PSL_2_3` via #280c.
- **#282 CFSG.C.1b** the order-168 family — LANDED in `Classification.lean`:
  `card_SL_3_2 = 168`, `card_center_SL_3_2 = 1`, `card_PSL_3_2 = 168`; remaining:
  `PSL(3,2)` simple — LANDED: `PSL_3_2_isSimpleGroup` (PSLSimple.lean), directly
  from the rank ≥ 3 Iwasawa theorem (`PSL_isSimpleGroup_zmod_of_three_le` at `n = 3`),
  with `card_PSL_3_2 = 168` in Classification.lean.
- **#283** (= #235, detailed) `Nat.card (rootsOfUnity n F_q) = gcd n (q - 1)`
  over finite fields (`F_qˣ` cyclic of order `q-1`) → the full order formula
  `|PSL(n,q)| = (∏_{i<n} (q^n - q^i)) / ((q-1) * gcd n (q-1))`.
  Module `BoringMath/GroupTheory/Simple/PSLCard.lean` pins the statement
  (`card_rootsOfUnity_zmod_prime`, TEMPORARY SORRY with peeling plan:
  `rootsOfUnityEquivNthRoots` → Bezout+Fermat in `ZMod p` →
  `nthRoots d 1` has card `d` for `d ∣ p-1` via `roots_X_pow_card_sub_X`;
  or the cyclic-torsion route via `IsCyclic (ZMod p)ˣ`) and proves the
  assembled formula `card_PSL_zmod_prime_mul_gcd` from it.
- **#284 CFSG.C.1c** `|PSL(2,4)| = |PSL(2,5)| = 60` (needs #283);
  `card_alternatingGroup_fin6 = 360` LANDED; exceptional isomorphisms
  `A_5 ≅ PSL(2,4) ≅ PSL(2,5)`, `A_6 ≅ PSL(2,9)`, `A_8 ≅ PSL(4,2)` under #256.

### Phase 3 — sporadic (ATLAS)
- **#222 PREP** ATLAS front matter + sporadic pages.
- **#216 CFSG.D** sector tracking; **#232 CFSG.D.1** Mathieu M11–M24 as permutation groups;
  **#233 CFSG.D.2** the other 21 sporadics.

### Phase 4 — assembly
- **#214 CFSG.0** master theorem sorry-free (sectors A–D feed it; A proved, B consumed).

## Working order note
Phases 2 and 3 are independent of Phase 1's hardest parts; Phase 2's PSL milestone
(#230) and Phase 3's Mathieu milestone (#232) are the natural first targets since
mathlib already supplies their surroundings.
