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
  (Iwasawa; sub-lemmas: SL perfect, projective action quasiprimitive, faithful mod center);
  **#231 CFSG.C.2** the other 15 families.
- **#218 CFSG.BRIDGE** Chevalley ℤ-forms + Deligne–Lusztig + motivic dictionary row (bet).
- Code so far: `BoringMath/GroupTheory/Simple/Classification.lean` (sectors A/B consumed,
  PSL cardinality proved), `BoringMath/GroupTheory/Simple/LieAlgebraBridge.lean`
  (lieAlgA/B/C/D; `dim sl(n,K) = n²−1` proved).

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
