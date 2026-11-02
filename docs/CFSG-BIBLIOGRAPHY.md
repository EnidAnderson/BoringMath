# CFSG free-source bibliography — total-coverage sourcing for faithful Lean reproduction

Principle (ticket #234 CFSG.SRC): every sector of the proof is citable from
**freely available** sources where possible — arXiv papers, open lecture notes,
open-access journals (msp.org/Project Euclid for old Pacific J. Math / Bull. AMS),
author-hosted PDFs — plus the PDFs held in `../refs/`. Where a component exists
only in paywalled originals, we cite the bibliographic record and verify the
statement via secondary sources, flagged honestly.

Held in `../refs/`: Feit–Thompson 1963 (7 parts, msp.org, open); Deligne–Lusztig
1976 (author page); ATLAS 1985 (full); Carter tables; Wilson GTM 251; GLS vol 1
endmatter/TOC; Lyons Math 555 notes; ETSU finite-simple-groups notes; plus the
arXiv downloads below.

## Phase 0 — odd-order theorem (FT.0, #226)
- Feit–Thompson 1963, PJM 13(3):775–1029 — **held** (open access, msp.org).
- Isaacs, *Finite Group Theory* (AMS 1994); Bender–Glauberman, *Local Analysis for
  Finite Groups* (2011) — the standard simplified accounts (books; borrow/buy).
- Péterfalvi's odd-order notes (free, webpage) — used by Ishida's formalization.
- **Lean precedent**: Yawara Ishida's Lean 4/Mathlib Feit–Thompson project (GitHub,
  cited in arXiv:2608.10894); Qiuzhen-CFSG project README lists Odd Order and
  Bender–Suzuki as completed.

## Phase 1 — the reduction (GLS/Aschbacher; #227–#229, #217)
- GLS Surveys 40 Numbers 1–6 (1994–2005): borrow-only on archive.org; vol 1 TOC held.
- Aschbacher, *Groups of Characteristic 2 Type*, 2 vols (CUP 2011); Gorenstein–Lyons
  Memoir 42.276 (1983); Aschbacher–Smith, Surveys 111 (2004) — obtain list.
- Free arXiv (now in refs/): **2608.10894** Nie–Zhang–Tang, *FormaTheoria … Toward the
  Formalization of the CFSG* (Lean-from-literature workflow; cites Qiuzhen-CFSG and
  Ishida's odd-order Lean project); **1609.08311** Flavell, new proof of the
  Nonsolvable Signalizer Functor Theorem; **0711.4169** Borovik–Burdges, *A New
  Trichotomy Theorem*; **1609.03026 / 1609.01969** K-group automorphisms/primitive pairs.
- Gorenstein, *Classifying the finite simple groups*, Bull. AMS 14 (1982) 1–75 (open on
  Project Euclid; direct download bot-guarded here — retry later); Solomon, Notices AMS
  65 (2018) progress report (ams.org, bot-guarded here).
- Original papers (paywalled): cited by record; statements cross-checked via the surveys.

## Phase 2 — Lie type (#215, #230, #231, #218)
- **held**: Deligne–Lusztig 1976; Wilson GTM 251 (simplicity of A_n, PSL via Iwasawa);
  Carter tables.
- Free arXiv (in refs/): **2404.11472** Geck, *A Course on Lie Algebras and Chevalley
  Groups* (modern full course — Chevalley construction, free).
- To obtain: Steinberg, *Lectures on Chevalley Groups* (1967); Steinberg 1968;
  Lusztig, *Characters of Reductive Groups over a Finite Field* (1984);
  Kleidman–Liebeck 1990.
- mathlib pin v4.35.0-rc3: `PSL`, SL card formulas, Iwasawa criterion, Lie algebra
  machinery (sl/so/sp, LieModule, weights, roots).

## Phase 3 — sporadic (#216, #232, #233)
- **held**: ATLAS 1985 (full — generators, orders, character tables for all 26).
- Free arXiv (in refs/): **1701.02095** Wilson, *Maximal subgroups of sporadic groups*;
  **2002.10921** Seysen, *A computer-friendly construction of the Monster*;
  **2203.04223**, *A fast implementation of the Monster group*.
- Original construction papers (paywalled): Griess, *The Friendly Giant*, Invent. Math.
  69 (1982); Fischer; Harada–Norton; … — cited by record.

## Phase 4 — assembly (#214)
- Master statement + sector glue in `BoringMath/GroupTheory/Simple/Classification.lean`;
  citations follow the sectors above.

## Critical arguments whose details are NOT directly accessible — and the free coverage

Must-be-in-the-proof arguments living in paywalled sources, mapped to the best
freely available coverage (all cross-referenceable in `../refs/`):

| Argument | Primary source (paywalled) | Free coverage now held |
|---|---|---|
| Odd-order theorem details | Feit–Thompson 1963 | **held in full** (msp.org); Lean precedent: yawara/odd-order (Ishida) + Qiuzhen-CFSG vendored Gorenstein–Walter/Feit–Thompson closure (public Lean code, cited in arXiv:2608.10894 **held**) |
| Nonsolvable signalizer functor theorem | GLS vol 2 / Aschbacher 2011 | Flavell, arXiv:1609.08311 **held** (new self-contained proof) |
| Trichotomy theorem | Gorenstein–Lyons Memoir 42.276 | Borovik–Burdges, arXiv:0711.4169 **held** (new proof) |
| K-group structure theory | Memoir 42.276 / GLS vols 2–5 | arXiv:1609.03026, 1609.01969 **held**; full theory still a gap (borrow Memoir/GLS) |
| Balance theorem, Thompson factorization, C*-stages, N-group analysis | Thompson 1968–71; GLS vols 1–2 | strategy surveys **held**: Gorenstein 1982 BAMS (via Wayback), Solomon 2018 Notices (via Wayback), GLS vol 1 TOC, Lyons 555 + ETSU notes; the proofs themselves remain the borrow/obtain gap |
| Quasithin case | Aschbacher–Smith, Surveys 111 (2004) | **no free full account — biggest gap**; obtain list |
| Characteristic-2 classification | Aschbacher, CUP 2011 (2 vols) | partial via held K-group/trichotomy papers; obtain Aschbacher 2011 |
| Lie-type simplicity, all 16 families | Steinberg 1967/1968; Lusztig 1984; GLS vol 3 | Wilson GTM 251 **held** (A_n, PSL via Iwasawa); Geck arXiv:2404.11472 **held** (Chevalley construction course); DL 1976 **held**; Steinberg/Lusztig on obtain list |
| Sporadic constructions, orders, maximal subgroups | ATLAS + original papers | ATLAS **held in full**; Wilson arXiv:1701.02095 **held**; Monster computer constructions arXiv:2002.10921, 2203.04223 **held**; simplicity proofs of the large sporadics: ATLAS tables + paywalled papers (partial gap) |
| Schreier conjecture (Out of simple is solvable) | follows from CFSG, details in GLS | statement in held surveys; consequence-only, proved from the master theorem |
| Bender–Suzuki, Gorenstein–Walter | 1970s papers | Lean closures exist in Qiuzhen-CFSG vendor tree (free code) |

Rule: we never cite the paywalled originals directly; statements from them are
verified through the held secondary sources and flagged `REVIEW(citation)`.

## Work-bot hints (mapped to tickets, PDFs now in `../refs/`)
- **geometric Satake** → arXiv:1603.05593 (PCMI notes; affine Grassmannian,
  geometric Satake equivalence) — the geometric lift of the Lie/representation
  sector; feeds #218/#252/#253/#271.
- **Neukirch–Uchida** → arXiv:1309.3046, 2009.10431, 1901.09243, 2601.01251 —
  G_k determines the number field; the Artin/finite-quotient side of G_mot;
  feeds #272.
- **sporadic Artin sectors** → ATLAS (held) + moonshine via Monster reps;
  feeds #272/#274.
- **Hilbert monodromy** → arXiv:1610.03528 (explicit Hilbert irreducibility) —
  generic S_n/A_n monodromy; feeds #277 (alternating row).
