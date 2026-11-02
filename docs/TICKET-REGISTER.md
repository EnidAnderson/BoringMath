# Master ticket register — the whole program, organized by stage

One register for every ticket in the program. Lab-side tickets (#2–#183) are
GitHub issues on `EnidAnderson/BoringLab`, tracked in `BoringLab/docs/`; the
library program (#201–#400) is doc-tracked here in `BoringMath/docs/`. Status
legend: **landed** (proved/committed), **in-flight** (agent or bot working),
**open** (named, not started), **conjecture** (labeled bet).

## Stage A — BoringLab foundations (#2–#183) — home: BoringLab/docs + GitHub issues

Games (L-line, #2/#10/#20/#21/#100/#111...), Doctrine/computads (#3/#8/#9/#14/
#68/#69/#70/#72/#112...), Epistemology (#28–#43, #54, #62–#67...), Deform/L∞
(#108/#109...), Physics doctrine (PHYS.0 #6), parallels register (#139).
Status: large parts landed; in-flight: Epistemology Regime/TruncatedLearning/
Verisimilitude, Games/Trace, Lisp/Hygiene, Deform (see `git status`).
Next: finish in-flight files, then L-line maturity per `games-library-roadmap.md`.

## Stage B — CFSG program (#214–#279) — home: CFSG-ROADMAP.md

Master: #214 (open, master sorry). Sectors: A landed, B landed (consumed),
C in progress, D data landed.

| Ticket | Content | Status |
|---|---|---|
| #226 | Feit–Thompson odd order | open (refs held) |
| #230 | PSL simplicity (Iwasawa) | in-flight: rank-2 consumed at pin (#700b4e3); rank≥3 reduced (#34cf085) to SL perfect + Iwasawa; transvection identity landed (#4d0f66e); SL_isPerfect + PSL_simple_of_SL_perfect open |
| #235/#283 | \|μ_n(F_q)\| = gcd formula → \|PSL\| formula | in-flight (CyclicTorsion landed #7fae0af; PSLCard.lean being closed by other lane) |
| #236–#257 | CFSG.LIB modules | partially landed (Quasisimple, Signalizer, ThompsonSubgroup, Fusion, FusionSystem, Local, PCore #c29c4f1, StronglyClosed, AlmostSimple, ThreeTransposition, BNPairs, Centralizer); rest open |
| #258 | \|A_5\|=60 | landed |
| #280a/b | order pq, p² not simple | landed (#72a321f) |
| #280c | order 12 | in-flight (OrderTwelve.lean) |
| #281/#282 | (2,3) exception, order-168 family | cards landed; not_isSimpleGroup_PSL_2_3 + PSL(3,2) simple open |
| #284 | \|PSL(2,4)\|=\|PSL(2,5)\|=60 | open (needs #283) |
| #285 | Ockham bound + counterexample | landed (#12ac636) |
| #286–#400 | new library folders | see Stage C |

## Stage C — new BoringMath libraries (#280–#400) — homes: per-area roadmaps

| Range | Folder | Roadmap | Landed | In-flight/open |
|---|---|---|---|---|
| #286–#292 | ProbabilityTheory | PROBABILITY-ROADMAP | #286 RatMass (proved) | #287–#292 open |
| #293–#300 | Combinatorics | COMBINATORICS-ROADMAP | #293 Species, #295 GenFun (proved) | #294–#300 open |
| #301–#308 | Complexity | COMPLEXITY-ROADMAP | #301 Defs (P⊆NP proved) | #302–#308 open |
| #309–#314 | ChaosTheory | CHAOS-ROADMAP | #309 Devaney defs | Banks theorem + #310–#314 open |
| #315–#320 | RepresentationTheory | REPRESENTATION-ROADMAP | — | all open |
| #321–#326 | AlgebraicGroups | ALGEBRAICGROUPS-ROADMAP | — | all open |
| #327–#355 | Cohomology/Forcing/ProofTheory/InfoTheory/CGT/Transcendence/Asymptotics/Optimization | LIBRARY-MAP | — | all open (proposed) |
| #462–#467 | CombinatorialGames missing main theorems (2026-11-02 audit of Impartial/Sum/Partizan): #462 attainment lemma `exists_move_grundy_eq_of_lt`; #463 close the `grundy_sum` xor-theorem sorry (Sum.lean:84); #464 outcome-for-sums `outcome_sum_eq_p_iff`; #465 multi-heap Nim / Bouton P-iff-xor-0; #466 partizan Conway order + partial-order laws; #467 partizan outcome + determinacy. GitHub issues #372–#377 (sub-issues of #331/#332) | LIBRARY-MAP (CGT row) | Mex/Impartial/Outcome landed; Sum.lean holds the sanctioned `grundy_sum` sorry | open |
| #356–#380 | Physics | PHYSICS-ROADMAP | #356 MHI, #357 Specializations, #358 ClassicalMechanics+Liouville (proved), #371 zeta seed, #352 LQG items 2–15 (proved), #366 STR lane (proved) | #359–#365, #367–#380 open |
| #381–#392 | Science + Foundations | SCIENCE-ROADMAP | #381 Verification (proved), #391 Computad (proved) | #382–#390, #392 open |
| #393–#400 | cross-program connections | CONNECTIONS.md | — | guidance tickets open |
| #401–#408 | LinearAlgebra | LINEARALGEBRA-ROADMAP | #401 Jordan seed, #402 RationalCanonical seed | #403–#408 open |
| #409–#416 | GaloisTheory (Beilinson focus) | GALOIS-ROADMAP | #409 ArtinSchreier seed, #410 InverseGalois seed, #411 Beilinson seed | #412–#416 open |
| #417–#424 | LinearAlgebra (extension wave: spectra, linear logic, computadic rewriting, higher LA) | LINEARALGEBRA-ROADMAP | #417 Spectrum, #418 LinearLogic, #419 Computadic, #420 Higher seeds | #421–#424 open |
| #425–#428 | GaloisTheory (Galois cohomology → Beilinson–Lichtenbaum bridge) | GALOIS-ROADMAP | #425 GaloisCohomology seed | #426–#428 open ( #428 depends on KTheory lane ) |

## Stage D — breadth pass: new top-level and mid-level libraries (#500–#561)

Opened by the folder-breadth pass: the structure now anticipates the full
breadth of modern mathematics around the motivic/transcendence core. Each new
folder landed with a seed module (defs + named sorries with peeling plans, per
STYLE §7) and a per-area roadmap. Homes: per-area roadmaps.

| Range | Folder | Roadmap | Seeds landed | Open |
|---|---|---|---|---|
| #500–#509 | `Analysis/` | ANALYSIS-ROADMAP | #500 Complex/Contour, #501 SpecialFunctions/Series, #502 Asymptotics/Basic | #503–#509 (Cauchy strengthening, D.13–D.17 home, Abel–Plana #371/#372, Functional #509) |
| #510–#519 | `AlgebraicTopology/` | ALGEBRAICTOPO-ROADMAP | #510 Spectra/Basic | #511–#519 (F.1–F.4, Dold–Kan, A¹-interface, six-functor, #259) |
| #520–#524 | `KTheory/` | KTHEORY-ROADMAP | #520 K0, #521 Milnor | #522–#524 (exact cats K.1, GW/Witt K.3/K.4, K-spectrum) |
| #525–#533 | `NumberTheory/Transcendence/` | TRANSCENDENCE-ROADMAP | #525 Gelfond, #526 Schanuel, #527 Apéry | #528–#533 (Baker D.4, Siegel–Shidlovsky D.5, Hermite–Lindemann D.2, LW assembly D.1, D.9 capstone, Mahler D.10) |
| #534–#537 | `SetTheory/` | SETTHEORY-ROADMAP | #534 Forcing/Basic, #535 Descriptive | #536–#537 (Boolean-valued models #332, independence #333–#334 / Neukirch–Uchida #272) |
| #538–#541 | `Logic/` | LOGIC-ROADMAP | #538 ProofTheory/Sequent, #539 Computability/Bridge | #540–#541 (cut-elim consequences #336, ludics #337–#338/#279) |
| #542–#545 | `InformationTheory/` | INFORMATION-ROADMAP | #542 Entropy | #543–#545 (Kolmogorov #340, BPP/PAC #308/#341, coding #342) |
| #546–#548 | `Optimization/` | OPTIMIZATION-ROADMAP | #546 Linear | #547–#548 (IP #354, convex #355) |
| #549–#553 | `LieTheory/` | LIETHEORY-ROADMAP | #549 RootData, #550 LieGroup | #551–#553 (Chevalley #323/#252, Steinberg #324, reductive/twisted #325/#326) |
| #554–#558 | mid-level seeds | nearest roadmap | #554 GaloisTheory/Differential (PV.0), #555 Combinatorics/Graph (Turán), #556 Combinatorics/Matroid (Tutte), #557 Cohomology/SpectralSequence (LHS), #558 ProbabilityTheory/Measure | — |
| #559–#561 | planned | LIBRARY-MAP | — | #559 Analysis/Functional, #560 NumberTheory LocalField/ClassField (#272), #561 reserved |

BoringLab side: `BoringLab/Transcendence/Zeta.lean` (lab T3 `ζ(2) = π²/6`
statement, docked on #500/#508) — lab ticket, doc-tracked here.

## Next stage (dependency order, proposed)

1. **Close the in-flight files** (OrderTwelve #280c, PSLCard #283, Verification follow-ups, Liouville follow-ups) — smallest risk, unblocks #281/#284.
2. **#394: SL(n,F) perfect for n≥3** — transvections-are-commutators landed; diagonal step (diag2n as product of transvections, n≥3) then `diagonal_transvection_induction'` closes `SL_isPerfect`; then Iwasawa assembly `PSL_simple_of_SL_perfect` (#230) using pin's `IsPreprimitive`/`FaithfulSMul` + `iSup (iwasawaT) = ⊤` for general ι.
3. **#371/#372: Abel–Plana, then ζ(2)=π²/6 (T3)** — the analytic holography law; feeds #373 (period conjecture as holography).
4. **#287–#289: finite PMF combinatorics → Hoeffding → PAC** — the probabilistic layer for the Learning↔Verification dictionary (#384–#386).
5. **#302–#304: DTIME closure → reductions → Cook–Levin** — Complexity's spine.
6. **#310/#312: shift + logistic map chaotic (Devaney)** — Chaos's first laws.
7. **#321/#323: algebraic groups basic + Chevalley** — the Lie-type sector's foundation.
8. Long tail: Stage A maturity, forcing, proof theory, #P/Toda, Savitch.

Rule (anti-pile): a ticket is opened only with a home doc, a status, and its
dependency named; closed tickets move to the landed column with their commit.
