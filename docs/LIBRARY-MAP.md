# BoringMath library map — existing folders and proposed ones

Master map of `BoringMath/<Area>/` folders, with the mathlib-pin coverage audit
and the program need that justifies each. Proposed folders get a ticket range
in the lab register; roadmap docs are added per area as work starts.
**All tickets (both repos, #2–#400) are organized in `docs/TICKET-REGISTER.md`.**

## Existing (landed)

| Folder | Status | Notes |
|---|---|---|
| `Algebra/` | landed | ChenWord, field/subfield helpers |
| `AlgebraicGeometry/` | active (other bot) | cycles, correspondences, motives, sites |
| `CategoryTheory/` | landed | limits/pullbacks, sheaves, triangulated (Verdier) |
| `ChaosTheory/` | NEW (#309–#314) | Devaney seed landed; see CHAOS-ROADMAP |
| `Combinatorics/` | NEW (#293–#300) | Species + GenFun seeds; see COMBINATORICS-ROADMAP |
| `Complexity/` | NEW (#301–#308) | Defs seed (DTIME/P/NP, P⊆NP); see COMPLEXITY-ROADMAP |
| `FormalPeriods/` | landed | the P-line (computable, lint-clean) |
| `Foundations/` | landed | Eta |
| `GroupTheory/` | active | CFSG program (Simple/, CFSG/), SpecificGroups |
| `NumberTheory/` | landed | Bernoulli, Cyclotomic |
| `Physics/` | NEW (#356–#380) | MHI framework + Specializations + HolographicZeta + Liouville; see PHYSICS-ROADMAP |
| `ProbabilityTheory/` | NEW (#286–#292) | RatMass seed; see PROBABILITY-ROADMAP |
| `Science/` | NEW (#381–#390) | abstract VerificationSystem; see SCIENCE-ROADMAP |
| `Symmetry/` | landed | S4Census |
| `Topology/` | landed | Order opens, sober generic points |

## Proposed (posterity + program-driven), with pin audit

| Proposed folder | Pin has | Gap | Program need | Tickets |
|---|---|---|---|---|
| `RepresentationTheory/` | ACTIVE (seeds pending build, tickets 303-308) | `Character`, `FDRep`, `FinGroupCharZero`, `Homological` | blocks, Brauer, DL character theory | CFSG #249/#253, motives #262 | #315–#320 |
| `AlgebraicGroups/` | ACTIVE (seed pending build, tickets 309-314) | nothing (no linear algebraic groups) | everything: GL/SL as groups, Chevalley | Lie-type sector #251–#253 | #321–#326 |
| `Cohomology/` | ACTIVE (seed pending build, tickets 315-318) | category-theoretic homological algebra | group cohomology H¹/H², spectral seqs | reduction phase #248 | #327–#330 |
| `SetTheory/Forcing/` | ZFC, Ordinal, Cardinal, Descriptive | forcing, independence | Neukirch–Uchida side #272 | #331–#334 |
| `Logic/ProofTheory/` | `Logic`, `ModelTheory` (rich, incl. `ModelTheory/Complexity`) | sequent calculus, cut-elim, ludics/designs | games-ludics row #279, doctrine | #335–#338 |
| `InformationTheory/` | Coding, Hamming, KullbackLeibler | Shannon entropy, Kolmogorov complexity | BPP/PAC #308, games | #339–#342 |
| `CombinatorialGames/` | ACTIVE (seed pending build, tickets 331-334) | only `Order/GameAdd` | Sprague–Grundy, partizan, misère | BoringLab/Games consumers | #343–#346 |
| `NumberTheory/Transcendence/` | Lindemann–Weierstrass | Gelfond–Schneider, Hilbert 7, Apéry | lab T3 (ζ(2)), periods | #347–#349 |
| `Analysis/Asymptotics/` | `Analysis` | saddle-point/Mellin asymptotics | analytic combinatorics #297–#298 | #350–#352 |
| `Optimization/` | `Combinatorics/Optimization`, `Analysis/Convex` | LP/IP at scale, duality | posterity | #353–#355 |

Rule: a proposed folder becomes real when its first ticket is picked up; until
then it lives here (and in the lab register) so scope creep has a home.
