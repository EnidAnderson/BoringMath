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
| `AlgebraicTopology/` | NEW (#510–#519) | Spectra seed (F-line); see ALGEBRAICTOPO-ROADMAP |
| `Analysis/` | NEW (#500–#509) | Complex/Contour, SpecialFunctions/Series, Asymptotics seeds; D-line substrate; see ANALYSIS-ROADMAP |
| `CategoryTheory/` | landed | limits/pullbacks, sheaves, triangulated (Verdier) |
| `ChaosTheory/` | NEW (#309–#314) | Devaney seed landed; see CHAOS-ROADMAP |
| `Combinatorics/` | NEW (#293–#300, #555–#556) | Species + GenFun seeds; Graph (Turán) + Matroid (Tutte) seeds; see COMBINATORICS-ROADMAP |
| `Complexity/` | NEW (#301–#308) | Defs seed (DTIME/P/NP, P⊆NP); see COMPLEXITY-ROADMAP |
| `Cohomology/` | NEW (#315/#557) | GroupCohomology + SpectralSequence seed |
| `FormalPeriods/` | landed | the P-line (computable, lint-clean) |
| `Foundations/` | landed | Eta |
| `GaloisTheory/` | NEW (#554) | ArtinSchreier + Differential (Picard–Vessiot) seed |
| `GroupTheory/` | active | CFSG program (Simple/, CFSG/), SpecificGroups |
| `InformationTheory/` | NEW (#542–#545) | Entropy seed; see INFORMATION-ROADMAP |
| `KTheory/` | NEW (#520–#524) | K0 functoriality + Milnor seeds (K-line); see KTHEORY-ROADMAP |
| `LieTheory/` | NEW (#549–#553) | RootData + LieGroup/BN-pair bridge seeds; see LIETHEORY-ROADMAP |
| `Logic/` | NEW (#538–#541) | ProofTheory/Sequent + Computability bridge seeds; see LOGIC-ROADMAP |
| `NumberTheory/` | landed | Bernoulli, Cyclotomic |
| `NumberTheory/Transcendence/` | NEW (#525–#533) | Gelfond/Schanuel/Apéry seeds (D-line); see TRANSCENDENCE-ROADMAP |
| `Optimization/` | NEW (#546–#548) | Linear (strong duality) seed; see OPTIMIZATION-ROADMAP |
| `Physics/` | NEW (#356–#380) | MHI framework + Specializations + HolographicZeta + Liouville; see PHYSICS-ROADMAP |
| `ProbabilityTheory/` | NEW (#286–#292, #558) | RatMass seed + Measure (PMF→measure) seed; see PROBABILITY-ROADMAP |
| `Science/` | NEW (#381–#390) | abstract VerificationSystem; see SCIENCE-ROADMAP |
| `SetTheory/` | NEW (#534–#537) | Forcing + Descriptive seeds; see SETTHEORY-ROADMAP |
| `Symmetry/` | landed | S4Census |
| `Topology/` | landed | Order opens, sober generic points |
| `LinearAlgebra/` | NEW (#401–#408, linear-algebra lane) | Jordan + RationalCanonical seeds; see LINEARALGEBRA-ROADMAP |
| `GaloisTheory/` | NEW (#409–#416, Beilinson focus) | ArtinSchreier + InverseGalois + Beilinson seeds; see GALOIS-ROADMAP |

## Proposed (posterity + program-driven), with pin audit

| Proposed folder | Pin has | Gap | Program need | Tickets |
|---|---|---|---|---|
| `RepresentationTheory/` | ACTIVE (seeds pending build, tickets 303-308) | `Character`, `FDRep`, `FinGroupCharZero`, `Homological` | blocks, Brauer, DL character theory | CFSG #249/#253, motives #262 | #315–#320 |
| `AlgebraicGroups/` | ACTIVE (seed pending build, tickets 309-314) | nothing (no linear algebraic groups) | everything: GL/SL as groups, Chevalley | Lie-type sector #251–#253 | #321–#326 |
| `CombinatorialGames/` | ACTIVE (seed pending build, tickets 331-334) | only `Order/GameAdd` | Sprague–Grundy, partizan, misère | BoringLab/Games consumers | #343–#346; follow-ups #462–#469 (GitHub #372–#377, #387–#388) |
| `Analysis/Functional/` | `Analysis` (normed/inner-product spaces) | spectral theory of compact operators, unitary reps at scale | LQG L²(Ā, dμ_AL) #352, reps #315–#320 | #410 (planned) |
| `NumberTheory/LocalField/` + `NumberTheory/ClassField/` | `NumberTheory` (adeles absent at pin) | local fields, ideles, reciprocity | Neukirch–Uchida #272, Chebotarev as fusion #272 | #460–#461 (planned) |
| `Algebra/Universal/` | `Algebra` | universal algebra / varieties | posterity | reserved |

Landed in Stage D (#500–#561): `Analysis/`, `AlgebraicTopology/`, `KTheory/`,
`NumberTheory/Transcendence/`, `SetTheory/`, `Logic/`, `InformationTheory/`,
`Optimization/`, `LieTheory/`, plus mid-level seeds in `GaloisTheory/`,
`Combinatorics/Graph/`, `Combinatorics/Matroid/`, `Cohomology/`,
`ProbabilityTheory/Measure.lean` — see TICKET-REGISTER Stage D.

Rule: a proposed folder becomes real when its first ticket is picked up; until
then it lives here (and in the lab register) so scope creep has a home.
