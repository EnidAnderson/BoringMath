# Complexity theory roadmap — BoringMath/Complexity/ (tickets #301–#308)

Pin audit (mathlib v4.35.0-rc3): `Mathlib/Computability/` has Turing machines
(`TuringMachine/`), the halting problem, `Primrec`, Ackermann, Akra–Bazzi,
Turing degrees, regular/context-free languages. MISSING: time-bounded
computation, the classes P/NP/coNP/PSPACE/EXP, polynomial reductions,
Cook–Levin, NP-completeness, and any counting/average-case classes (#BPP etc.).

## Ticket tree

- **#301** `Complexity/Defs.lean` — SEED LANDING: languages as `Set (List Bool)`;
  halting within a step bound on a 2-tape Turing machine (`haltsWithin` via
  iterated `step`); `DTIME t`, `P = ⋃ k, DTIME (n^k)`, `NTIME`; `NP` via
  polynomial-time verifiers; `P ⊆ NP` proved.
- **#302** basic closure: `DTIME` closed under union/intersection/complement
  (for the complement, via the machine swapping accept/reject); `P` closed under
  concatenation/iteration (dovetailing) — statement + proof plan.
- **#303** polynomial reductions (`≤ₚ` via polytime-computable maps);
  transitivity proved; `NP` closed under `≤ₚ`.
- **#304** Cook–Levin: SAT ∈ NP and NP-hard (`≤ₚ`); the reduction from any
  NTIME language via tableau — the big theorem of the folder.
- **#305** NP-completeness corpus: 3-SAT, clique, vertex cover, Hamiltonian
  cycle, subset sum; each a ticket with the reduction proved.
- **#306** PSPACE and Savitch's theorem (statement layer + proof plan);
  PSPACE = NPSPACE.
- **#307** counting classes: #P, #SAT, Toda's theorem (statement layer);
  connection to `Complexity` of the CFSG order computations (sporadic orders as
  data are trivially in P — the point is the *recognition* problems).
- **#308** average-case / PAC connection: #BPP, randomness in computation,
  derandomization statements; ties to the probability folder (#286–#292) and
  the PAC layer (#289).

## References
* [Arora–Barak] M. Arora, S. Barak, *Computational Complexity: A Modern
  Approach*, Cambridge 2009.
* [Cook 1971]; [Levin 1973]; [Karp 1972] (the 21 NP-complete problems).
* [Savitch 1970]; [Toda 1991].
* mathlib pin v4.35.0-rc3: `Computability.TuringMachine.*`,
  `Computability.Halting`, `Computability.Primrec`, `Computability.Ackermann`.
