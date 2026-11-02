# Physics roadmap — BoringMath/Physics/ (tickets #356–#370)

## The organizing principle (decided here, before any content)

The Physics folder is organized **top-down**, computad-style: we define the
most general framework first — **Motivic Holographic Information (MHI)** — and
every area of physics is a *specialization instance* of it, not built up from
"the basics" as a student would learn. Concretely: `Physics/MotivicHolographicInfo.lean`
defines the `MotivicHolographicInfo` structure (bulk phase category, boundary
site, holographic functor, information measure with the holographic equation
`boundaryInfo ∘ hologram = bulkInfo`); each area (`Physics/ClassicalMechanics.lean`,
`Physics/QuantumMechanics.lean`, ...) provides an MHI instance plus its
area-specific fields. The framework is the library; the areas are data.

This mirrors the lab's existing `BoringLab/Physical/PhysicalDoctrine` (LAB
PHYS.0, the five-axiom operational doctrine with calibrations) and the
Motivic Information theory-element (MI.0.1, #67): MHI is the BoringMath-grade,
computable shadow of "the bulk is encoded in the boundary" (holographic
principle) with motivic information as the counting/resource layer.

## Non-vacuity / acceptance criteria (anti-triviality)

Honest note (2026-11): as seeded, `MotivicHolographicInfo` is an *interface* —
its only law (`holographicEq`) is satisfiable by the trivial calibration, so the
framework alone proves nothing. That is deliberate (computad-style: the general
frame first), but the folder is only non-crank when each specialization proves
**laws on nontrivial instances**. Acceptance criteria per area:

- Classical mechanics (#358): Liouville — the Hamiltonian flow preserves the
  symplectic form — proved on a nontrivial instance (pin has
  `Matrix.symplecticGroup`, `mem_iff' : A * J * Aᵀ = J`).
- Quantum mechanics (#359): unitarity of time evolution; measurement
  probabilities sum to 1 (via the probability folder #286–#292).
- FQFT (#360): Atiyah–Segal axioms as theorems about the hologram functor.
- Gravity (#361): the AdS/CFT dictionary as an adjunction, with the
  entropic/information bound (boundary entropy = bulk area in Planck units,
  statement layer).
- Zeta/holography (#371, below): Abel–Plana proved, ζ(2) = π²/6 derived.

## The Abel–Plana dictionary and the period conjecture (#371–#375)

The motivic holographic principle in its analytic-number-theory form: the
**boundary** is the discrete sum side (`∑ f(n)`, `n : ℕ`), the **bulk** is the
contour/integral side (the complex plane, residues), and the **hologram** is
the Abel–Plana map. The holographic equation is then literally the Abel–Plana
formula: sum = integral + boundary term + contour term. Periods/zeta values
sit at the interface: the lab's T3 thread re-derives ζ(2) = π²/6 this way, with
Euler–Maclaurin remainders as the "correction" terms (zugzwang corrections).
Connection to the period conjecture / standard conjectures / t-structures: the
pin HAS t-structures (`Algebra/Homology/DerivedCategory/Ext/TStructure.lean`);
the motivic holography conjecture reads as: the period matrix of a bulk motive
is computed by the boundary's discrete invariants — an equation of information
measures, stated as a labeled conjecture (never a bare `sorry`-shaped theorem,
per the lab honesty rules).

- **#371** `Physics/HolographicZeta.lean` — SEED: the Abel–Plana formula as a
  named theorem (sorry + peeling plan via the residue theorem; pin has
  `Analysis/Complex/CauchyIntegral`) and the MHI dictionary reading.
- **#372** Euler–Maclaurin with remainder (statement + plan); ζ(2) = π²/6 by
  Abel–Plana (T3) once #371 lands.
- **#373** the motivic holography conjecture: stated as a `Prop` about
  `MotivicHolographicInfo` + periods, labeled conjecture with falsifier.
- **#374** t-structure interface: bulk motive categories with t-structures
  (pin API), the conjecture that the hologram is t-exact on the relevant subcategory.
- **#375** renormalization/residues dark sector (T4): Connes–Kreimer as the
  bulk-side Hopf algebra; Apéry certificate as boundary-side null-move.

## Universality checklist (what "a framework for any theory of physics" must carry)

Reviewed 2026-11 against the specializations table; MHI currently carries:
bulk category+unit (states/processes, P1), boundary site + locality (P3),
hologram functor + holographic equation (the principle itself), information
monoid + measures (P2). **Pending fields** (each its own ticket, added to MHI
with calibrations updated):

- **#376 time/dynamics**: a monoid `time` with `dynamics : time →* (bulk ⥤ bulk)`
  (evolution as an endofunctor action); every theory has one.
- **#377 symmetries/referee**: `referee` group acting on the boundary, ruling =
  fixed points (Wigner; PHYS.0 P4) — gauge symmetries live here.
- **#378 reconstruction/duality**: `hasReconstruction : ∃ r, Nonempty (hologram ⊣ r)`
  as a Prop field (adjunction at the pin: `CategoryTheory.Adjunction`); the
  AdS/CFT dictionary is an instance.
- **#379 observables**: measurable/observable maps `boundary → info`-valued with
  the expectation interface to the probability folder (#286–#292).
- **#380 compositionality**: bulk processes compose (already, via the category);
  tensor/product of MHI systems (two theories side by side) as a binary operation
  on MHI — needed for QFT locality and for combining subsystems.

## Crank-free rules (binding for this folder)

1. **No `axiom` declarations, ever.** Every structure field is data or `Prop`
   (as in PhysicalDoctrine). Physical content is a *theorem about a structure*.
2. Every physical interpretation lives in docstrings/comments with a citation
   (REVIEW(citation) if unverified); the code itself is pure mathematics.
3. Every seed module must ship a **calibration instance** (trivial + one
   nontrivial toy), as PhysicalDoctrine does.
4. Conjectural content (e.g. AdS/CFT as a theorem) is a labeled `sorry` with a
   peeling plan, or a `Prop` field — never asserted.
5. Bets (T-labeled) and interpretations (D-labeled) follow the lab's honesty
   rules from the workspace notes.

## Ticket tree

- **#356** `Physics/MotivicHolographicInfo.lean` — SEED: the MHI structure +
  trivial and toy calibrations, all fields checked.
- **#357** `Physics/Specializations.lean` — SEED: the specialization slot
  structures (each extends MHI with area fields; instances land per-area).
- **#358** Classical mechanics: symplectic phase spaces as bulk objects,
  Hamiltonian as `phaseSpace → info`; Liouville (volume preservation) as a
  theorem slot.
- **#359** Quantum mechanics: Hilbert object in the boundary, observables as
  self-adjoint endomorphisms (statement layer), measurement = referee ruling
  (ties to PhysicalDoctrine P4).
- **#360** Functorial QFT (Atiyah–Segal): an MHI whose bulk is the cobordism
  category; the QFT as the hologram functor into the boundary — statement + plan.
- **#361** Gravity/holography: AdS/CFT as an adjunction bulk ⊣ boundary;
  differential cohomology as the observable layer (Schreiber's cohesive
  framework, statement layer).
- **#362** Statistical mechanics / thermodynamics: the resource monoid `info`
  with Landauer's principle as a theorem slot; ties to P2.
- **#363** Condensed matter / topology of phases: the boundary site's
  sheaves = order parameters; phase transitions as sheaf changes.
- **#364** Chemistry as molecular QM specialization (posterity).
- **#365–#370** reserved: gauge theory (higher connections on the bulk site),
  cosmology, quantum information interfaces (#339–#342), measurement problem
  formulations (decoherence as information flow bulk→boundary), foundations
  debates as *structures* (e.g. Everett/branching as a functor), and the
  MI.0.1 world-connection field discipline applied to physics claims.

## References
* [Schreiber] U. Schreiber, *Differential cohomology in a cohesive ∞-topos*
  (the higher-structure approach this folder adapts to 1-categorical,
  computable carriers).
* [Maldacena 1997]; [Witten 1998] (AdS/CFT); [Atiyah 1988] (FQFT axioms,
  Publ. Math. IHÉS 49 — already the P5 anchor of PhysicalDoctrine).
* [’t Hooft 1993]; [Susskind 1995] (holographic principle).
* Lab: BoringLab `docs/PhysicalDoctrine.md` (PHYS.0), `docs/...` MI.0.1 (#67).
* mathlib pin v4.35.0-rc3: `CategoryTheory` (categories, sites/coverages),
  `Algebra.Order.Monoid` (`IsOrderedMonoid`).

## The Rovelli (LQG) and Susskind (string) lanes — #352 items 3–15, #366

Landed (all proved, warning-clean, style-clean):

- **#352 items 3–6** `Physics/LQG/SpinNetwork.lean` — colored graphs as data
  (vertices, endpoints, edge spins, intertwiner data), the relabeling setoid
  (diffeomorphism invariance as an equivalence relation, proved), area and
  info invariance under relabeling (proved), and the LQG kinematical MHI
  instance `lqgKinematics` with the discrete-info law `lqgKinematics_info_gap`
  (proved).
- **#352 items 7–9** `Physics/LQG/HolonomyFlux.lean` — signed-edge holonomies,
  the path composition law `pathHolonomy_append` (proved), cylinder functions
  (`dependsOn`), pullback as an algebra homomorphism (proved).
- **#352 items 10–12** `Physics/LQG/VolumeSpectrum.lean` — the `VolumeOperator`
  structure (positivity, relabeling invariance, discreteness as Prop fields)
  with the area-as-volume toy proving all laws including the volume gap.
- **#352 items 13–15** `Physics/LQG/SpinFoam.lean` — foams as labeled
  2-complexes, `repDim` (dim j = 2j+1), amplitude positivity (proved),
  boundary spin network, boundary-area ≤ bulk-area (proved).
- **#366 items 1–3** `Physics/Strings/Worldsheet.lean` — lattice worldsheet and
  the lattice Polyakov action; nonnegativity, translation invariance,
  quadratic homogeneity, and relabeling (background) invariance all proved.
- **#366 items 4–6** `Physics/Strings/HolographicBound.lean` — the holographic
  counting bound `#B ≤ k ^ #ι` (proved), the Bekenstein bound in bits, and the
  holographic toy MHI with the counting bound as its non-vacuity law.
- **#366 items 7–8** `Physics/Strings/AdSCFT.lean` — the `HolographicGravity`
  toy with the reconstruction adjunction proved (`adscftToy_reconstruction`).

Lab ledgers over the MHI framework (QG.0.1 #23 shape): BoringLab
`QGRequirements/LQG.lean` (LQG.1.1 #27) and `QGRequirements/StringTheory.lean`
(STR.1.1 #26) — demands with satisfied/pending grades. **The motivic hooks**
are the info measures: `SpinNetwork.info = Σ_e (repDim j_e − 1)` (proved row)
and the boundary cell count `bulkInfo = #ι` of the holographic toy (proved
row) — the slots where the DM-motive/period layer (#117, #373, MI.0.1 #67)
attaches.

Open gaps (pending rows with peeling plans in the lab ledgers): the proper
volume spectrum (intertwiners + 6j symbols), black-hole entropy matching
`S = A/4` in counting form (LQG); the continuum limit of the lattice action
and perturbation-series convergence (string theory).

### Gap tickets (filed; to be filled, never simplified away)

- **#367** LQG open rows (lab LQG.1.1 #27): proper volume spectrum
  (intertwiners + 6j), black-hole entropy `S = A/4` in counting form.
- **#368** STR open rows (lab STR.1.1 #26): continuum limit of the lattice
  action, perturbation-series convergence.
- **#369** MI.0.2 puncture-degree model (lab #66): FILLED —
  `Physics/LQG/PunctureCycle.lean` (puncture point-cycle over Spec k,
  degree = total spin via `degree_single` + `residueDegree_id`), bridged by
  `gysinMove_degree_trace` (via `degree_pushforward`). Finer per-edge model
  (degrees = area eigenvalues) is the named extension.
- The discrete-info law is stated at full generality (zero element as
  explicit data): `DiscreteInfo` + `mhi_exists_discreteInfo` in
  `Physics/LQG/SpinNetwork.lean`.
