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
