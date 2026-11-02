# Cross-program connections — guidance tickets (#393–#400)

The library's purpose is to avoid conflations and discover the *stable*
connections between related areas — checked conservatively, each connection a
proved dictionary (a def/functor with laws), not a slogan. Current map:

| Connection | Dictionary | Status / ticket |
|---|---|---|
| Learning ↔ Verification (Popper/Ockham/Kuhn) | `Learning.falsifiable` ↔ `VerificationSystem.falsified`; `OckhamBound` mind-change bound ↔ `choose_law` | #384–#386 |
| Physics MHI ↔ Science Verification | `VerificationSystem.ofMHI` | landed seed #388 |
| Abel–Plana ↔ periods ↔ holography | `HolographicZeta` + t-structures (pin) | #371–#375 |
| Computads ↔ categories ↔ theories | `Computad.ofCategory` / `presentedCategory` | #391–#392 |
| Combinatorial species ↔ sporadic orders / CFSG | OGF/EGF of `sporadicOrder` data; species of group actions | #299 |
| Mind changes ↔ complexity ↔ VC/PAC | `mindChangesOn` bounds ↔ `DTIME`/generalization | #289, #308 |
| Games ↔ motives (dictionary rows) | face-down ↔ sporadic; referee ↔ motivic Galois (T2 bet) | #276–#279 (BoringLab) |
| Chaos ↔ dynamics ↔ entropy | Devaney ↔ `TopologicalEntropy` (pin) | #314 |
| Forcing ↔ Neukirch–Uchida independence | #331–#334 | proposed |

Rule: every row must be a *proved* def/functor with laws before it is cited in
docs; otherwise it stays a labeled conjecture row.

## Guidance tickets for other lanes

- **#393** AlgebraicGeometry/Motives lane: state the MHI↔motives dictionary
  (bulk = DM_gm, boundary = realization functors) as a labeled conjecture with
  falsifier; do not conflate with #388's 1-categorical shadow.
- **#394** GroupTheory/CFSG lane: connect `SLTransvection` (commutator identity,
  landed) to `SL_isPerfect` rank≥3 via the diagonal step (diag2n as a product of
  transvections for n≥3); then `PSL_simple_of_SL_perfect` via Iwasawa.
- **#395** FormalPeriods lane: the period conjecture as a holography statement
  (connects to #373); keep Prop-field discipline.
- **#396** BoringLab Epistemology: `TruncatedLearning`/`Regime` in flight — align
  their `ruling`/verdict fields with `VerificationSystem` fields when landed.
- **#397** BoringLab Games: Sprague–Grundy belongs in BoringMath
  `CombinatorialGames/` (#343); Games consumes it.
- **#398** BoringLab Lisp/Doctrine: computad morphisms (`Computad.Map`) should
  be the Lisp macro rewriting maps; align after #391 lands.
- **#399** AUDITS lane: add a standing audit that no `axiom` declaration exists
  in BoringMath (crank-free rule) — scriptable grep.
- **#400** reserved.
