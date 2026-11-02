# Science roadmap — BoringMath/Science/ (tickets #381–#390)

The Science folder is the abstract **verification system**: it ingests data,
runs experiments, and emits judgments *in its own terms*, without presupposing
any particular model (not A¹-homotopy, not DM_gm(ℚ)_ℚ). The long-term target —
stated as a labeled conjecture, never assumed — is that a motivic category
(DM_gm(ℚ)_ℚ or the MHI category) is **initial among models of science**.
Physics (#356–#380) is then a specialization of Science, as Science is of the
verification interface.

Epistemology lessons applied (from BoringLab/Epistemology): Prop-vs-data
discipline (STYLE.D — world-claims are Prop fields, never global axioms);
calibrations required; bets (T-labeled) vs interpretations (D-labeled);
REVIEW(citation) discipline; Popper/Kuhn/Ockham are *structures with laws*, not
slogans.

## Ticket tree

- **#381** `Science/Verification.lean` — SEED: the `VerificationSystem`
  structure (theory category + current model, data, experiments, run/predict,
  fits, falsified, revise, complexity, choose) with the laws as Prop fields;
  trivial calibration; the MHI dictionary (`MHI → VerificationSystem`); the
  initiality conjecture as a labeled Prop.
- **#382** real data ingestion: a `Dataset` as a computable table
  (`experiment → data` lists), ingestion = loading, with checksums/counts as
  proved invariants.
- **#383** experiment runner: `run` executing registered experiments on the
  current model, producing verdicts; calibration on a toy dataset.
- **#384** Popper layer: `falsified` laws proved on instances; demarcation vs
  the Learning thread's `falsifiable` (#28/#31).
- **#385** Ockham layer: `choose` = simplest fitting model, proved minimal
  among the candidate list (ties to OckhamBound #285).
- **#386** Kuhn layer: `revise` as model deformation; the cycle as a state
  machine (BoringLab Kuhn.lean #34); incommensurability as data property.
- **#387** the initiality conjecture made precise: category of verification
  systems, the forgetful/structure functor to motives, and the statement that
  the motivic model is initial — CONJECTURE label, proof plan via universal
  property of DM_gm.
- **#388** connection to geometric motives: the MHI↔Verification dictionary
  proved as a functor; holographic reading of model revision.
- **#389** verification of *this library itself*: self-application — the
  verification system judging its own predictions (fixed-point / diagonal
  statement layer).
- **#390** reserved: measurement theory (POVMs via probability folder #286+),
  and the referee = symmetry group dictionary (T2 bet, #276–#279).

## References
* [Popper 1959]; [Kuhn 1962]; [Kelly 1996]; lab BoringLab Epistemology (#28–#37).
* [Voevodsky] A¹-homotopy / DM_gm as candidate universal motivic model
  (conjecture target, not assumption).
* mathlib pin v4.35.0-rc3: `CategoryTheory` basics; `Algebra/Homology/
  DerivedCategory` (t-structures for #374).
