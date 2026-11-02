# Probability theory roadmap — BoringMath/ProbabilityTheory/ (tickets #286–#292)

Pin audit (mathlib v4.35.0-rc3): `Mathlib/Probability/` is rich — `PMF`
(`ProbabilityMassFunction/`), kernels, martingales, independence, CLT, strong
law, Borel–Cantelli, distributions, conditional probability/expectation. Our
folder EXTENDS this; nothing here duplicates the pin.

Why now: ticket #287 (from the epistemology thread) needs the bridge from
`Learning.lean`'s ℚ-mass prediction tables to `PMF`, so that identification in
the limit has a probabilistic (PAC-style) sibling layer.

## Ticket tree

- **#286** `ProbabilityTheory/RatMass.lean` — SEED LANDING: a ℚ-valued prediction
  table over a finite outcome space (nonnegative, sum 1) yields a `PMF`
  (`PMF.ofRatTable`), with the pointwise mass lemma. Bridge to #31/#28.
- **#287** finite PMF combinatorics: `PMF` on a `Fintype` ↔ finite tables;
  expectation of a function as a finite sum (`PMF.integral`/`tsum` over
  `Fintype`); variance; proved ties to the ℚ-table shadow.
- **#288** concentration on finite sums: Hoeffding's lemma and inequality for
  independent bounded finite sums (via `PMF`/product measures on `Fin n`),
  Chernoff bound. Feeds the PAC generalization bound (#289).
- **#289** the PAC layer for finite hypothesis families (deterministic shadow in
  `Learning.lean`): with high probability over samples, every compatible
  hypothesis has small error — proved from #288 + the elimination lemma
  `ledgerWeight_runLedger_zero`.
- **#290** probabilistic method basics: if a random structure avoids all bad
  events with positive probability, it exists (finite union bound); first
  applications (e.g. a graph property).
- **#291** martingale convergence interface: Doob's upcrossing on finite
  filtrations, tying to `Probability/Martingale` at the pin.
- **#292** connection to the games/motives dictionary: referee conventions as
  random strategies (mixed strategies = PMFs over pure strategies), value of
  the game as expectation — the T2-bet interface (#276–#279).

## References
* [Billingsley] P. Billingsley, *Probability and Measure*, Wiley 1995.
* [Hoeffding 1963]; [Chernoff 1952]; [Valiant 1984] PAC; [Shalev-Shwartz–Ben-David
  2014] *Understanding Machine Learning* (the PAC finite-class bound, ch. 2).
* mathlib pin v4.35.0-rc3: `Probability.ProbabilityMassFunction.*`,
  `Probability.Kernel`, `Probability.Martingale`, `MeasureTheory`.
