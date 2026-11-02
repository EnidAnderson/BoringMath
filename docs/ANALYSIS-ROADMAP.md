# Analysis roadmap — BoringMath/Analysis/ (tickets #500–#509)

Pin audit (mathlib v4.35.0-rc3): `Analysis/` at the pin is deep (complex
analysis incl. `circleIntegral` and the Cauchy integral formula, meromorphic
functions, asymptotics `IsBigO`/`IsLittleO`, special functions incl. `exp`,
`log`, Gamma, `BinaryEntropy`, measure theory). MISSING (audited against the
D-line tickets): the residue theorem, winding numbers/argument principle
(TREE D.13–D.15, D.17), the special-function shelf `Ein/Ci/E₁/Si` (D.8),
Stirling/saddle-point asymptotics (#350–#352), the measure-theoretic
probability bridge (#558, seeded in `ProbabilityTheory/Measure.lean`).

This folder is the substrate for the transcendence line (D-line) and the
analytic holography law (#371/#372).

## Ticket tree

- **#500** `Analysis/Complex/Contour.lean` — SEED LANDED: `HasResidueAt`,
  residue theorem, Cauchy–Goursat (circle form), argument principle (all
  named sorries with peeling plans). Home of TREE D.13–D.17.
- **#501** `Analysis/SpecialFunctions/Series.lean` — SEED LANDED: `einSeries`,
  `siSeries` (noncomputable power series), `exists_entire_ein` (sorry).
  Home of TREE D.8.
- **#502** `Analysis/Asymptotics/Basic.lean` — SEED LANDED: `IsAsymptotic`,
  Stirling's formula (sorry). Home of #350–#352 (saddle point/Mellin for
  analytic combinatorics #297–#298).
- **#503** Cauchy's integral formula strengthening + Laurent expansions on
  annuli (feeds D.13).
- **#504** TREE D.17: Cauchy–Goursat on punctured rectangles (mechanical
  route to D.15).
- **#505** TREE D.15: residue theorem proved from #500/#504.
- **#506** TREE D.14: winding numbers + argument principle proved.
- **#507** TREE D.16: Hermite's contour method assembled for LW (feeds #531).
- **#508** #371/#372 consumption: Abel–Plana ⇒ `ζ(2) = π²/6` (with
  `Physics/HolographicZeta.lean` and lab T3).
- **#509** reserved: functional-analysis substrate for LQG `L²(Ā, dμ_AL)`
  (#352) and unitary representations (#315–#320) — `Analysis/Functional/`
  planned.

## References
* [Ahlfors], ch. 4; [Conway], ch. IV; [de Bruijn], ch. 3, 5;
  [Flajolet–Sedgewick], ch. VIII; [DLMF] §6.
* mathlib pin v4.35.0-rc3: `Analysis/Complex/CauchyIntegral`,
  `Analysis/Meromorphic/Basic`, `Analysis/Asymptotics/*`,
  `Analysis/SpecialFunctions/*`.
