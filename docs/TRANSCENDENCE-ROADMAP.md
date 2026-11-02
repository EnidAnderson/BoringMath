# Transcendence roadmap — BoringMath/NumberTheory/Transcendence/ (tickets #525–#533, D-line)

Pin audit (mathlib v4.35.0-rc3): `NumberTheory/Transcendental/` has the
Lindemann–Weierstrass analytic part (`Lindemann/AnalyticalPart`) and Liouville
numbers; `NumberTheory/LSeries/RiemannZeta` has `riemannZeta`. MISSING
(audited against TREE D.1–D.12): Gelfond–Schneider, Baker, Apéry, Schanuel,
Siegel–Shidlovsky, Hermite–Lindemann corollaries. The contour machinery they
need lives in `Analysis/Complex/Contour.lean` (#500).

## Ticket tree

- **#525** `Transcendence/Gelfond.lean` — SEED LANDED: `gelfond_schneider`
  (sorry, plan via Hermite's method + #500). TREE D.3.
- **#526** `Transcendence/Schanuel.lean` — SEED LANDED: `SchanuelConjecture`
  as a typed `Prop` (never an axiom). TREE D.11; capstone D.9 docks here.
- **#527** `Transcendence/Apery.lean` — SEED LANDED: `apery_zeta_three_irrational`
  (sorry, plan via Beukers integral + Dirichlet criterion). TREE D.6.
- **#528** TREE D.4: Baker's theorem on linear forms in logarithms
  (statement layer).
- **#529** TREE D.5: E-functions and Siegel–Shidlovsky (statement layer).
- **#530** TREE D.2: Hermite–Lindemann corollaries (π transcendental,
  `e^r` transcendental for algebraic `r ≠ 0`) — from pin's LW engine.
- **#531** TREE D.1 / #14: Lindemann–Weierstrass assembly (statement +
  consumption of `Lindemann/AnalyticalPart` + TREE D.16).
- **#532** TREE D.9: the certificate capstone `ζ(3)` transcendental over
  `ℚ(2πi)` conditional on Schanuel (#526).
- **#533** TREE D.10: Mahler's π-approximation measure + letter-reduction
  (quantitative layer, statement only).

## References
* [Gelfond]; [Schneider]; [Baker]; [Apéry]/[van der Poorten]; [Lang];
  [Ax 1971]; [Mahler 1953].
* mathlib pin v4.35.0-rc3: `NumberTheory/Transcendental/Lindemann/*`,
  `NumberTheory/LSeries/RiemannZeta`; BoringMath pin: `Analysis/Complex/Contour`.
