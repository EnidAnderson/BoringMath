# Optimization roadmap — BoringMath/Optimization/ (tickets #546–#548, proposed #353–#355)

Pin audit (mathlib v4.35.0-rc3): `Combinatorics/Optimization/` (valuations,
max-flow/min-cut substrate) and `Analysis/Convex/*`. MISSING: LP/IP duality
at scale, convex optimization algorithms.

## Ticket tree

- **#546** `Optimization/Linear.lean` — SEED LANDED: `LinearProgram` (data),
  `LinearProgram.feasible`, `strong_duality` (sorry with plan via weak
  duality + Farkas).
- **#547** #354: integer programming — branch & bound, cutting planes
  (statement layer; docks #353).
- **#548** #355: convex optimization — KKT conditions, gradient descent
  convergence (statement layer over pin's `Analysis/Convex`).

## References
* [Dantzig], ch. 4; [Schrijver], ch. 7; [Boyd–Vandenberghe], *Convex
  Optimization*, Cambridge 2004, ch. 5.
* mathlib pin v4.35.0-rc3: `Combinatorics/Optimization/*`, `Analysis/Convex/*`.
