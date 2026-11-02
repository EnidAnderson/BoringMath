# Chaos theory roadmap — BoringMath/ChaosTheory/ (tickets #309–#314)

Pin audit (mathlib v4.35.0-rc3): `Mathlib/Dynamics/` has topological
transitivity (`MulAction.IsTopologicallyTransitive`), periodic points
(`periodicPts`), minimal systems, topological entropy, ergodic theory,
Birkhoff sums, symbolic dynamics. MISSING: sensitive dependence, Devaney
chaos, Lyapunov exponents, the logistic/quadratic family, Sharkovsky's
theorem.

## Ticket tree

- **#309** `ChaosTheory/Devaney.lean` — SEED LANDING: `SensitiveDependence`,
  `TopologicallyTransitive` for a self-map, `DensePeriodicPts`,
  `DevaneyChaos`; Banks' theorem (transitive + dense periodic ⇒ sensitive)
  as a named theorem with peeling plan.
- **#310** Devaney chaos implies the other two characterizations; examples:
  the doubling map on the circle (pin has `Dynamics/Circle`), the shift on
  `SymbolicDynamics` (chaotic, proved).
- **#311** Lyapunov exponents for interval maps: definition via the chain
  rule for `C¹` maps, existence a.e. for absolutely continuous invariant
  measures (statement layer), Pesin's formula (statement).
- **#312** the quadratic family `x ↦ r x (1 - x)`: logistic map at `r = 4` is
  conjugate to the tent/doubling map (proved via the sine conjugacy), hence
  chaotic; period-doubling route statement.
- **#313** Sharkovsky's theorem (statement layer + ordering proof plan) and
  Li–Yorke "period three implies chaos" (proved on the interval).
- **#314** bridges: topological entropy vs chaos (positive entropy ⇒ chaos in
  the Devaney sense on compact spaces — statement), and to the games thread
  (chaotic dynamics of referee adaptation; zugzwang as sensitive dependence).

## References
* [Devaney] R. L. Devaney, *An Introduction to Chaotic Dynamical Systems*,
  Westview 1989.
* [Banks–Brooks–Cairns–Davis–Stacey 1992] (transitivity + dense periodic points
  ⇒ sensitive dependence).
* [Lyapunov 1892]; [Pesin 1977]; [Sharkovsky 1964]; [Li–Yorke 1975].
* mathlib pin v4.35.0-rc3: `Dynamics.Transitive`, `Dynamics.PeriodicPts`,
  `Dynamics.TopologicalEntropy`, `Dynamics.SymbolicDynamics`, `Dynamics.Circle`.
