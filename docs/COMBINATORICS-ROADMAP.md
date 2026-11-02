# Combinatorics roadmap — BoringMath/Combinatorics/ (tickets #293–#300)

Pin audit (mathlib v4.35.0-rc3): `Mathlib/Combinatorics/` has additive
combinatorics, graph theory, designs, enumeration (partitions, `GenFun` for
partitions), Young tableaux, etc. `RingTheory/PowerSeries` has formal power
series with `coeff_mul`, `Catalan`, `Exp`, `Derivative`. MISSING: combinatorial
species (Joyal), general OGF/EGF theory, analytic combinatorics
(Flajolet–Sedgewick), and the link to the CFSG sector-D sporadic orders
(counting/structural).

## Ticket tree

- **#293** `Combinatorics/Species.lean` — SEED LANDING: a species as a functor
  `Type → Type` with `Fintype` instances on finite carriers; `card : Species →
  ℕ → ℕ`; sum and product species with proved cardinality formulas.
- **#294** species operations: disjoint union, product, composition (partitional),
  derivative; the exponential formula (connected components) as a named theorem.
- **#295** `Combinatorics/GenFun.lean` — SEED LANDING: ordinary generating
  functions as `PowerSeries ℚ` (`ogf`), coefficient lemmas, the Cauchy product
  proved via `PowerSeries.coeff_mul`.
- **#296** EGFs and the species↔EGF dictionary: `card S n * n!` coefficients;
  labelled vs unlabelled counting.
- **#297** analytic combinatorics layer (over ℂ): radius of convergence,
  coefficient asymptotics for rational OGFs (partial fractions), the
  transfer theorems as named statements; singularity analysis deferred (#298).
- **#298** Flajolet–Sedgewick singularity analysis: [z^n] asymptotics from
  dominant singularities for the standard scale (needs #297's complex layer).
- **#299** applications to the CFSG program: order formulas of sporadic groups
  as data (`sporadicOrder`), generating-function sanity checks; and to the
  games thread (nimber arithmetic as a species/ordinal structure).
- **#300** additive-combinatorial tools used by the reduction phase: Freiman,
  Plünnecke (statement layer), connecting to `Mathlib/Combinatorics/Additive`.

## References
* [Bergeron–Labelle–Leroux] *Combinatorial Species and Tree-like Structures*,
  Cambridge 1998 (Joyal's theory).
* [Flajolet–Sedgewick] *Analytic Combinatorics*, Cambridge 2009.
* [Stanley] R. P. Stanley, *Enumerative Combinatorics*, vols. 1–2, Cambridge.
* mathlib pin v4.35.0-rc3: `RingTheory.PowerSeries.*`, `Combinatorics.Enumerative.*`.
