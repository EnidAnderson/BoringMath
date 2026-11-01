# Audit 2026-11-01 — Bernoulli floor (ticket #204, M.1.3a): consume-or-cite at pin v4.35.0-rc3

Machine: grep over the pinned mathlib checkout
`EnidsMathMadness/.lake/packages/mathlib` at rev `v4.35.0-rc3`. Verdicts stamped
"pending build" (this audit is grep-only; no compilation).

## Parity row — CONSUME (present at pin)

- `bernoulli_eq_zero_of_odd {n : ℕ} (h_odd : Odd n) (hlt : 1 < n) : bernoulli n = 0`
  — `Mathlib/NumberTheory/Bernoulli.lean:212`.
- Sibling: `bernoulli'_eq_zero_of_odd` (Bernoulli.lean:178),
  `bernoulli_eq_bernoulli'_of_ne_one` (:215), values `bernoulli_zero/one/two` (:202–208).
- Decision: the parity wrapper row in `BoringMath/NumberTheory/Bernoulli/Audit.lean`
  consumes `bernoulli_eq_zero_of_odd` by a one-line term — no duplication (STYLE.C
  consume-or-cite law).

## Growth row — GAP (absent at pin), recorded honestly

- No `abs_bernoulli`, no `|B_{2k}| ≤ …` growth bound, no `two_pow`-relative bound exists
  anywhere in the pinned checkout (grep for `bernoulli.*two_pow`, `abs_bernoulli`,
  `bernoulli_le`, `le_bernoulli`, `growth` over `Mathlib/` — zero hits).
- Decision per ticket: do NOT pad this ticket with a growth lemma; the growth row is
  deferred to a separate moderate ticket. The divergence-of-Σ 1/n² row instead cites:
- `hasSum_zeta_two : HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) (π ^ 2 / 6)`
  — `Mathlib/NumberTheory/ZetaValues.lean:453` — CONSUME (present at pin; the ζ(2)
  anchor for the AP.1.1/AP.A.1 shelf, #201).

## Cross-references

- #183 (M.1.3 parent: Bernoulli numbers as data), #201 (AP.A.1 s=2 anchor row),
  #134 (STYLE.D), #113 (STYLE.C consume-or-cite).
