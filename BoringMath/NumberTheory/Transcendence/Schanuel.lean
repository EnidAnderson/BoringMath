/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.RingTheory.AlgebraicIndependent.Defs
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Schanuel's conjecture — ticket #526 (TREE D.11/D.9)

Schanuel's conjecture as a typed `Prop` (the "statement-layer sink": a
structure field, never an axiom — TREE D.11). Mathlib at the pin has
`AlgebraicIndependent` but no Schanuel statement (audited).

## References
* [Schanuel 1962]; [Lang] S. Lang, *Transcendental Numbers*, Addison-Wesley
  1966, ch. II.
* [Ax 1971] J. Ax, *On Schanuel's conjectures*, Ann. of Math. 93 (1971)
  (differential Schanuel, TREE D.12 — the only proved engine).
* mathlib pin v4.35.0-rc3: `AlgebraicIndependent`; MISSING: Schanuel (D.11).
-/

namespace BoringMath

-- Reference: [Lang], ch. II (Schanuel's conjecture: if `z₁,…,zₙ` are
-- ℚ-linearly independent, then `trdeg_ℚ ℚ(z₁,…,zₙ, e^{z₁},…,e^{zₙ}) ≥ n`;
-- here in the equivalent "n algebraically independent among the 2n" form).
/-- **Schanuel's conjecture** (typed statement-layer sink — a `Prop`, never
an axiom): among `z₁,…,zₙ, e^{z₁},…,e^{zₙ}` there are `n` algebraically
independent complex numbers. -/
def SchanuelConjecture : Prop :=
  ∀ (n : ℕ) (z : Fin n → ℂ), LinearIndependent ℚ z →
    ∃ w : Fin n → ℂ,
      (∀ j, w j = z j ∨ w j = Complex.exp (z j)) ∧ AlgebraicIndependent ℚ w

end BoringMath
