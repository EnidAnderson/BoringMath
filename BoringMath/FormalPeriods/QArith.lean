/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/

import BoringMath.FormalPeriods.QArith.Normalize
import BoringMath.FormalPeriods.QArith.Ops
import BoringMath.FormalPeriods.QArith.CrossEq
import BoringMath.FormalPeriods.QArith.IntLemmas
import BoringMath.FormalPeriods.QArith.FieldLaws
import BoringMath.FormalPeriods.QArith.FieldLawsAssoc
import BoringMath.FormalPeriods.AxiomLint

/-!
# Constructive rational arithmetic (`QArith`)

A narrow, fully computable replacement for the choice-tainted rational
arithmetic of Lean core / Mathlib at the pin `lean4 v4.35.0-rc3` /
`mathlib v4.35.0-rc3` (ticket RETRO.7). At this pin, `Rat.add`, `Rat.mul`,
`Rat.sub`, `Rat.div`, `Rat.normalize` and `Rat.instField` all depend on
`Classical.choice`: the taint enters through the `reduced` field proofs —
`Rat.normalize.reduced` (via `Int.natAbs_ediv_of_dvd`/`Int.natAbs_ediv`)
for `Rat.add`/`Rat.sub`/`Rat.normalize`, and through `Int.divExact_eq_tdiv`
in the `reduced` field of `Rat.mul`. Everything else used here
(`Rat.mk'`, `Rat.normalize.dvd_num`/`dvd_den`/`den_nz`, `Nat.gcd` lemmas,
`Int.divExact_eq_ediv`, `Int.natCast_ediv`, ...) is axiom-clean.

This module defines computable operations `qadd`, `qneg`, `qsub`, `qmul`,
`qinv`, `qdiv` over `ℚ` built directly on `Rat.mk'` with explicit
computable normalization (`Nat.gcd` + `Int.divExact`/`Nat.divExact` +
a computable `Nat.Coprime` proof via `qNatAbs_ediv` and
`Nat.coprime_div_gcd_div_gcd`), and proves the field laws the P-line
needs. Every declaration is linted at the bottom with `#print axioms`;
all are clean (only `propext`/`Quot.sound`).

## References
* [MRR] A. Mines, F. Richman, W. Ruitenburg, *A Course in Constructive
  Algebra*, Springer Universitext, 1988, DOI 10.1007/978-1-4419-8640-5
  (the rationals as a constructive field; field laws).
* [LeanRat] Lean 4 core `v4.35.0-rc3`, `Init/Data/Rat/Basic.lean` and
  `Init/Data/Rat/Lemmas.lean` (the `Rat` structure, `Rat.mk'`,
  `Rat.normalize`, `Rat.ext`).
-/

/-! ### Axiom lint trailer: every declaration must be CLEAN
(only `propext` / `Quot.sound`; no classical choice, no conjecture axioms). -/

#lint_axioms BoringMath.qdvd_num
#lint_axioms BoringMath.qdvd_den
#lint_axioms BoringMath.qNatAbs_ediv
#lint_axioms BoringMath.qreduced
#lint_axioms BoringMath.qden_nz
#lint_axioms BoringMath.qmk
#lint_axioms BoringMath.qmk_num
#lint_axioms BoringMath.qmk_den
#lint_axioms BoringMath.qdivExact_num_mul
#lint_axioms BoringMath.qdivExact_den_mul
#lint_axioms BoringMath.qdivExact_den_mul_nat
#lint_axioms BoringMath.qgcd_pos
#lint_axioms BoringMath.qgcd_ne_zero
#lint_axioms BoringMath.qmul_comm_assoc
#lint_axioms BoringMath.qmul_assoc_swap
#lint_axioms BoringMath.qmul_assoc_swap'
#lint_axioms BoringMath.qcancel
#lint_axioms BoringMath.qneg_reduced
#lint_axioms BoringMath.qneg
#lint_axioms BoringMath.qneg_num
#lint_axioms BoringMath.qneg_den
#lint_axioms BoringMath.qden_mul
#lint_axioms BoringMath.qadd
#lint_axioms BoringMath.qadd_num
#lint_axioms BoringMath.qadd_den
#lint_axioms BoringMath.qmul
#lint_axioms BoringMath.qmul_num
#lint_axioms BoringMath.qmul_den
#lint_axioms BoringMath.qsub
#lint_axioms BoringMath.qsub_def
#lint_axioms BoringMath.qinv_den_nz
#lint_axioms BoringMath.qinv_reduced_neg
#lint_axioms BoringMath.qinv_reduced_pos
#lint_axioms BoringMath.qinv
#lint_axioms BoringMath.qmk'_num
#lint_axioms BoringMath.qmk'_den
#lint_axioms BoringMath.qinv_num_neg
#lint_axioms BoringMath.qinv_den_neg
#lint_axioms BoringMath.qinv_num_pos
#lint_axioms BoringMath.qinv_den_pos
#lint_axioms BoringMath.qdiv
#lint_axioms BoringMath.qdiv_def
#lint_axioms BoringMath.qnum_eq_zero
#lint_axioms BoringMath.qnum_ne_zero
#lint_axioms BoringMath.qden_eq_of_cross
#lint_axioms BoringMath.qeq_of_cross
#lint_axioms BoringMath.qeq_iff
#lint_axioms BoringMath.qmk_cross
#lint_axioms BoringMath.qmk_int_of_eq
#lint_axioms BoringMath.qmk_eq_iff
#lint_axioms BoringMath.qmk_congr
#lint_axioms BoringMath.qmk_self
#lint_axioms BoringMath.qmk_zero
#lint_axioms BoringMath.qmk_one
#lint_axioms BoringMath.qadd_assoc_int
#lint_axioms BoringMath.qmul_assoc_int
#lint_axioms BoringMath.mul_add_int
#lint_axioms BoringMath.qadd_comm
#lint_axioms BoringMath.qmul_comm
#lint_axioms BoringMath.qadd_zero
#lint_axioms BoringMath.qmul_one
#lint_axioms BoringMath.qadd_left_neg
#lint_axioms BoringMath.qadd_assoc
#lint_axioms BoringMath.qmul_assoc
#lint_axioms BoringMath.mul_add
#lint_axioms BoringMath.qmul_inv_cancel
