/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Algebra.Lie.Classical
import Mathlib.Algebra.Lie.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import BoringMath.GroupTheory.Simple.Classification

/-!
# The Lie-algebra bridge for the Lie-type sector of the CFSG

Ticket CFSG.C (Lie-type sector, #215) meets the program's representation /
motivic thread: the finite simple groups of Lie type arise from the
**classical Lie algebras** (types A–D, exceptional) over finite fields, and
their character theory (Deligne–Lusztig) is built from representations of the
algebraic group — i.e. of the Lie algebra over `\bar F_q`. Mathlib at the pin
already has the classical Lie algebras `sl`, `so`, `sp` as matrix Lie
subalgebras over any commutative ring, and `LieModule` for their
representations.

This module fixes the concrete Lie-algebra side of the bridge (types A–D over
any commutative ring, with the type-A dimension over a field proved) and records
the bridge theorems' peeling plans (Chevalley construction; Deligne–Lusztig
character theory; the motivic-Galois dictionary row, labeled as a bet per the
honesty rules) — the statements themselves land as their objects are built.

## References
* [Carter] R. W. Carter, *Simple Groups of Lie Type*, Wiley 1972 (Chevalley
  construction from the ℤ-form of a complex simple Lie algebra, ch. 4–6).
* [DL] P. Deligne, G. Lusztig, *Representations of reductive groups over finite
  fields*, Ann. of Math. 103 (1976) 103–161 (characters of `G(F_q)` from
  representations of the dual group).
* [GLS] Gorenstein–Lyons–Solomon, *The Classification of the Finite Simple
  Groups*, Number 3 (Lie-type sector).
* mathlib pin v4.35.0-rc3: `LieAlgebra.SpecialLinear.sl`,
  `LieAlgebra.Orthogonal.so`, `LieAlgebra.Symplectic.sp` (Classical.lean),
  `LieModule` (Basic.lean), `Matrix.traceLinearMap`/`trace_surjective`
  (LinearAlgebra/Matrix/Trace.lean).
-/

namespace BoringMath

open Matrix

-- The matrix Lie ring structure is a local instance in mathlib's
-- `Algebra/Lie/Matrix.lean`; make it available here (standard pattern).
attribute [local instance 100] LieRing.ofAssociativeRing

/-! ## The classical Lie algebras (consumed from mathlib at the pin) -/

-- Reference: mathlib pin v4.35.0-rc3, `Mathlib/Algebra/Lie/Classical.lean`
-- (`LieAlgebra.SpecialLinear.sl`); [Carter] ch. 4 (type A_l = sl(l+1)).
/-- **Type A_l over `R`**: `sl(l+1, R)`, the Lie algebra of `SL(l+1, R)` —
the Lie-algebra side of the `PSL(l+1, q)` family of sector C. -/
abbrev lieAlgA (l : ℕ) (R : Type*) [CommRing R] :
    LieSubalgebra R (Matrix (Fin (l+1)) (Fin (l+1)) R) :=
  LieAlgebra.SpecialLinear.sl (Fin (l+1)) R

-- Reference: mathlib pin v4.35.0-rc3, `Classical.lean`
-- (`LieAlgebra.Orthogonal.so`); [Carter] ch. 4 (types B_l, D_l).
/-- **Type B_l over `R`**: `so(2l+1, R)`. -/
abbrev lieAlgB (l : ℕ) (R : Type*) [CommRing R] :
    LieSubalgebra R (Matrix (Fin (2*l+1)) (Fin (2*l+1)) R) :=
  LieAlgebra.Orthogonal.so (Fin (2*l+1)) R

-- Reference: mathlib pin v4.35.0-rc3, `Classical.lean`; [Carter] ch. 4.
/-- **Type D_l over `R`**: `so(2l, R)`. -/
abbrev lieAlgD (l : ℕ) (R : Type*) [CommRing R] :
    LieSubalgebra R (Matrix (Fin (2*l)) (Fin (2*l)) R) :=
  LieAlgebra.Orthogonal.so (Fin (2*l)) R

-- Reference: mathlib pin v4.35.0-rc3, `Classical.lean`
-- (`LieAlgebra.Symplectic.sp`); [Carter] ch. 4 (type C_l).
/-- **Type C_l over `R`**: `sp(2l, R)`, the symplectic Lie algebra. -/
abbrev lieAlgC (l : ℕ) (R : Type*) [CommRing R] :
    LieSubalgebra R (Matrix (Fin l ⊕ Fin l) (Fin l ⊕ Fin l) R) :=
  LieAlgebra.Symplectic.sp (Fin l) R

-- Reference: mathlib pin v4.35.0-rc3, `Classical.lean` (a `LieSubalgebra` carries
-- a `LieAlgebra` instance over `R`).
/-- Each classical type is a Lie algebra over the finite field `F_p` (the
`LieSubalgebra` instance, available by typeclass search). -/
example (l p : ℕ) [Fact p.Prime] : LieAlgebra (ZMod p) (lieAlgA l (ZMod p)) := inferInstance

/-! ## The type-A dimension over a field (proved) -/

-- Reference: mathlib pin v4.35.0-rc3, `Classical.lean` (`sl = ker trace`),
-- `Matrix.trace_surjective`, `LinearMap.finrank_range_add_finrank_ker`;
-- [Carter] ch. 4: `dim sl(n) = n^2 - 1`.
/-- **Dimension of `sl(n, K)`** over a field: `dim ker(trace) + 1 = n * n`
(proved by rank-nullity; `sl(n,K)` is the trace kernel). -/
theorem finrank_trace_ker (n : ℕ) [NeZero n] (K : Type*) [Field K] :
    Module.finrank K (LinearMap.ker (Matrix.traceLinearMap (Fin n) K K)) + 1 = n * n := by
  have hsurj : Function.Surjective (Matrix.traceLinearMap (Fin n) K K) := by
    intro r
    obtain ⟨A, hA⟩ := @Matrix.trace_surjective (Fin n) K _ _ ⟨0⟩ r
    exact ⟨A, hA⟩
  have hrange : (Matrix.traceLinearMap (Fin n) K K).range = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  have hfin := LinearMap.finrank_range_add_finrank_ker (Matrix.traceLinearMap (Fin n) K K)
  have hrangefin : Module.finrank K (Matrix.traceLinearMap (Fin n) K K).range = 1 :=
    Eq.subst (motive := fun (S : Submodule K K) => Module.finrank K S = 1) hrange.symm
      ((finrank_top K K).trans (Module.finrank_self K))
  have hdom : Module.finrank K (Matrix (Fin n) (Fin n) K) = n * n :=
    (Module.finrank_matrix K K (Fin n) (Fin n)).trans
      ((congrArg (fun c => c * Fintype.card (Fin n) * Module.finrank K K)
          (Fintype.card_fin n)).trans
        ((congrArg (fun c => n * c * Module.finrank K K) (Fintype.card_fin n)).trans
          ((congrArg (fun f => n * n * f) (Module.finrank_self K)).trans (Nat.mul_one (n * n)))))
  have h2 : 1 + Module.finrank K (LinearMap.ker (Matrix.traceLinearMap (Fin n) K K)) = n * n :=
    (congrArg (fun x => x + Module.finrank K (LinearMap.ker (Matrix.traceLinearMap (Fin n) K K)))
        hrangefin).symm.trans
      (hfin.trans hdom)
  exact Eq.subst (motive := fun t => t = n * n) (Nat.add_comm 1 _) h2

-- Reference: as `finrank_trace_ker`; the carrier of `sl(l+1, K)` is the trace
-- kernel (`Classical.lean`, def of `sl`).
/-- **Dimension of the type-A Lie algebra** `sl(l+1, K)` over a field:
`dim lieAlgA l K + 1 = (l+1)^2` (proved). This is the numerical interface
between sector C's `PSL(l+1, q)` and its Lie algebra. -/
theorem finrank_lieAlgA (l : ℕ) (K : Type*) [Field K] :
    Module.finrank K (lieAlgA l K) + 1 = (l + 1) * (l + 1) := by
  exact @finrank_trace_ker (l + 1) ⟨Nat.succ_ne_zero l⟩ K inferInstance

/-! ## The bridge theorems — peeling plans

The two bridge theorems below are the connection to the program's
representation/motivic core. Their precise statements land as the objects are
built (per STYLE §7); the plans:

* **Chevalley bridge** [Carter] ch. 4–6: from the ℤ-form of `lieAlgA l` (root
  vectors and divided powers — mathlib has root systems/weights in
  `Mathlib/Algebra/Lie/Weights`), exponentiating over `F_q` gives the Chevalley
  group, identified with `PSL(l+1, q)` of sector C (`Classification.lean`).
* **Deligne–Lusztig bridge** [DL]: the irreducible characters of `G(F_q)` are
  parametrized via `R_{T,θ}` from `LieModule` representations of the dual group
  over `\bar F_q` — building on the proved `finrank_lieAlgA`.
* **Motivic dictionary row (BET, not a theorem)**: the character table of the
  finite Lie-type group should carry a motivic Galois action (program register,
  T2 bet). Labeled as a bet per the honesty rules; first step is the
  representation ring of `lieAlgA l` over `ℚ` with its weight decomposition.
-/

end BoringMath
