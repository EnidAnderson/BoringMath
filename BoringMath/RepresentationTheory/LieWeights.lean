/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Algebra.Lie.Weights.Basic
import Mathlib.Algebra.Lie.Semisimple.Defs

/-!
# Lie-module weights and semisimplicity (house naming over the pin)

RepresentationTheory ticket #345 (REP.LIE.2 seed). The pin `v4.35.0-rc3`
carries Lie-module weight spaces (`LieModule.weightSpace`), root systems and
Cartan subalgebras (`Algebra/Lie/Weights/*`), the Killing form and Cartan's
criterion, and the definition of semisimplicity (`LieAlgebra.IsSemisimple`).
Not yet at the pin: highest-weight modules / Verma modules, and Weyl's
complete reducibility — those are the gaps tickets #345/#346 fill.

Program role: representations of semisimple Lie algebras are the prototype of
the Tannakian mechanism (`Rep(𝔤) ≃ Rep(G)`, ticket #347): weight spaces are
the graded pieces, the Weyl group acts on weights — the same socle/graded
picture as in the motivic dictionary (#262).

## References
* mathlib pin v4.35.0-rc3: `LieModule.weightSpace`, `LieModule.mem_weightSpace`,
  `LieAlgebra.IsSemisimple`.
* [Bourbaki] *Lie Groups and Lie Algebras*, ch. VII–VIII (weights, ch. VIII
  §2 for highest weight theory).
* [Humphreys] *Introduction to Lie Algebras and Representation Theory*, GTM 9,
  ch. VII (weights), ch. VI (complete reducibility is NOT at the pin — #346).
* Program register: BoringMath #345–#348.
-/

namespace BoringMath

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

-- Reference: mathlib pin v4.35.0-rc3, `LieModule.mem_weightSpace`; [Bourbaki]
-- ch. VII §1.
/-- **Weight space membership**: `m` has weight `χ` iff every `x` acts on `m`
by the scalar `χ x` (proved). -/
theorem mem_weightSpace (χ : L → R) (m : M) :
    m ∈ LieModule.weightSpace M χ ↔ ∀ x, ⁅x, m⁆ = χ x • m :=
  LieModule.mem_weightSpace χ m

end BoringMath
