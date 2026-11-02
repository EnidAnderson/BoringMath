/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.FinGroupCharZero
import Mathlib.RepresentationTheory.Induced

/-!
# Finite-group characters and Frobenius reciprocity (house naming over the pin)

RepresentationTheory tickets #315 (characters) and #316 (induction/restriction).
The pin `v4.35.0-rc3` already carries the character API
(`RepresentationTheory/Character.lean`, `FinGroupCharZero.lean`) and the
induction–restriction adjunction (`RepresentationTheory/Induced.lean`); this
module restates the load-bearing facts in the house naming so later CFSG and
motives modules cite one place. Everything here is proved — direct
specializations of the pin.

## References
* mathlib pin v4.35.0-rc3: `FDRep.char_one`, `FDRep.char_conj`,
  `FDRep.isIntegral_character`, `FDRep.average_char_eq_finrank_invariants`,
  `FDRep.char_orthonormal`, `FDRep.simple_iff_char_is_norm_one`,
  `Rep.indResHomEquiv`, `Rep.indResAdjunction`.
* [Isaacs] ch. 2 (orthogonality relations), ch. 6 (induction, Frobenius
  reciprocity).
* [Serre] Part I, ch. 2–3.
-/

namespace BoringMath

universe u v

variable {k : Type u} [Field k] {G : Type u} [Group G]

-- Reference: mathlib pin v4.35.0-rc3, `FDRep.char_one`; [Serre] §2.3.
/-- The character at the identity is the dimension (proved). -/
theorem char_one_eq_finrank (V : FDRep k G) :
    V.character 1 = Module.finrank k V :=
  FDRep.char_one V

-- Reference: mathlib pin v4.35.0-rc3, `FDRep.char_conj`; [Isaacs] §2.6
-- (characters are class functions).
/-- Characters are class functions (proved). -/
theorem char_conj (V : FDRep k G) (g h : G) :
    V.character (h * g * h⁻¹) = V.character g :=
  FDRep.char_conj V g h

-- Reference: mathlib pin v4.35.0-rc3, `FDRep.isIntegral_character`; [Isaacs]
-- §3.3 (character values are sums of roots of unity).
/-- Character values are integral over `ℤ` (proved). -/
theorem char_isIntegral [Finite G] (V : FDRep k G) (g : G) :
    IsIntegral ℤ (V.character g) :=
  FDRep.isIntegral_character V g

-- Reference: mathlib pin v4.35.0-rc3,
-- `FDRep.average_char_eq_finrank_invariants`; [Serre] §2.4 (projection onto
-- invariants).
/-- The averaged character is the dimension of the invariant subspace
(proved). -/
theorem average_char_eq_finrank_invariants [Fintype G] [Invertible (Nat.card G : k)]
    (V : FDRep k G) :
    (Nat.card G : k)⁻¹ * ∑ g : G, V.character g =
      Module.finrank k (Representation.invariants V.ρ) :=
  FDRep.average_char_eq_finrank_invariants V

open scoped Classical in
-- Reference: mathlib pin v4.35.0-rc3, `FDRep.char_orthonormal`; [Isaacs]
-- Theorem 2.18 (first orthogonality relation).
/-- **First orthogonality relation** for irreducible characters (proved). -/
theorem char_orthonormal [IsAlgClosed k] [Fintype G] [Invertible (Nat.card G : k)]
    (V W : FDRep k G) [CategoryTheory.Simple V] [CategoryTheory.Simple W] :
    (Nat.card G : k)⁻¹ * ∑ g : G, V.character g * W.character g⁻¹ =
      if Nonempty (V ≅ W) then ↑1 else ↑0 :=
  FDRep.char_orthonormal V W

-- Reference: mathlib pin v4.35.0-rc3, `FDRep.simple_iff_char_is_norm_one`;
-- [Isaacs] Corollary 2.30 (irreducibility criterion).
/-- **Irreducibility criterion**: over an algebraically closed field of
characteristic zero, `V` is simple iff the norm of its character is `1`
(proved). -/
theorem simple_iff_char_norm_one [CharZero k] [IsAlgClosed k] [Fintype G] (V : FDRep k G) :
    CategoryTheory.Simple V ↔ ∑ g : G, V.character g * V.character g⁻¹ = Nat.card G :=
  FDRep.simple_iff_char_is_norm_one V

variable {H : Type u} [Group H]

-- Reference: mathlib pin v4.35.0-rc3, `Rep.indResHomEquiv`;
-- [Isaacs] Theorem 6.3 / [Serre] §7.1.
/-- **Frobenius reciprocity**: `Hom_H(ind φ A, B) ≃ₗ Hom_G(A, res φ B)`
(proved). -/
noncomputable def frobeniusEquiv (φ : G →* H) (A : Rep k G) (B : Rep k H) :
    (Rep.ind φ A ⟶ B) ≃ₗ[k] (A ⟶ Rep.res φ B) :=
  Rep.indResHomEquiv φ A B

-- Reference: mathlib pin v4.35.0-rc3, `Rep.indResAdjunction`.
/-- Induction is left adjoint to restriction (proved). -/
noncomputable def indResAdjunction (φ : G →* H) :
    Rep.indFunctor k φ ⊣ Rep.resFunctor φ :=
  Rep.indResAdjunction k φ

end BoringMath
