/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.RepresentationTheory.Tannaka
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RepresentationTheory.Semisimple

/-!
# Tannaka reconstruction for finite groups, and semisimplicity (Maschke)

RepresentationTheory tickets #131 (Tannakian reconstruction, finite-group case)
and the semisimplicity backbone (#315). The pin `v4.35.0-rc3` proves Tannaka
duality for finite groups (`TannakaDuality.FiniteGroup.equiv :
G ≃* Aut (forget k G)`) and Maschke's theorem; this module restates them in
house naming.

Program role (tickets #131/#348, REP.LIE.4–5): `FDRep k G` is the prototype of
a Tannakian category with Tannakian group `G`. The Lie-algebra analogue —
`Rep(𝔤)` symmetric monoidal with a fiber functor, `Rep(𝔤) ≃ Rep(G)` with
`Lie G = 𝔤` — is exactly the "Lurie-style" presentation of representations of
semisimple Lie algebras, and it is the model for the motivic row: motives form
a Tannakian category with the much larger motivic Galois group, and simple
motives are consumed from the CFSG list via the socle mechanism (#262).

## References
* mathlib pin v4.35.0-rc3: `TannakaDuality.FiniteGroup.equiv`,
  `TannakaDuality.FiniteGroup.forget`, Maschke
  (`IsSemisimpleRepresentation`, `IsSemisimpleRing (AddMonoidAlgebra k G)`).
* [Deligne–Milne] *Tannakian Categories*, AMS 1982.
* [Commelin] Leiden bachelor thesis (Tannaka duality for finite groups),
  math.leidenuniv.nl/scripties/1bachCommelin.pdf.
* Program register: BoringMath #131, #262, #344–#348.
-/

namespace BoringMath

universe u

variable {k G : Type u} [CommRing k] [Group G]

-- Reference: mathlib pin v4.35.0-rc3, `TannakaDuality.FiniteGroup.equiv`;
-- [Deligne–Milne] §2.
/-- **Tannaka reconstruction for finite groups**: `G` is recovered as the
monoidal automorphism group of the forgetful functor `FDRep k G ⥤ FGModuleCat k`
(proved). -/
noncomputable def tannakaEquiv [IsDomain k] [Finite G] :
    G ≃* CategoryTheory.Aut (TannakaDuality.FiniteGroup.forget k G) :=
  TannakaDuality.FiniteGroup.equiv k G

variable {k : Type u} [Field k] {G : Type u} [Group G] [Finite G] [NeZero (Nat.card G : k)]

-- Reference: mathlib pin v4.35.0-rc3, Maschke's theorem
-- (`instIsSemisimpleRepresentation...`); [Serre] §1.2 / [Isaacs] §3.6.
/-- **Maschke's theorem**: every representation of a finite group whose order
is nonzero in `k` is semisimple (proved). -/
instance isSemisimpleRepresentation {V : Type u}
    [AddCommGroup V] [Module k V] (ρ : Representation k G V) [Module (MonoidAlgebra k G) V]
    [IsScalarTower k (MonoidAlgebra k G) V] : Representation.IsSemisimpleRepresentation ρ :=
  inferInstance

-- Reference: mathlib pin v4.35.0-rc3, Maschke (`IsSemisimpleRing
-- (AddMonoidAlgebra k G)`); [Serre] §1.2.
/-- **Maschke's theorem, ring form**: the group algebra `k[G]` is semisimple
when `|G|` is nonzero in `k` (proved). -/
instance monoidAlgebra_isSemisimpleRing :
    IsSemisimpleRing (MonoidAlgebra k G) :=
  inferInstance

end BoringMath
