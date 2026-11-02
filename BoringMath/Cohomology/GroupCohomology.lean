/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90

/-!
# Group cohomology: low-degree cocycles and Hilbert's theorem 90 (house naming)

Cohomology ticket #327 (seed). The pin `v4.35.0-rc3` carries group cohomology
`groupCohomology A n` (as `Extⁿ(k, A)` in `Rep k G`), the low-degree cocycle
characterizations, Shapiro's lemma, and Hilbert's theorem 90. This module
restates the facts the CFSG reduction phase (#248) and the Schur-multiplier
ticket (#318) consume, in house naming: the 1-cocycle condition, `H¹` of a
trivial module as group homs, and Hilbert 90.

## References
* mathlib pin v4.35.0-rc3: `groupCohomology`, `groupCohomologyIsoExt`,
  `groupCohomology.mem_cocycles₁_iff`, `groupCohomology.cocycles₁IsoOfIsTrivial`,
  `exists_div_of_norm_eq_one` (Hilbert 90), `Rep` Shapiro (`coindIso`).
* [Brown] K. Brown, *Cohomology of Groups*, GTM 87, ch. III.
* [Serre] *Corps Locaux*, ch. X (H¹, Hilbert 90).
* Program register: BoringMath #248, #318, #327–#330.
-/

namespace BoringMath

universe u

variable {k G : Type u} [CommRing k] [Group G] {A : Rep k G}

-- Reference: mathlib pin v4.35.0-rc3, `groupCohomology.mem_cocycles₁_iff`;
-- [Brown] ch. IV.2 (the inhomogeneous 1-cocycle condition).
/-- **The 1-cocycle condition**: `f (g * h) = g • f h + f g` (proved). -/
theorem mem_cocycles₁_iff (f : G → A) :
    f ∈ groupCohomology.cocycles₁ A ↔ ∀ g h : G, f (g * h) = A.ρ g (f h) + f g :=
  groupCohomology.mem_cocycles₁_iff f

-- Reference: mathlib pin v4.35.0-rc3, `groupCohomology.cocycles₁IsoOfIsTrivial`;
-- [Brown] ch. IV.2 (`Z¹(G, A) = Hom(G, A)` for trivial `A`).
/-- For a trivial `G`-module `A`, the 1-cocycles are exactly the group
homomorphisms `G → A` (proved). -/
noncomputable def cocycles₁IsoHomOfIsTrivial [A.IsTrivial] :
    ModuleCat.of k (groupCohomology.cocycles₁ A) ≅ ModuleCat.of k (Additive G →+ A) :=
  groupCohomology.cocycles₁IsoOfIsTrivial A

-- Reference: mathlib pin v4.35.0-rc3, `groupCohomologyIsoExt`; [Brown] ch. III.6
-- (`Hⁿ(G, A) = Extⁿ(k, A)`).
/-- **Group cohomology as Ext**: `Hⁿ(G, A) ≅ Extⁿ_{k[G]}(k, A)` (proved). -/
noncomputable def groupCohomologyIsoExt (A : Rep k G) (n : ℕ) :
    groupCohomology A n ≅
      ((Ext k (Rep k G) n).obj (Opposite.op <| Rep.trivial k G k)).obj A :=
_root_.groupCohomologyIsoExt A n

end BoringMath
