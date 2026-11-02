/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.AlgebraicGeometry.Scheme

/-!
# Application of scheme morphisms to points

The coercion of a scheme morphism to a function on points
(`instance : CoeFun (X ⟶ Y) (fun _ ↦ X → Y)`, `coe f := f.base`), its
composition law (`Scheme.Hom.comp_apply`, mathlib), and the identity law.

## References
* Stacks Project, Schemes, Def. 26.6.4? (morphisms of schemes act on
  underlying topological points) — REVIEW(citation): pin the tag.
-/

universe u

namespace AlgebraicGeometry

open CategoryTheory

namespace Scheme

namespace Hom

-- Reference: primitive definitional lemma (STYLE §5, eta discipline),
-- sibling of mathlib's `Scheme.Hom.comp_apply`: the identity morphism of a
-- scheme is the identity on points.
/-- The identity morphism of a scheme acts as the identity on points. -/
theorem id_apply {X : Scheme.{u}} (x : ↥X) : (𝟙 X : X ⟶ X) x = x := rfl

end Hom

end Scheme

end AlgebraicGeometry
