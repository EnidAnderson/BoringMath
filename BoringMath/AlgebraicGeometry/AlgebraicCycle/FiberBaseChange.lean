/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringMath.AlgebraicGeometry.AlgebraicCycle.FiberCycle
import BoringMath.AlgebraicGeometry.Fiber.BaseChange

/-!
# The fiber cycle under base change

The fiber cycle of a base change is supported on the preimage of the fiber:
for a cartesian square, every point of the support of the fiber cycle of
the vertical morphism maps under the cartesian map into the set-theoretic
fiber of the given morphism at the image point.

## References
* W. Fulton, *Intersection Theory*, ch. 1 (the support of the flat
  pullback of a point cycle: the fiber cycle under base change).
  REVIEW(citation): pin down the section.
-/

universe u

namespace AlgebraicGeometry

open CategoryTheory

namespace AlgebraicCycle

variable {P X Y Z : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}

-- Reference: W. Fulton, *Intersection Theory*, ch. 1 (the fiber cycle of a
-- base change is supported on the preimage of the fiber).
-- REVIEW(citation): pin down the section.
/-- **The fiber cycle of a base change is supported on the preimage of the
fiber**: for a cartesian square and a point of the base, every point of
the support of the fiber cycle of the vertical morphism maps under the
cartesian map into the set-theoretic fiber of the given morphism at the
image point. -/
theorem support_fiberCycle_baseChange (h : IsPullback fst snd f g) (y : Y)
    [IsNoetherian (Scheme.Hom.fiber snd y)] :
    (fiberCycle snd y).support ⊆
      fst.base ⁻¹' (Set.range (f.fiberι (g y)).base) := by
  intro x hx
  obtain ⟨η', _, rfl⟩ := (Set.mem_image (snd.fiberι y).base
      (Scheme.fundamentalCycle (Scheme.Hom.fiber snd y)).support x).mp
      (support_fiberCycle snd y hx)
  refine (Set.mem_preimage.mpr (Set.mem_range.mpr
    ⟨fiberBaseChange h y η', ?_⟩))
  exact congrArg (fun φ => φ η') (fiberBaseChange_fiberι h y)

end AlgebraicCycle

end AlgebraicGeometry
