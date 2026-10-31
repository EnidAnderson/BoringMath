/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.CategoryTheory.Sites.GlobalSections
import Mathlib.CategoryTheory.Sites.LeftExact

/-!
# Universe-polymorphic global sections of sheaves of types

This module addresses the TODO in the module docstring of
`Mathlib.CategoryTheory.Sites.GlobalSections.lean` (Eltschig), quoted verbatim
in issue #44:

> TODO: Generalise `Sheaf.ΓNatIsoSectionsFunctor` and
> `Sheaf.ΓNatIsoCoyoneda` from `Type max u v` to `Type max u v w`. This should
> hopefully be doable by relaxing the universe constraints of
> `instHasSheafifyOfHasFiniteLimits`.

Per the coordination flag in issue #44 the route is purely additive: no
existing Mathlib instance is edited. This file adds a new instance
`hasWeakSheafify_types_of_hasFiniteLimits_of_small_covers` supplying
`HasWeakSheafify J (Type (max u v w))` at general universes under an explicit
finite-limits hypothesis and an explicit smallness hypothesis on the covers,
and then the two generalized natural isomorphisms
`Sheaf.ΓNatIsoSectionsFunctorPoly` and `Sheaf.ΓNatIsoCoyonedaPoly` at
`Type (max u v w)`.

GOLD notes at pin v4.35.0-rc3 (mathlib commit c55e6e78): the TODO's
`instHasSheafifyOfHasFiniteLimits` is the anonymous instance
`[PreservesLimits (forget D)] [HasFiniteLimits D] [∀ X : C, Small.{t, max u v}
(J.Cover X)ᵒᵖ] : HasSheafify J D` (`Sites/LeftExact.lean`, `universe s t w' w v u`,
`{C : Type u} [Category.{v} C]`, `{D : Type w} [Category.{t} D]`), and
`J.Cover X : Type (max u v)` (`Sites/Grothendieck.lean`). For
`D = Type (max u v w)` every hypothesis of that instance except
`Small.{max u v w, max u v} (J.Cover X)ᵒᵖ` is already an instance; the new
instance below takes exactly that smallness (plus finite limits, mirroring the
upstream hypothesis shape) explicitly. At the pin, `HasWeakSheafify J
(Type (max u v w))` is in fact already synthesized unconditionally via
`sheafToPresheaf_isRightAdjoint` (priority 900, `Sites/ConcreteSheafification.lean`),
so the two natural isomorphisms below need no extra hypotheses; the new
instance does not collide at overlapping universes because `HasWeakSheafify`
is a `Prop` (proof irrelevance), verified by probes at `Type (max u v)`.

## References
* [Eltschig] B. Eltschig, `Mathlib.CategoryTheory.Sites.GlobalSections` (2025),
  the TODO anchor, read in full at the pin.
* [Stacks] The Stacks Project, Chapter 7 "Sites and Sheaves" (tag 00UZ).
* [MM] S. Mac Lane, I. Moerdijk, *Sheaves in Geometry and Logic*, Springer,
  1992, Chapter III (the associated sheaf functor).
* [Mac Lane] S. Mac Lane, *Categories for the Working Mathematician*, 2nd ed.,
  Springer, 1998, Chapter IV (adjoints).
-/

universe u v w

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

-- Reference: [MM], Chapter III, §6 (the plus construction, i.e. the associated
-- sheaf functor); [Stacks], Chapter 7 "Sites and Sheaves" (tag 00UZ), §7.10.
-- REVIEW(citation): exact section pins owned by W5/#13 per issue #44.
/-- Weak sheafification exists for presheaves of types in `Type (max u v w)`
when the target has finite limits and the covering posets `J.Cover X` are
small in `Type (max u v)`, mirroring the hypothesis shape of Mathlib's
`HasSheafify` instance for concrete categories (`Sites/LeftExact.lean`). -/
instance hasWeakSheafify_types_of_hasFiniteLimits_of_small_covers
    [Limits.HasFiniteLimits (Type (max u v w))]
    [∀ X : C, Small.{max u v w, max u v} (J.Cover X)ᵒᵖ] :
    HasWeakSheafify J (Type (max u v w)) :=
  have h : HasSheafify J (Type (max u v w)) :=
    HasSheafify.mk' J (Type (max u v w)) (plusPlusAdjunction J (Type (max u v w)))
  h.isRightAdjoint

-- Reference: [Eltschig], `Sheaf.ΓNatIsoSectionsFunctor` in
-- `Mathlib.CategoryTheory.Sites.GlobalSections` (the TODO of issue #44);
-- [Mac Lane], Chapter IV, §1 (natural isomorphisms of adjoint functors).
-- REVIEW(citation): exact section pins owned by W5/#13 per issue #44.
/-- For sheaves of types in `Type (max u v w)`, the global sections functor is
naturally isomorphic to the sections functor of the underlying presheaf. This
generalizes `Sheaf.ΓNatIsoSectionsFunctor` from `Type (max u v)` to
`Type (max u v w)`. -/
noncomputable def Sheaf.ΓNatIsoSectionsFunctorPoly :
    Sheaf.Γ J (Type (max u v w)) ≅ sheafToPresheaf J _ ⋙ Functor.sectionsFunctor _ :=
  NatIso.ofComponents (fun F ↦ (Sheaf.ΓObjEquivSections J F).toIso) fun f ↦
    ConcreteCategory.ext_apply (fun x => Sheaf.ΓObjEquivSections_naturality J f x)

-- Reference: [Eltschig], `Sheaf.ΓNatIsoCoyoneda` in
-- `Mathlib.CategoryTheory.Sites.GlobalSections` (the TODO of issue #44);
-- [Mac Lane], Chapter IV, §1 (adjoints and representable functors).
-- REVIEW(citation): exact section pins owned by W5/#13 per issue #44.
/-- For sheaves of types in `Type (max u v w)`, the global sections functor is
naturally isomorphic to the coyoneda embedding of a terminal (constant) sheaf.
This generalizes `Sheaf.ΓNatIsoCoyoneda` from `Type (max u v)` to
`Type (max u v w)`. -/
noncomputable def Sheaf.ΓNatIsoCoyonedaPoly (X : Type (max u v w)) [Unique X] :
    Sheaf.Γ J (Type (max u v w)) ≅
      coyoneda.obj (Opposite.op ((constantSheaf J (Type (max u v w))).obj X)) :=
  NatIso.ofComponents (fun F ↦ (Sheaf.ΓObjEquivHom J F X).toIso) fun f ↦
    ConcreteCategory.ext_apply (fun x => Sheaf.ΓObjEquivHom_naturality J X f x)

end CategoryTheory
