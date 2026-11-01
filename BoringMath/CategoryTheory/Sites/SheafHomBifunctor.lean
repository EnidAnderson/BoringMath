/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringMath.CategoryTheory.Sites.SheafHomBifunctor.Bifunctor
import BoringMath.CategoryTheory.Sites.SheafHomBifunctor.Curry
import BoringMath.CategoryTheory.Sites.SheafHomBifunctor.Adjunction

/-!
# The `sheafHom` bifunctor and the product adjunction for sheaves of types

This module addresses the TODO in the module docstring of
`Mathlib.CategoryTheory.Sites.SheafHom.lean` (Riou), quoted verbatim in
issue #41:

> TODO: turn both `presheafHom` and `sheafHom` into bifunctors; for a sheaf
> of types `F`, the `sheafHom` functor from `F` is right-adjoint to the product
> functor with `F`, i.e. for all `X` and `Y`, there is a natural bijection
> `(X ⨯ F ⟶ Y) ≃ (X ⟶ sheafHom F Y)`; use these results in order to show that
> the category of sheaves of types is Cartesian closed.

The three peels:

* Peel (a): `presheafHomBifunctor` and `sheafHomBifunctor` — the hom presheaf
  and the hom sheaf as bifunctors (contravariant in the first variable).
* Peel (b): `sheafHomAdjunction` — `(- ⨯ F) ⊣ sheafHom F` for sheaves of
  types, built from the bijection `sheafHomProdHomEquiv`.
* Peel (c): `Sheaf J (Type (max u v))` is Cartesian closed; at this pin
  "Cartesian closed" means `CartesianMonoidalCategory` together with
  `MonoidalClosed` (see `Mathlib.CategoryTheory.Monoidal.Closed.Cartesian`),
  and the internal hom is `sheafHom` (`sheafHom_iso_internalHom`).

Universe note: for `A := Type (max u v)` the category instance
`CategoryTheory.types : Category.{w} (Type w)` puts `v' = max u v`, so
`sheafHom F G : Sheaf J (Type (max u v))` lands in the same category
(`max u v v'` reduces to `max u v`).

## References
* [Riou] J. Riou, `Mathlib.CategoryTheory.Sites.SheafHom` (the TODO above).
* [SGA4] A. Grothendieck et al., *Éléments de géométrie algébrique IV*,
  Publ. Math. IHÉS 32 (1967), Exposé I.
* [Stacks] The Stacks Project, Chapter 7 "Sites and Sheaves" (tag 00UZ),
  §7.7 "Sheaves" (tag 00VL).
* [MM] S. Mac Lane, I. Moerdijk, *Sheaves in Geometry and Logic*, Springer,
  1992, Chapter I.
* [Mac Lane] S. Mac Lane, *Categories for the Working Mathematician*, 2nd ed.,
  Springer, 1998, Chapter IV (Adjoints).
-/
