/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.Algebra.Order.Monoid.Defs

/-!
# Motivic Holographic Information — the Physics folder's primitive — ticket #356

The top-down framework of `BoringMath/Physics/` (see `docs/PHYSICS-ROADMAP.md`):
a **Motivic Holographic Information** system bundles a *bulk* phase category,
a *boundary* site, a *holographic functor* `bulk ⥤ boundary`, and an
*information measure* into an ordered commutative monoid, subject to the
**holographic equation** `boundaryInfo (hologram.obj x) = bulkInfo x` — the
bulk's information is exactly what the boundary records. Every area of physics
is a specialization of this structure (computad-style: framework first,
special cases after).

Crank-free: no `axiom`; all fields are data or `Prop`; two calibrations are
proved below (trivial, and a two-point toy).

## References
* [’t Hooft 1993]; [Susskind 1995] (holographic principle).
* [Schreiber], *Differential cohomology in a cohesive ∞-topos* (the higher
  framework this adapts to 1-categorical computable carriers).
* Lab: `BoringLab/Physical/PhysicalDoctrine.lean` (PHYS.0) for the style;
  MI.0.1 (#67) for the motivic-information reading.
-/

namespace BoringMath

-- Reference: [’t Hooft 1993]; [Susskind 1995]; [Schreiber]; lab PHYS.0 / MI.0.1.
/-- A **Motivic Holographic Information** system: bulk phase category with a
unit interface, boundary site, the holographic functor, and an
information-valued measure on both sides satisfying the holographic equation. -/
structure MotivicHolographicInfo where
  /-- The bulk: the category of bulk phases/processes. -/
  bulk : Type u
  /-- The category instance on the bulk. -/
  [bulkCategory : Category.{v} bulk]
  /-- The distinguished unit/interface object of the bulk. -/
  bulkUnit : bulk
  /-- The boundary: the category on which the hologram lives. -/
  boundary : Type u₁
  /-- The category instance on the boundary. -/
  [boundaryCategory : Category.{v₁} boundary]
  /-- The holographic functor: bulk data projects to boundary data. -/
  hologram : bulk ⥤ boundary
  /-- The information/resource monoid (ordered commutative monoid). -/
  info : Type w
  /-- Commutative monoid instance on `info`. -/
  [infoCommMonoid : CommMonoid info]
  /-- Preorder on `info`. -/
  [infoPreorder : Preorder info]
  /-- Multiplication in `info` is monotone (the ordered-monoid law). -/
  [infoOrderedMonoid : IsOrderedMonoid info]
  /-- Information content of a bulk state. -/
  bulkInfo : bulk → info
  /-- Information content of a boundary state. -/
  boundaryInfo : boundary → info
  /-- **The holographic equation**: the boundary records exactly the bulk's
  information — no information is lost or created at the hologram. -/
  holographicEq : ∀ x : bulk, boundaryInfo (hologram.obj x) = bulkInfo x
  /-- Locality on the boundary: a coverage (raw locality, as in PHYS.0's P3). -/
  boundaryLocality : CategoryTheory.Coverage boundary

-- Reference: [’t Hooft 1993] (holographic principle); the terminal calibration,
-- as in PHYS.0's `trivialDoctrine`.
/-- The **trivial MHI**: one-object bulk and boundary, `ℕ` as information. -/
def trivialMHI : MotivicHolographicInfo.{0, 0, 0, 0, 0, 0} where
  bulk := Discrete Unit
  bulkUnit := Discrete.mk ()
  boundary := Discrete Unit
  hologram := 𝟭 (Discrete Unit)
  info := ℕ
  bulkInfo := fun _ => 0
  boundaryInfo := fun _ => 0
  holographicEq := fun _ => rfl
  boundaryLocality := (CategoryTheory.GrothendieckTopology.trivial _).toCoverage

-- Reference: the toy calibration: two-point bulk and boundary, information =
-- the point's value in `ℕ`.
/-- The **two-point toy MHI**: bulk = boundary = `Discrete (Fin 2)`, identity
hologram, information = `Fin.val`. -/
def toyMHI : MotivicHolographicInfo.{0, 0, 0, 0, 0, 0} where
  bulk := Discrete (Fin 2)
  bulkUnit := Discrete.mk 0
  boundary := Discrete (Fin 2)
  hologram := 𝟭 (Discrete (Fin 2))
  info := ℕ
  bulkInfo := fun b => b.unbox.val
  boundaryInfo := fun b => b.unbox.val
  holographicEq := fun _ => rfl
  boundaryLocality := (CategoryTheory.GrothendieckTopology.trivial _).toCoverage

end BoringMath
