/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Data.List.Basic
import Mathlib.CategoryTheory.Category.Basic

/-!
# Computads (1-dimensional) — the foundational primitive — ticket #391

A **computad** (Street): a port monoid carried as *explicit data*, plus objects
(0-cells) and generators (1-cells) with source/target and port lists. This
mirrors the lab's experimental `BoringLab.Doctrine.Computad` (which cannot be
imported here — the dependency runs Lab → Math) so the two can later be proved
equivalent. Categories are the special case (`Computad.ofCategory`, #392).

## References
* [Street] R. Street, "The algebra of oriented simplexes" (computads);
  [Makkai] computads as presentations of higher categories.
* Lab: `BoringLab/Doctrine/Computad.lean` (experimental mirror).
-/

namespace BoringMath

universe u

-- Reference: [Street]; lab `BoringLab.Doctrine.Computad` (same field shape).
/-- A **1-dimensional computad**: port monoid as explicit data, objects, and
generators with source/target and left/right port lists. -/
structure Computad where
  /-- The port universe. -/
  port : Type u
  /-- The monoid product on ports. -/
  portMul : port → port → port
  /-- The unit port. -/
  portOne : port
  /-- Associativity of the port product. -/
  portMul_assoc : ∀ a b c : port, portMul a (portMul b c) = portMul (portMul a b) c
  /-- Left unit law. -/
  portMul_left_one : ∀ a : port, portMul portOne a = a
  /-- Right unit law. -/
  portMul_right_one : ∀ a : port, portMul a portOne = a
  /-- Objects (0-cells). -/
  obj : Type u
  /-- Generators (1-cells). -/
  gen : Type u
  /-- Source of a generator. -/
  src : gen → obj
  /-- Target of a generator. -/
  tgt : gen → obj
  /-- Left ports of a generator. -/
  leftPorts : gen → List port
  /-- Right ports of a generator. -/
  rightPorts : gen → List port

-- Reference: the terminal computad.
/-- The **trivial computad**: unit ports, one object, one identity generator. -/
def Computad.trivial : Computad.{u} where
  port := ULift.{u} Unit
  portMul := fun _ _ => ⟨()⟩
  portOne := ⟨()⟩
  portMul_assoc := fun _ _ _ => rfl
  portMul_left_one := fun _ => rfl
  portMul_right_one := fun _ => rfl
  obj := ULift.{u} Unit
  gen := ULift.{u} Unit
  src := fun _ => ⟨()⟩
  tgt := fun _ => ⟨()⟩
  leftPorts := fun _ => []
  rightPorts := fun _ => []

-- Reference: [Street]; a map of computads preserves ports, objects, generators
-- and the incidence/port structure. Full preservation laws land with #392.
/-- A **map of computads**. -/
structure Computad.Map (c d : Computad.{u}) where
  /-- On ports. -/
  port : c.port → d.port
  /-- On objects. -/
  obj : c.obj → d.obj
  /-- On generators. -/
  gen : c.gen → d.gen
  /-- Preserves the port monoid (statement-level, refined in #392). -/
  port_mul : ∀ a b, port (c.portMul a b) = d.portMul (port a) (port b)
  /-- Preserves sources. -/
  src : ∀ g, obj (c.src g) = d.src (gen g)
  /-- Preserves targets. -/
  tgt : ∀ g, obj (c.tgt g) = d.tgt (gen g)

-- Reference: [Street]; ticket #392, easy direction (categories are the
-- degenerate case of computads). Probe-verified at the pin; recorded in
-- SCIENCE.REVIEW.0 #351 acceptance (d).
/-- **Every category is a computad**: the unit port monoid (`ULift Unit`),
objects are the category's objects, generators are the arrows (a sigma over
pairs of objects), with empty port lists. The other direction
(`presentedCategory`, the free category on a computad, with unit/counit) is
the remaining half of #392. -/
def Computad.ofCategory (C : Type u) [CategoryTheory.Category.{u} C] : Computad.{u} where
  port := ULift.{u} Unit
  portMul := fun _ _ => ⟨()⟩
  portOne := ⟨()⟩
  portMul_assoc := fun _ _ _ => rfl
  portMul_left_one := fun _ => rfl
  portMul_right_one := fun _ => rfl
  obj := C
  gen := Σ (p : C × C), Quiver.Hom p.1 p.2
  src := fun g => g.1.1
  tgt := fun g => g.1.2
  leftPorts := fun _ => []
  rightPorts := fun _ => []

end BoringMath
