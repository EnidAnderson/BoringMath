/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.GroupTheory.DoubleCoset

/-!
# BN-pairs (Tits systems) — the Lie-type classification tool

Ticket CFSG.LIB.bnpair (#251). A **BN-pair** in `G` is a pair of subgroups
`B` (the Borel) and `N` with `B ∩ N ⊴ N`, together with a set `S ⊆ N` of
simple reflections, satisfying the Bruhat axioms. Tits' theorem: a thick
irreducible BN-pair of rank ≥ 3 comes from a group of Lie type. mathlib at the
pin has Coxeter groups and double cosets but no BN-pairs.

## References
* [Tits] J. Tits, *Buildings of spherical type and finite BN-pairs*, Springer
  LNM 386, 1974, ch. 1 (axioms).
* [GLS] Number 3 (BN-pairs in the Lie-type sector).
* mathlib pin v4.35.0-rc3: `DoubleCoset.doubleCoset`, Coxeter groups
  (GroupTheory/Coxeter).
-/

namespace BoringMath

open Subgroup
open scoped Pointwise

variable {G : Type*} [Group G]

-- Reference: [Tits] LNM 386, ch. 1 (definition of a BN-pair; the Bruhat
-- decomposition axiom BN1). REVIEW(citation): pin the exact axioms (BN2, BN3)
-- against Tits ch. 1 when the Coxeter group `W` is attached.
/-- A **BN-pair** in `G`: subgroups `B` (Borel) and `N`, a set `S ⊆ N` of simple
reflections, `B ∩ N ⊴ N`, and the Bruhat axiom (BN1) on double cosets. -/
structure BNPairs (G : Type*) [Group G] where
  /-- The Borel subgroup. -/
  B : Subgroup G
  /-- The `N` of the BN-pair. -/
  N : Subgroup G
  /-- The simple reflections, contained in `N`. -/
  S : Set G
  /-- `S` lies in `N`. -/
  S_sub_N : S ⊆ (N : Set G)
  /-- `B ∩ N` is normal in `N` (relative normality, as a Prop). -/
  BN_normal : ∀ n : G, n ∈ N → ∀ x : G, x ∈ B ⊓ N → n * x * n⁻¹ ∈ B ⊓ N
  /-- **Bruhat axiom (BN1)**: `B w B · B s B ⊆ B w s B ∪ B w B` for `w ∈ N`,
  `s ∈ S`. -/
  bruhat : ∀ w : G, w ∈ N → ∀ s : G, s ∈ S →
    DoubleCoset.doubleCoset w (B : Set G) (B : Set G) *
      DoubleCoset.doubleCoset s (B : Set G) (B : Set G) ⊆
      DoubleCoset.doubleCoset (w * s) (B : Set G) (B : Set G) ∪
        DoubleCoset.doubleCoset w (B : Set G) (B : Set G)

end BoringMath
