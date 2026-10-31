/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
import BoringMath.AlgebraicGeometry.AlgebraicCycle.Zero
import BoringMath.AlgebraicGeometry.ResidueField.Tower

/-!
# The weight-general ring on `AlgebraicCycle.map`

Mathlib's `AlgebraicCycle.map` pushes a cycle along a quasicompact
morphism `f` with an arbitrary pair of weight functions `wx`, `wy`: the
coefficient at `z` is the fiber sum `∑ᶠ x ∈ f ⁻¹' {z}, c x * w x` with
weight `w x = mapCoeff f wx wy x`, i.e. the residue degree of `x` over
`f` when `wx x = wy (f x)` and `0` otherwise. This module fills out the
ring on `map` with arbitrary weights: the coefficient formula, the
fiber finiteness, `map_zero`, `map_add`, `map_single`, the bundled
`mapHom` with `mapHom_apply`, and the composition law `map_comp` under
the weight compatibility `wy (g x) = wz ((g ≫ h) x)` — the weight
bookkeeping the weight pair exists for — together with `mapCoeff_comp`
(the weight of a composite is the product of the weights, by the tower
law for residue degrees) and `mapHom_comp`.

## References
* Stacks Project, *Chow Homology*, Def. 42.8.1, tag 02QR (a cycle is a
  locally finite formal sum).
* Stacks Project, *Chow Homology*, §42.12, tag 02R3 (proper pushforward;
  Def. 42.12.1 = tag 02R4 carries the degree weight `deg(Z/f(Z)) [f(Z)]`;
  Lemma 42.12.2 = tag 02R5 is the composition law `g_* ∘ f_* = (g ∘ f)_*`).
* W. Fulton, *Intersection Theory*, ch. 1, §1.3 (push-forward).
  REVIEW(citation): pin down the section in review.
-/

universe u

namespace AlgebraicGeometry

open CategoryTheory

variable {X Y : Scheme.{u}} {R : Type*} [Semiring R]

namespace AlgebraicCycle

-- Reference: Stacks Project, Chow Homology, Def. 42.8.1, tag 02QR (a cycle
-- is a locally finite formal sum), and tag 02R4 (the weight of the
-- pushforward is the residue degree `deg(Z/f(Z))`).
/-- The coefficient of `AlgebraicCycle.map` at a point is the fiber sum of
the coefficients weighted by `mapCoeff`. -/
theorem map_apply (f : X ⟶ Y) [QuasiCompact f] {N : Type*} [DecidableEq N]
    (wx : X → N) (wy : Y → N) (c : AlgebraicCycle X R) (z : ↥Y) :
    map f wx wy c z = ∑ᶠ (x : ↥X) (_ : x ∈ f.base ⁻¹' {z}),
      c x * (mapCoeff f wx wy x : R) := rfl

-- Reference: Stacks Project, Chow Homology, Def. 42.8.1, tag 02QR (the
-- support of a cycle is locally finite, Topology Def. 5.28.4).
/-- The support of a cycle meets a fiber of a quasicompact morphism in a
finite set: any compact open neighbourhood of the point has compact
preimage under the spectral map, and the support meets a compact set
finitely. -/
theorem finite_support_inter_fiber_of_coeff (f : X ⟶ Y) [QuasiCompact f]
    {S : Type*} [Zero S] (c : AlgebraicCycle X S) (z : ↥Y) :
    (f.base ⁻¹' {z} ∩ c.support).Finite := by
  obtain ⟨U, hU⟩ :=
    (PrespectralSpace.isTopologicalBasis (X := ↥Y)).exists_subset_of_mem_open
      (Set.mem_univ z) isOpen_univ
  refine Set.Finite.subset
    (LocallyFiniteSupport.finite_inter_support_of_isCompact
      (Function.locallyFinsupp.locallyFiniteSupport c)
      (IsCompact.preimage_of_isOpen f.isSpectralMap hU.1.2 hU.1.1)) ?_
  intro x hx
  exact ⟨Set.mem_preimage.mpr
      (Eq.subst (Set.mem_singleton_iff.mp (Set.mem_preimage.mp hx.1)).symm
        hU.2.1),
    hx.2⟩

-- Reference: Stacks Project, Chow Homology, §42.12, tag 02R3 ("by definition
-- the proper pushforward of cycles is a homomorphism of abelian groups").
/-- The map of the zero cycle is the zero cycle: the weighted fiber sums
vanish termwise. -/
theorem map_zero (f : X ⟶ Y) [QuasiCompact f] {N : Type*} [DecidableEq N]
    (wx : X → N) (wy : Y → N) :
    map f wx wy (0 : AlgebraicCycle X R) = 0 := by
  refine Function.locallyFinsuppWithin.ext (fun z => ?_)
  refine Eq.trans (map_apply f wx wy (0 : AlgebraicCycle X R) z) ?_
  exact finsum_mem_of_eqOn_zero (fun _ _ => zero_mul _)

-- Reference: Stacks Project, Chow Homology, §42.12, tag 02R3 (the pushforward
-- is a homomorphism of abelian groups).
/-- The map is additive: the map of a sum of cycles is the sum of the maps
(pointwise multiplicities add, multiplication distributes, and the fiber
sums add by the fiber finiteness). -/
theorem map_add (f : X ⟶ Y) [QuasiCompact f] {N : Type*} [DecidableEq N]
    (wx : X → N) (wy : Y → N) (c d : AlgebraicCycle X R) :
    map f wx wy (c + d) = map f wx wy c + map f wx wy d := by
  refine Function.locallyFinsuppWithin.ext (fun z => ?_)
  -- a nonzero weighted term has a nonzero coefficient, so the weighted
  -- support in the fiber is finite
  have hfin : ∀ e : AlgebraicCycle X R,
      (f.base ⁻¹' {z} ∩ (fun x => e x * (mapCoeff f wx wy x : R)).support).Finite := by
    intro e
    refine Set.Finite.subset (finite_support_inter_fiber_of_coeff f e z) ?_
    intro x hx
    exact ⟨hx.1, Function.mem_support.mpr
      (fun he => (Function.mem_support.mp hx.2)
        (Eq.trans (congrArg₂ HMul.hMul he rfl) (zero_mul _)))⟩
  calc map f wx wy (c + d) z
      = ∑ᶠ (x : ↥X) (_ : x ∈ f.base ⁻¹' {z}),
          (c + d) x * (mapCoeff f wx wy x : R) :=
        map_apply f wx wy (c + d) z
    _ = ∑ᶠ (x : ↥X) (_ : x ∈ f.base ⁻¹' {z}),
          (c x * (mapCoeff f wx wy x : R) + d x * (mapCoeff f wx wy x : R)) :=
        finsum_mem_congr rfl fun x _ =>
          Eq.trans (congrArg₂ HMul.hMul (multiplicity_add c d x) rfl)
            (add_mul _ _ _)
    _ = (∑ᶠ (x : ↥X) (_ : x ∈ f.base ⁻¹' {z}), c x * (mapCoeff f wx wy x : R)) +
        ∑ᶠ (x : ↥X) (_ : x ∈ f.base ⁻¹' {z}), d x * (mapCoeff f wx wy x : R) :=
        finsum_mem_add_distrib' (hfin c) (hfin d)
    _ = (map f wx wy c + map f wx wy d) z :=
        Eq.trans
          (Eq.symm (congrArg₂ HAdd.hAdd (map_apply f wx wy c z)
            (map_apply f wx wy d z)))
          (Eq.symm (multiplicity_add (map f wx wy c) (map f wx wy d) z))

-- Reference: Stacks Project, Chow Homology, Def. 42.12.1, tag 02R4
-- (`f_* [Z] = deg(Z/f(Z)) [f(Z)]`: the pushforward of a point cycle is the
-- point cycle at the image, weighted by the residue degree).
open scoped Classical in
/-- The map of a point cycle is the point cycle at the image point, with
the coefficient weighted by `mapCoeff` at the point. -/
theorem map_single (f : X ⟶ Y) [QuasiCompact f] {N : Type*} [DecidableEq N]
    [DecidableEq ↥X] [DecidableEq ↥Y] (wx : X → N) (wy : Y → N) (x : ↥X) (r : R) :
    map f wx wy (Function.locallyFinsuppWithin.single x r) =
      Function.locallyFinsuppWithin.single (f.base x)
        (r * (mapCoeff f wx wy x : R)) := by
  refine Function.locallyFinsuppWithin.ext (fun z => ?_)
  -- a nonzero weighted term of a point cycle sits at its point
  have key : ∀ {a : ↥X},
      Function.locallyFinsuppWithin.single x r a * (mapCoeff f wx wy a : R) ≠ 0 →
      a = x :=
    fun ha => Set.mem_singleton_iff.mp (support_single_subset
      (Function.mem_support.mpr
        (fun hsingle => ha (Eq.trans (congrArg₂ HMul.hMul hsingle rfl)
          (zero_mul _)))))
  rcases Classical.em (z = f.base x) with hz | hz
  · subst hz
    calc map f wx wy (Function.locallyFinsuppWithin.single x r) (f.base x)
        = ∑ᶠ (a : ↥X) (_ : a ∈ f.base ⁻¹' {f.base x}),
            Function.locallyFinsuppWithin.single x r a *
              (mapCoeff f wx wy a : R) :=
          map_apply f wx wy _ _
      _ = ∑ a ∈ ({x} : Finset ↥X),
            Function.locallyFinsuppWithin.single x r a *
              (mapCoeff f wx wy a : R) :=
          finsum_cond_eq_sum_of_cond_iff _
            (fun ha => Iff.intro
              (fun _ => Finset.mem_singleton.mpr (key ha))
              (fun hmem => Set.mem_preimage.mpr
                (Set.mem_singleton_iff.mpr
                  (congrArg f.base (Finset.mem_singleton.mp hmem)))))
      _ = Function.locallyFinsuppWithin.single x r x *
            (mapCoeff f wx wy x : R) :=
          Finset.sum_singleton _ x
      _ = r * (mapCoeff f wx wy x : R) :=
          congrArg₂ HMul.hMul
            (Eq.trans Function.locallyFinsuppWithin.single_apply
              (ite_eq_left rfl)) rfl
      _ = Function.locallyFinsuppWithin.single (f.base x)
            (r * (mapCoeff f wx wy x : R)) (f.base x) :=
          (Eq.trans Function.locallyFinsuppWithin.single_apply
            (ite_eq_left rfl)).symm
  · calc map f wx wy (Function.locallyFinsuppWithin.single x r) z
        = ∑ᶠ (a : ↥X) (_ : a ∈ f.base ⁻¹' {z}),
            Function.locallyFinsuppWithin.single x r a *
              (mapCoeff f wx wy a : R) :=
          map_apply f wx wy _ _
      _ = ∑ a ∈ (∅ : Finset ↥X),
            Function.locallyFinsuppWithin.single x r a *
              (mapCoeff f wx wy a : R) :=
          finsum_cond_eq_sum_of_cond_iff _
            (fun ha => Iff.intro
              (fun hmem => absurd
                (Eq.trans (congrArg f.base (key ha)).symm
                  (Set.mem_singleton_iff.mp (Set.mem_preimage.mp hmem)))
                (Ne.symm hz))
              (fun hmem => absurd hmem (Finset.notMem_empty _)))
      _ = 0 := Finset.sum_empty
      _ = Function.locallyFinsuppWithin.single (f.base x)
            (r * (mapCoeff f wx wy x : R)) z :=
          Eq.symm (Eq.trans Function.locallyFinsuppWithin.single_apply
            (ite_eq_right hz))

-- Reference: Stacks Project, Chow Homology, §42.12, tag 02R3 (the pushforward
-- is a homomorphism of abelian groups).
/-- The **map homomorphism**: `AlgebraicCycle.map` along a quasicompact
morphism with a weight pair, as a homomorphism of the additive monoids of
cycles. Noncomputable: the fiber sums in `map` are enumerated by choice. -/
noncomputable def mapHom (f : X ⟶ Y) [QuasiCompact f] {N : Type*} [DecidableEq N]
    (wx : X → N) (wy : Y → N) : AlgebraicCycle X R →+ AlgebraicCycle Y R where
  toFun := map f wx wy
  map_zero' := map_zero f wx wy
  map_add' := map_add f wx wy

-- Reference: Stacks Project, Chow Homology, §42.12, tag 02R3.
/-- The map homomorphism is the map. -/
theorem mapHom_apply (f : X ⟶ Y) [QuasiCompact f] {N : Type*} [DecidableEq N]
    (wx : X → N) (wy : Y → N) (c : AlgebraicCycle X R) :
    mapHom f wx wy c = map f wx wy c := rfl

-- Reference: Stacks Project, Chow Homology, Lemma 42.12.2, tag 02R5 (the
-- degrees multiply along a tower: `deg(W/W'') = deg(W/W') deg(W'/W'')`),
-- with the weight of Def. 42.12.1, tag 02R4, and the tower law for residue
-- degrees (`Scheme.Hom.residueDegree_comp`).
/-- **The weight law along a tower**: under the weight compatibility
`wy (g x) = wz ((g ≫ h) x)`, the `mapCoeff` weight of the composite is the
product of the weights (the residue degrees multiply along the tower). -/
theorem mapCoeff_comp {Z : Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ Z)
    {N : Type*} [DecidableEq N] (wx : X → N) (wy : Y → N) (wz : Z → N)
    (hwt : ∀ x : X, wy (g.base x) = wz ((g ≫ h).base x)) (x : X) :
    mapCoeff (g ≫ h) wx wz x =
      mapCoeff g wx wy x * mapCoeff h wy wz (g.base x) := by
  unfold mapCoeff
  rcases Classical.em (wx x = wz ((g ≫ h).base x)) with h1 | h1
  · have h2 : wx x = wy (g.base x) := Eq.trans h1 (hwt x).symm
    have h3 : wy (g.base x) = wz ((g ≫ h).base x) := hwt x
    calc (if wx x = wz ((g ≫ h).base x) then (g ≫ h).residueDegree x else 0)
        = (g ≫ h).residueDegree x := ite_eq_left h1
      _ = h.residueDegree (g.base x) * g.residueDegree x :=
          Scheme.Hom.residueDegree_comp g h x
      _ = (if wx x = wy (g.base x) then g.residueDegree x else 0) *
            (if wy (g.base x) = wz ((g ≫ h).base x)
              then h.residueDegree (g.base x) else 0) :=
          Eq.symm (Eq.trans (congrArg₂ HMul.hMul (ite_eq_left h2) (ite_eq_left h3))
            (mul_comm _ _))
  · have h2 : ¬ (wx x = wy (g.base x)) := fun hc => h1 (Eq.trans hc (hwt x))
    calc (if wx x = wz ((g ≫ h).base x) then (g ≫ h).residueDegree x else 0)
        = 0 := ite_eq_right h1
      _ = (if wx x = wy (g.base x) then g.residueDegree x else 0) *
            (if wy (g.base x) = wz ((g ≫ h).base x)
              then h.residueDegree (g.base x) else 0) :=
          Eq.symm (Eq.trans (congrArg₂ HMul.hMul (ite_eq_right h2) rfl) (zero_mul _))

-- Reference: Stacks Project, Chow Homology, Lemma 42.12.2, tag 02R5 (the
-- pushforward is functorial: `g_* ∘ f_* = (g ∘ f)_*`); the weight
-- compatibility clause is the weight pair's own design purpose (mathlib's
-- `AlgebraicCycle.map` docstring).
-- W. Fulton, *Intersection Theory*, ch. 1, §1.3 (push-forward is
-- functorial). REVIEW(citation): pin down the section in review.
open scoped Classical in
/-- **The composition law for the weighted map**: the map along a
composite is the map of the map, provided the middle weight agrees with
the outer weight along the tower (`wy (g x) = wz ((g ≫ h) x)`). -/
theorem map_comp {Z : Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ Z)
    [QuasiCompact g] [QuasiCompact h] {N : Type*} [DecidableEq N]
    (wx : X → N) (wy : Y → N) (wz : Z → N)
    (hwt : ∀ x : X, wy (g.base x) = wz ((g ≫ h).base x))
    (c : AlgebraicCycle X R) :
    map (g ≫ h) wx wz c = map h wy wz (map g wx wy c) := by
  refine Function.locallyFinsuppWithin.ext (fun w => ?_)
  have hS : ((g ≫ h).base ⁻¹' {w} ∩ c.support).Finite :=
    finite_support_inter_fiber_of_coeff (g ≫ h) c w
  have hV : (h.base ⁻¹' {w} ∩ (map g wx wy c).support).Finite :=
    finite_support_inter_fiber_of_coeff h (map g wx wy c) w
  have hTy : ∀ y : ↥Y, (g.base ⁻¹' {y} ∩ c.support).Finite := fun y =>
    finite_support_inter_fiber_of_coeff g c y
  -- a nonzero weighted term has a nonzero coefficient
  have key : ∀ x : ↥X, c x * (mapCoeff g wx wy x : R) ≠ 0 → c x ≠ 0 :=
    fun x hx hc => hx (Eq.trans (congrArg₂ HMul.hMul hc rfl) (zero_mul _))
  -- each coefficient of the inner map is a finite sum over the fiber
  have coeff_red : ∀ y : ↥Y, (map g wx wy c) y =
      ∑ x ∈ (hTy y).toFinset, c x * (mapCoeff g wx wy x : R) := fun y =>
    finsum_cond_eq_sum_of_cond_iff _ fun ha => Iff.intro
      (fun hmem =>
        (Set.Finite.mem_toFinset (hTy y)).mpr
          ⟨Set.mem_preimage.mpr
            (Eq.trans (Set.mem_singleton_iff.mp (Set.mem_preimage.mp hmem))
              rfl),
          Function.mem_support.mpr (key _ ha)⟩)
      (fun hmem => ((Set.Finite.mem_toFinset (hTy y)).mp hmem).1)
  -- multiplying a coefficient by the outer weight is a finite weighted
  -- fiber sum
  have fiber_red : ∀ y : ↥Y, (map g wx wy c) y * (mapCoeff h wy wz y : R) =
      ∑ x ∈ (hTy y).toFinset,
        (c x * (mapCoeff g wx wy x : R)) * (mapCoeff h wy wz y : R) := fun y =>
    Eq.trans (congrArg₂ HMul.hMul (coeff_red y) rfl) (Finset.sum_mul _ _ _)
  -- the composite weight is the product of the weights along the tower
  have tower : ∀ x : ↥X, c x * (mapCoeff (g ≫ h) wx wz x : R) =
      (c x * (mapCoeff g wx wy x : R)) * (mapCoeff h wy wz (g.base x) : R) :=
    fun x =>
      Eq.trans (congrArg₂ HMul.hMul rfl
        (Eq.trans (congrArg (Nat.cast (R := R))
            (mapCoeff_comp g h wx wy wz hwt x))
          (Nat.cast_mul _ _)))
        (mul_assoc _ _ _).symm
  -- the left side: the composite fiber sum, with the factored weight
  have left_red : (map (g ≫ h) wx wz c) w =
      ∑ x ∈ hS.toFinset,
        (c x * (mapCoeff g wx wy x : R)) * (mapCoeff h wy wz (g.base x) : R) := by
    refine Eq.trans (Eq.trans (map_apply (g ≫ h) wx wz c w)
      (finsum_mem_congr rfl fun x _ => tower x)) ?_
    refine finsum_cond_eq_sum_of_cond_iff _ fun ha => Iff.intro
      (fun hmem =>
        (Set.Finite.mem_toFinset hS).mpr
          ⟨hmem, Function.mem_support.mpr (key _
            (fun hc => ha (Eq.trans (congrArg₂ HMul.hMul hc rfl)
              (zero_mul _))))⟩)
      (fun hmem => ((Set.Finite.mem_toFinset hS).mp hmem).1)
  -- the right side: the outer fiber sum, then the inner fiber sums
  have right_red : (map h wy wz (map g wx wy c)) w =
      ∑ y ∈ hV.toFinset, ∑ x ∈ (hTy y).toFinset,
        (c x * (mapCoeff g wx wy x : R)) * (mapCoeff h wy wz y : R) := by
    refine Eq.trans (Eq.trans (map_apply h wy wz (map g wx wy c) w)
      (finsum_cond_eq_sum_of_cond_iff _ fun ha => Iff.intro
        (fun hmem =>
          (Set.Finite.mem_toFinset hV).mpr
            ⟨hmem, Function.mem_support.mpr
              (fun hc => ha (Eq.trans (congrArg₂ HMul.hMul hc rfl)
                (zero_mul _)))⟩)
        (fun hmem => ((Set.Finite.mem_toFinset hV).mp hmem).1))) ?_
    exact Finset.sum_congr rfl fun y _ => fiber_red y
  -- the fibers of g over the image of the composite fiber carry the left sum
  have part : ∑ x ∈ hS.toFinset,
        (c x * (mapCoeff g wx wy x : R)) * (mapCoeff h wy wz (g.base x) : R) =
      ∑ y ∈ hV.toFinset, ∑ x ∈ (hTy y).toFinset,
        (c x * (mapCoeff g wx wy x : R)) * (mapCoeff h wy wz y : R) := by
    have maps_to : ∀ x ∈ hS.toFinset,
        g.base x ∈ hS.toFinset.image g.base :=
      fun _ hx => Finset.mem_image_of_mem _ hx
    have step1 : ∑ x ∈ hS.toFinset,
          (c x * (mapCoeff g wx wy x : R)) *
            (mapCoeff h wy wz (g.base x) : R) =
        ∑ y ∈ hS.toFinset.image g.base,
          ∑ x ∈ hS.toFinset.filter (fun a => g.base a = y),
            (c x * (mapCoeff g wx wy x : R)) *
              (mapCoeff h wy wz (g.base x) : R) :=
      Eq.symm (Finset.sum_fiberwise_of_maps_to maps_to _)
    -- an image point lies over w
    have himg : ∀ y, y ∈ hS.toFinset.image g.base → h.base y = w := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      exact Eq.trans (congrArg h.base rfl)
        (Set.mem_singleton_iff.mp
          (Set.mem_preimage.mp ((Set.Finite.mem_toFinset hS).mp hx).1))
    -- on a fiber of g, the outer weight is constant, and the fiber sum is
    -- the coefficient of the inner map
    have step2 : ∀ y, y ∈ hS.toFinset.image g.base →
        ∑ x ∈ hS.toFinset.filter (fun a => g.base a = y),
            (c x * (mapCoeff g wx wy x : R)) *
              (mapCoeff h wy wz (g.base x) : R) =
          (map g wx wy c) y * (mapCoeff h wy wz y : R) := by
      intro y hy
      have fil_eq : hS.toFinset.filter (fun a => g.base a = y) =
          (hTy y).toFinset := by
        refine Finset.ext fun a => ?_
        refine Iff.trans (Finset.mem_filter) ?_
        refine Iff.trans ?_ (Set.Finite.mem_toFinset (hTy y)).symm
        refine Iff.intro (fun hmem => ?_) (fun hmem => ?_)
        · exact Set.mem_inter
            (Set.mem_preimage.mpr
              (Set.mem_singleton_iff.mpr hmem.2))
            ((Set.Finite.mem_toFinset hS).mp hmem.1).2
        · refine ⟨(Set.Finite.mem_toFinset hS).mpr
              (Set.mem_inter ?_ hmem.2), ?_⟩
          · exact Set.mem_preimage.mpr
              (Eq.trans (congrArg h.base
                (Set.mem_singleton_iff.mp (Set.mem_preimage.mp hmem.1)))
                (himg y hy))
          · exact Set.mem_preimage.mp hmem.1
      refine Eq.trans (Finset.sum_congr rfl fun x hx =>
        congrArg₂ HMul.hMul rfl
          (congrArg (Nat.cast (R := R))
            (congrArg (mapCoeff h wy wz) (Finset.mem_filter.mp hx).2))) ?_
      refine Eq.trans (Eq.symm (Finset.sum_mul _ _ _)) ?_
      refine Eq.trans (congrArg₂ HMul.hMul
        (congrArg (Finset.sum · (fun x => c x * (mapCoeff g wx wy x : R)))
          fil_eq) rfl) ?_
      exact congrArg₂ HMul.hMul (coeff_red y).symm rfl
    -- the support of the inner map lies in the image, and the extension to
    -- the image vanishes off the support
    have Vsub : hV.toFinset ⊆ hS.toFinset.image g.base := by
      intro y hy
      have hyV := (Set.Finite.mem_toFinset hV).mp hy
      obtain ⟨x, hx, hxne⟩ := exists_ne_zero_of_finsum_mem_ne_zero
        (Function.mem_support.mp hyV.2)
      refine Finset.mem_image.mpr ⟨x, ?_, ?_⟩
      · refine (Set.Finite.mem_toFinset hS).mpr ⟨?_, ?_⟩
        · exact Set.mem_preimage.mpr
            (Eq.trans (congrArg h.base
              (Set.mem_singleton_iff.mp (Set.mem_preimage.mp hx)))
              (Set.mem_singleton_iff.mp (Set.mem_preimage.mp hyV.1)))
        · exact Function.mem_support.mpr (key x hxne)
      · exact Set.mem_singleton_iff.mp (Set.mem_preimage.mp hx)
    have hext : ∑ y ∈ hS.toFinset.image g.base,
        (map g wx wy c) y * (mapCoeff h wy wz y : R) =
      ∑ y ∈ hV.toFinset, (map g wx wy c) y * (mapCoeff h wy wz y : R) :=
      Eq.symm (Finset.sum_subset Vsub
        (fun y hy hyV => Eq.trans (congrArg₂ HMul.hMul
          (Function.notMem_support.mp (fun hmem => hyV
            ((Set.Finite.mem_toFinset hV).mpr
              ⟨Set.mem_preimage.mpr (himg y hy), hmem⟩)))
          rfl)
          (zero_mul _)))
    exact Eq.trans step1
      (Eq.trans (Finset.sum_congr rfl fun y hy => step2 y hy)
        (Eq.trans hext (Finset.sum_congr rfl fun y _ => fiber_red y)))
  exact Eq.trans left_red (Eq.trans part right_red.symm)

-- Reference: Stacks Project, Chow Homology, Lemma 42.12.2, tag 02R5
-- (functoriality of the pushforward).
-- W. Fulton, *Intersection Theory*, ch. 1, §1.3 (push-forward is
-- functorial). REVIEW(citation): pin down the section in review.
/-- The map homomorphism is functorial under the weight compatibility: the
homomorphism of a composite is the composite of the homomorphisms. -/
theorem mapHom_comp {Z : Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ Z)
    [QuasiCompact g] [QuasiCompact h] {N : Type*} [DecidableEq N]
    (wx : X → N) (wy : Y → N) (wz : Z → N)
    (hwt : ∀ x : X, wy (g.base x) = wz ((g ≫ h).base x)) :
    mapHom (R := R) (g ≫ h) wx wz = (mapHom (R := R) h wy wz).comp (mapHom (R := R) g wx wy) :=
  AddMonoidHom.ext fun c => map_comp (R := R) g h wx wy wz hwt c

end AlgebraicCycle

end AlgebraicGeometry
