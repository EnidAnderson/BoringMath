/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringMath.AlgebraicGeometry.AlgebraicCycle.ChowGroup
import BoringMath.AlgebraicGeometry.AlgebraicCycle.Pushforward

/-!
# Functoriality of Chow groups: proper pushforward on `A_*(-)` (I.2, part 1)

The pushforward `f_* : A_*(X) → A_*(Y)` for a quasicompact morphism `f : X ⟶ Y`
(ticket I.2, #283; Fulton ch. 1, §1.4): the cycle-level pushforward
`AlgebraicCycle.pushforward` (LANDED, C.0) descends to the Chow groups, because
it carries the rational-equivalence subgroup of `X` into that of `Y` —
pointwise, `f_*(i_t*γ) = i_t'*((f × 𝔸¹)_*γ)`, the key lemma
`pushforward_sectionPullback` (sorried at Tier 1 with peeling plan: the
fiber-sum bijection `x ↦ i_t x` between the fibers and the residue-degree
base-change equality).

The flat pullback `f*` on Chow groups (I.2 part 2) needs the flat pullback of
general cycles (Serre multiplicities) — not here.

## References
* W. Fulton, *Intersection Theory*, 2nd ed., Springer 1998, ch. 1, §1.4
  (pushforward on Chow groups; Prop. 1.4? — REVIEW(citation): pin).
* Stacks Project, Chow Homology, §42.12, Lemma 42.12.2 (tag 02R5: the
  composition law; rational-equivalence compatibility tags 02R9 ff.).
  REVIEW(citation): pin the tags.
* Hartshorne, GTM 52, App. A, §1-2. REVIEW(citation).
-/

universe u

namespace AlgebraicGeometry

open CategoryTheory Limits

variable {X Y W : Scheme.{u}}

-- Reference: the induced map `X × 𝔸¹ → Y × 𝔸¹` on products with the affine
-- line (base change of `f` along the terminal maps).
/-- The map `X × 𝔸¹ ⟶ Y × 𝔸¹` induced by `f` (on points `(x, t) ↦ (f x, t)`),
as the lift of `(pr₁ ≫ f, pr₂)` against the projections. `noncomputable`:
the fiber products carry chosen limit data. -/
noncomputable def prodMapAffineLine (f : X ⟶ Y) : prodAffineLine X ⟶ prodAffineLine Y :=
  pullback.lift
    (pullback.fst (specULiftZIsTerminal.from X) (specULiftZIsTerminal.from affineLine) ≫ f)
    (pullback.snd (specULiftZIsTerminal.from X) (specULiftZIsTerminal.from affineLine))
    (specULiftZIsTerminal.hom_ext _ _)

-- Reference: computation step (the lift's first projection); primitive
-- definitional lemma.
/-- The product map composed with the first projection is the first
projection composed with `f`. -/
theorem prodMapAffineLine_fst (f : X ⟶ Y) :
    prodMapAffineLine f ≫ pullback.fst (specULiftZIsTerminal.from Y)
      (specULiftZIsTerminal.from affineLine) =
      pullback.fst (specULiftZIsTerminal.from X) (specULiftZIsTerminal.from affineLine) ≫ f :=
  pullback.lift_fst _ _ _

-- Reference: computation step (the lift's second projection); primitive
-- definitional lemma.
/-- The product map composed with the second projection is the second
projection. -/
theorem prodMapAffineLine_snd (f : X ⟶ Y) :
    prodMapAffineLine f ≫ pullback.snd (specULiftZIsTerminal.from Y)
      (specULiftZIsTerminal.from affineLine) =
      pullback.snd (specULiftZIsTerminal.from X) (specULiftZIsTerminal.from affineLine) :=
  pullback.lift_snd _ _ _

-- Reference: the square `X × 𝔸¹ → Y × 𝔸¹` over `f` commutes with the section
-- inclusions: `i_t ≫ (f × 𝔸¹) = f ≫ i_t` (Fulton ch. 1, §1.4: families push
-- forward).
/-- The section inclusion commutes with the product map:
`i_t ≫ (f × 𝔸¹) = f ≫ i_t`. -/
theorem sectionIncl_prodMap (f : X ⟶ Y) (t : specZ ⟶ affineLine)
    (ht : t ≫ affineLineProj = 𝟙 specZ) :
    sectionIncl X t ht ≫ prodMapAffineLine f = f ≫ sectionIncl Y t ht := by
  refine pullback.hom_ext ?_ ?_
  · have hL : (sectionIncl X t ht ≫ prodMapAffineLine f) ≫
        pullback.fst (specULiftZIsTerminal.from Y) (specULiftZIsTerminal.from affineLine) = f :=
      calc (sectionIncl X t ht ≫ prodMapAffineLine f) ≫
            pullback.fst (specULiftZIsTerminal.from Y) (specULiftZIsTerminal.from affineLine)
          = sectionIncl X t ht ≫ (pullback.fst (specULiftZIsTerminal.from X)
              (specULiftZIsTerminal.from affineLine) ≫ f) :=
            congrArg (sectionIncl X t ht ≫ ·) (prodMapAffineLine_fst f)
        _ = (sectionIncl X t ht ≫ pullback.fst (specULiftZIsTerminal.from X)
              (specULiftZIsTerminal.from affineLine)) ≫ f := (Category.assoc _ _ _).symm
        _ = 𝟙 X ≫ f := congrArg (· ≫ f) (sectionIncl_fst X t ht)
        _ = f := Category.id_comp f
    have hR : (f ≫ sectionIncl Y t ht) ≫
        pullback.fst (specULiftZIsTerminal.from Y) (specULiftZIsTerminal.from affineLine) = f :=
      Eq.trans (Category.assoc f _ _)
        (Eq.trans (congrArg (f ≫ ·) (sectionIncl_fst Y t ht)) (Category.comp_id f))
    exact Eq.trans hL hR.symm
  · have hL : (sectionIncl X t ht ≫ prodMapAffineLine f) ≫
        pullback.snd (specULiftZIsTerminal.from Y) (specULiftZIsTerminal.from affineLine) =
        specULiftZIsTerminal.from X ≫ t :=
      Eq.trans (congrArg (sectionIncl X t ht ≫ ·) (prodMapAffineLine_snd f))
        (pullback.lift_snd _ _ _)
    have hR : (f ≫ sectionIncl Y t ht) ≫
        pullback.snd (specULiftZIsTerminal.from Y) (specULiftZIsTerminal.from affineLine) =
        specULiftZIsTerminal.from X ≫ t :=
      Eq.trans (Category.assoc f _ _)
        (Eq.trans (congrArg (f ≫ ·) (pullback.lift_snd _ _ _))
          (Eq.trans (Category.assoc _ _ _).symm
            (congrArg (· ≫ t) (specULiftZIsTerminal.hom_ext (f ≫ specULiftZIsTerminal.from Y)
              (specULiftZIsTerminal.from X)))))
    exact Eq.trans hL hR.symm

-- Reference: the square `X × 𝔸¹ → Y × 𝔸¹` over `f` is a pullback (pasting of
-- the two canonical pullback squares of the products; Stacks 01K4?).
-- REVIEW(citation): pin.
/-- The square `(pr₁, f × 𝔸¹, f, pr₁)` is a pullback square: `X × 𝔸¹` is the
pullback of the first projection `Y × 𝔸¹ → Y` along `f`. -/
theorem isPullback_prodMapAffineLine (f : X ⟶ Y) :
    IsPullback (pullback.fst (specULiftZIsTerminal.from X) (specULiftZIsTerminal.from affineLine))
      (prodMapAffineLine f) f
      (pullback.fst (specULiftZIsTerminal.from Y) (specULiftZIsTerminal.from affineLine)) := by
  have hfac : pullback.fst (specULiftZIsTerminal.from X)
        (specULiftZIsTerminal.from affineLine) ≫ f =
      prodMapAffineLine f ≫ pullback.fst (specULiftZIsTerminal.from Y)
        (specULiftZIsTerminal.from affineLine) :=
    (prodMapAffineLine_fst f).symm
  have houter : IsPullback
      (pullback.fst (specULiftZIsTerminal.from X) (specULiftZIsTerminal.from affineLine))
      (prodMapAffineLine f ≫ pullback.snd (specULiftZIsTerminal.from Y)
        (specULiftZIsTerminal.from affineLine))
      (f ≫ specULiftZIsTerminal.from Y) (specULiftZIsTerminal.from affineLine) := by
    have h1 : prodMapAffineLine f ≫ pullback.snd (specULiftZIsTerminal.from Y)
        (specULiftZIsTerminal.from affineLine) =
        pullback.snd (specULiftZIsTerminal.from X) (specULiftZIsTerminal.from affineLine) :=
      prodMapAffineLine_snd f
    have h2 : f ≫ specULiftZIsTerminal.from Y = specULiftZIsTerminal.from X :=
      (specULiftZIsTerminal.hom_ext _ _).symm
    refine Eq.subst (motive := fun t => IsPullback
      (pullback.fst (specULiftZIsTerminal.from X) (specULiftZIsTerminal.from affineLine)) t
      (f ≫ specULiftZIsTerminal.from Y) (specULiftZIsTerminal.from affineLine)) h1.symm ?_
    refine Eq.subst (motive := fun t => IsPullback
      (pullback.fst (specULiftZIsTerminal.from X) (specULiftZIsTerminal.from affineLine))
      (pullback.snd (specULiftZIsTerminal.from X) (specULiftZIsTerminal.from affineLine)) t
      (specULiftZIsTerminal.from affineLine)) h2.symm ?_
    exact IsPullback.of_hasPullback _ _
  exact IsPullback.of_bot houter hfac
    (IsPullback.of_hasPullback (specULiftZIsTerminal.from Y)
      (specULiftZIsTerminal.from affineLine))

-- Reference: quasicompactness is stable under base change (Stacks tag
-- 01K4? — REVIEW(citation)); mathlib pins
-- `MorphismProperty.IsStableUnderBaseChange @QuasiCompact`.
/-- The product map `f × 𝔸¹` is quasicompact when `f` is: it is the base change
of `f` along the first projection `Y × 𝔸¹ → Y` (`isPullback_prodMapAffineLine`),
and `QuasiCompact` is stable under base change. -/
theorem quasiCompact_prodMapAffineLine (f : X ⟶ Y) [QuasiCompact f] :
    QuasiCompact (prodMapAffineLine f) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (isPullback_prodMapAffineLine f) ‹QuasiCompact f›

-- Reference: a section composed with its retraction is the identity, applied
-- at a point (the pullback-lift laws `Scheme.Hom.comp_apply`,
-- `Scheme.Hom.id_apply`).
/-- The retraction of a section acts as the identity on points:
`r (i x) = x`. -/
theorem section_point_retraction (i : X ⟶ W) (r : W ⟶ X) (h : i ≫ r = 𝟙 X) (x : ↥X) :
    r (i x) = x :=
  Eq.trans (Scheme.Hom.comp_apply i r x).symm
    (Eq.trans (congrFun (congrArg (fun g : X ⟶ X => (g : ↥X → ↥X)) h) x)
      (Scheme.Hom.id_apply x))

-- Reference: the residue-field split of a section: `i.map (r.map y) = y`
-- (the comp law `residueFieldMap_comp` with `i ≫ r = 𝟙` and
-- `residueFieldMap_id`, cast along `section_point_retraction`'s index
-- `X.residueField (r (i x)) = X.residueField x`). Stacks tag 01HX? —
-- REVIEW(citation): pin.
/-- The residue-field map of a section is split-surjective: for every
`y : κ(x)`, `i.residueFieldMap x (r.residueFieldMap (i x) (y cast to κ(r (i x)))) = y`.
TEMPORARY SORRY: peeling plan — `Scheme.residueFieldMap_comp i r x` +
congruence on `h` + `Scheme.residueFieldMap_id`, with the index cast
`congrArg (β := CommRingCat.{u}) X.residueField (section_point_retraction …)` +
`Eq.subst`. -/
theorem residueFieldMap_section_split (i : X ⟶ W) (r : W ⟶ X) (h : i ≫ r = 𝟙 X) (x : ↥X)
    (y : X.residueField x) :
    i.residueFieldMap x (r.residueFieldMap (i x)
      (cast (congrArg (β := Type u) (fun K : CommRingCat.{u} => ↥K)
        (congrArg (β := CommRingCat.{u}) X.residueField
          (section_point_retraction i r h x))).symm y)) = y := by
  -- TEMPORARY SORRY: peeling plan above.
  sorry

-- Reference: a section's `residueFieldMap` is an isomorphism (field homs are
-- injective; the split gives surjectivity; `ConcreteCategory.isIso_iff_bijective`).
-- Stacks tag 01HX? — REVIEW(citation): pin.
/-- The residue-field map of a section is an isomorphism. -/
theorem isIso_residueFieldMap_section (i : X ⟶ W) (r : W ⟶ X) (h : i ≫ r = 𝟙 X) (x : ↥X) :
    IsIso (i.residueFieldMap x) := by
  have hxx := section_point_retraction i r h x
  have hinj : Function.Injective (i.residueFieldMap x) := RingHom.injective _
  have hsurj : Function.Surjective (i.residueFieldMap x) := by
    intro y
    refine ⟨r.residueFieldMap (i x)
      (cast (congrArg (β := Type u) (fun K : CommRingCat.{u} => ↥K)
        (congrArg (β := CommRingCat.{u}) X.residueField hxx)).symm y),
      residueFieldMap_section_split i r h x y⟩
  exact (ConcreteCategory.isIso_iff_bijective _).mpr ⟨hinj, hsurj⟩

-- Reference: the residue degree of `f × 𝔸¹` at the section point `i_t x`
-- equals that of `f` at `x` (the section's residue-field iso transports the
-- extension; `Module.finrank` is invariant under algebra isos).
/-- Residue-degree base change along a section: `(f × 𝔸¹).residueDegree (i_t x)
= f.residueDegree x`. TEMPORARY SORRY: peeling plan — `residueDegree` is
`Module.finrank` of the residue-field extension; the section isos
(`isIso_residueFieldMap_section` for `i_t` and `i_t'`) transport the extension
κ(f x) → κ(x) to κ(i_t' (f x)) → κ(i_t x); finrank invariance under algebra
isos (`Module.finrank_eq_of_algEquiv`-style). -/
theorem residueDegree_prodMap_sectionIncl (f : X ⟶ Y) (t : specZ ⟶ affineLine)
    (ht : t ≫ affineLineProj = 𝟙 specZ) (x : ↥X) :
    (prodMapAffineLine f).residueDegree
      ((sectionIncl X t ht).base x) = f.residueDegree x := by
  -- TEMPORARY SORRY: peeling plan above.
  sorry

-- Reference: Fulton ch. 1, §1.4 (pushforward commutes with pullback along
-- sections: `f_*(i_t*γ) = i_t'*((f × 𝔸¹)_*γ)`).
-- REVIEW(citation): pin.
/-- **Pushforward commutes with section pullback**: `f_*(i_t*γ) =
`i_t'*((f × 𝔸¹)_*γ)`. TEMPORARY SORRY: peeling plan — pointwise via the landed
`AlgebraicCycle.pushforward_apply` (fiber sums), the bijection
`x ↦ i_t x : f ⁻¹' {y} ≃ (f × 𝔸¹) ⁻¹' {i_t' y}` (from
`sectionIncl_prodMap` and injectivity of `i_t`, then `Finset.sum_bij` on the
finite fibers via `finite_support_inter_fiber`), and the residue-degree
base-change equality `residueDegree_prodMap_sectionIncl`. -/
theorem pushforward_sectionPullback (f : X ⟶ Y) [QuasiCompact f]
    [QuasiCompact (prodMapAffineLine f)]
    (t : specZ ⟶ affineLine) (ht : t ≫ affineLineProj = 𝟙 specZ)
    (γ : AlgebraicCycle (prodAffineLine X) ℤ) :
    AlgebraicCycle.pushforward f
        (sectionPullbackHom (sectionIncl X t ht)
          (pullback.fst (specULiftZIsTerminal.from X) (specULiftZIsTerminal.from affineLine))
          (sectionIncl_fst X t ht) γ) =
      sectionPullbackHom (sectionIncl Y t ht)
        (pullback.fst (specULiftZIsTerminal.from Y) (specULiftZIsTerminal.from affineLine))
        (sectionIncl_fst Y t ht)
        (AlgebraicCycle.pushforward (prodMapAffineLine f) γ) := by
  -- TEMPORARY SORRY: peeling plan above.
  sorry

-- Reference: Fulton ch. 1, §1.4 (pushforward preserves rational equivalence).
-- REVIEW(citation): pin.
/-- **Pushforward preserves rational equivalence**: the cycle-level
pushforward carries the rational-equivalence subgroup of `X` into that of
`Y`. -/
theorem pushforward_mem_rationalEquivalence (f : X ⟶ Y) [QuasiCompact f]
    [QuasiCompact (prodMapAffineLine f)] {c : AlgebraicCycle X ℤ}
    (hc : c ∈ rationalEquivalenceAddSubgroup X) :
    AlgebraicCycle.pushforward f c ∈ rationalEquivalenceAddSubgroup Y := by
  obtain ⟨γ, hγ⟩ := (AddMonoidHom.mem_range).mp hc
  have h0 := pushforward_sectionPullback f affineLineZero affineLineZero_proj γ
  have h1 := pushforward_sectionPullback f affineLineOne affineLineOne_proj γ
  refine (AddMonoidHom.mem_range).mpr
    ⟨AlgebraicCycle.pushforward (prodMapAffineLine f) γ, ?_⟩
  calc rationalEquivalenceHom Y (AlgebraicCycle.pushforward (prodMapAffineLine f) γ)
      = sectionPullbackHom (sectionIncl Y affineLineZero affineLineZero_proj)
          (pullback.fst _ _) (sectionIncl_fst Y affineLineZero affineLineZero_proj)
          (AlgebraicCycle.pushforward (prodMapAffineLine f) γ) -
        sectionPullbackHom (sectionIncl Y affineLineOne affineLineOne_proj)
          (pullback.fst _ _) (sectionIncl_fst Y affineLineOne affineLineOne_proj)
          (AlgebraicCycle.pushforward (prodMapAffineLine f) γ) := rfl
    _ = AlgebraicCycle.pushforward f
          (sectionPullbackHom (sectionIncl X affineLineZero affineLineZero_proj)
            (pullback.fst _ _) (sectionIncl_fst X affineLineZero affineLineZero_proj) γ) -
        AlgebraicCycle.pushforward f
          (sectionPullbackHom (sectionIncl X affineLineOne affineLineOne_proj)
            (pullback.fst _ _) (sectionIncl_fst X affineLineOne affineLineOne_proj) γ) :=
          congrArg₂ (· - ·) h0.symm h1.symm
    _ = AlgebraicCycle.pushforward f
          (sectionPullbackHom (sectionIncl X affineLineZero affineLineZero_proj)
            (pullback.fst _ _) (sectionIncl_fst X affineLineZero affineLineZero_proj) γ -
            sectionPullbackHom (sectionIncl X affineLineOne affineLineOne_proj)
            (pullback.fst _ _) (sectionIncl_fst X affineLineOne affineLineOne_proj) γ) :=
          (map_sub (AlgebraicCycle.pushforwardHom f) _ _).symm
    _ = AlgebraicCycle.pushforward f (rationalEquivalenceHom X γ) := rfl
    _ = AlgebraicCycle.pushforward f c := congrArg (AlgebraicCycle.pushforward f) hγ

-- Reference: Fulton ch. 1, §1.4 (the pushforward on Chow groups
-- `f_* : A_*(X) → A_*(Y)`); the lift of the class map along the pushforward.
-- REVIEW(citation): pin.
/-- The **pushforward on Chow groups** `f_* : A_*(X) → A_*(Y)`, induced by the
cycle-level pushforward (well defined by
`pushforward_mem_rationalEquivalence`). `noncomputable`: via the choice-backed
subgroups. -/
noncomputable def chowPushforward (f : X ⟶ Y) [QuasiCompact f]
    [QuasiCompact (prodMapAffineLine f)] :
    chowGroup X →+ chowGroup Y :=
  QuotientAddGroup.lift (rationalEquivalenceAddSubgroup X)
    ((chowClass Y).comp (AlgebraicCycle.pushforwardHom f))
    (fun _ hc => AddMonoidHom.mem_ker.mpr (by
      have h0 : (chowClass Y) (AlgebraicCycle.pushforward f _) = 0 :=
        (QuotientAddGroup.eq_zero_iff _).mpr
          (pushforward_mem_rationalEquivalence f hc)
      exact h0))

-- Reference: computation step (the lift applied to a class); primitive
-- definitional lemma — mathlib's `QuotientAddGroup.lift_mk` is itself `rfl`,
-- and `pushforwardHom_apply`/`chowClass` unfold definitionally.
/-- The pushforward of the class of a cycle is the class of the pushforward. -/
theorem chowPushforward_mk (f : X ⟶ Y) [QuasiCompact f]
    [QuasiCompact (prodMapAffineLine f)] (c : AlgebraicCycle X ℤ) :
    chowPushforward f (chowClass X c) = chowClass Y (AlgebraicCycle.pushforward f c) :=
  rfl

variable {Z : Scheme.{u}}

-- Reference: Fulton ch. 1, §1.4 (the identity law `(𝟙 X)_* = id` on Chow
-- groups); the cycle-level `AlgebraicCycle.pushforward_id` lifted.
-- REVIEW(citation): pin.
/-- **Identity law**: the pushforward along the identity is the identity on
the Chow group. -/
theorem chowPushforward_id (X : Scheme.{u}) [QuasiCompact (prodMapAffineLine (𝟙 X))] :
    chowPushforward (𝟙 X) = AddMonoidHom.id (chowGroup X) := by
  refine AddMonoidHom.ext fun x => ?_
  induction x using Quotient.inductionOn with
  | h c =>
    exact Eq.trans (chowPushforward_mk (𝟙 X) c)
      (Eq.trans (congrArg (chowClass X) (AlgebraicCycle.pushforward_id c)) rfl)

-- Reference: Fulton ch. 1, §1.4 (the composition law `(g ∘ f)_* = g_* ∘ f_*`
-- on Chow groups, Stacks Lemma 42.12.2 tag 02R5); the cycle-level
-- `AlgebraicCycle.pushforward_comp` lifted.
-- REVIEW(citation): pin.
/-- **Composition law**: `(g ≫ f)_* = g_* ∘ f_*` on Chow groups. -/
theorem chowPushforward_comp (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiCompact f] [QuasiCompact g]
    [QuasiCompact (prodMapAffineLine f)] [QuasiCompact (prodMapAffineLine g)]
    [QuasiCompact (prodMapAffineLine (f ≫ g))] :
    chowPushforward (f ≫ g) = (chowPushforward g).comp (chowPushforward f) := by
  refine AddMonoidHom.ext fun x => ?_
  induction x using Quotient.inductionOn with
  | h c =>
    have h1 := chowPushforward_mk (f ≫ g) c
    have h2 := chowPushforward_mk f c
    have h3 := chowPushforward_mk g (AlgebraicCycle.pushforward f c)
    calc chowPushforward (f ≫ g) (chowClass X c)
        = chowClass Z (AlgebraicCycle.pushforward (f ≫ g) c) := h1
      _ = chowClass Z (AlgebraicCycle.pushforward g (AlgebraicCycle.pushforward f c)) :=
          congrArg (chowClass Z) (AlgebraicCycle.pushforward_comp f g c)
      _ = chowPushforward g (chowClass Y (AlgebraicCycle.pushforward f c)) := h3.symm
      _ = chowPushforward g (chowPushforward f (chowClass X c)) :=
          congrArg (chowPushforward g) h2
      _ = ((chowPushforward g).comp (chowPushforward f)) (chowClass X c) := rfl

end AlgebraicGeometry
