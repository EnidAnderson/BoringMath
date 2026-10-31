/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Sites.Precoverage
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck

/-!
# Over-sites from arbitrary precoverages

Mathlib's `Mathlib.CategoryTheory.Sites.Over` proves, for a precoverage `K` on
`C` with `[K.HasPullbacks]` and `[K.IsStableUnderBaseChange]`, the identity
`K.toGrothendieck.over X = (K.comap (Over.forget X)).toGrothendieck`
(`over_toGrothendieck_eq_toGrothendieck_comap_forget`), and leaves a TODO to
generalize the section to arbitrary precoverages.

This file resolves that TODO in the negative:

* One inequality holds for an **arbitrary** precoverage `K`, with no
  base-change hypotheses at all:
  `(K.comap (Over.forget X)).toGrothendieck ≤ K.toGrothendieck.over X`
  (`Precoverage.comap_forget_toGrothendieck_le_over_toGrothendieck`).
* The reverse inequality is **false** in general. The counterexample is the
  four-object poset `W ≤ Z`, `Zp ≤ Z`, `W ≤ X` carrying the precoverage
  whose only covering presieve is the empty presieve at `Z`
  (`OverPrecoverageCounterexample.K`): the empty sieve at `W` is covering for
  `K.toGrothendieck` (it is a pullback of a covering sieve), hence the empty
  sieve at `V = (W ⟶ X)` is covering for `K.toGrothendieck.over X`, while
  `K.comap (Over.forget X)` is the empty precoverage, so its generated
  topology is the bottom topology, which does not contain the empty sieve
  (`OverPrecoverageCounterexample.over_toGrothendieck_ne_comap_forget_toGrothendieck`).
  The base-change hypotheses of the Mathlib lemma are exactly what rules this
  out: they are used upstream only to convert `Precoverage.Saturate` into the
  pullback-free `Coverage.Saturate` (`Precoverage.toGrothendieck_toCoverage`).

## References
* SGA 4, Exposé III, §5.2.1: the topology on the category `C/X` of objects
  over `X` — a sieve of `Y : C/X` is covering iff its image under the
  forgetful functor is — as cited by `Mathlib.CategoryTheory.Sites.Over`
  (Riou).
* J. Riou, `Mathlib.CategoryTheory.Sites.Over` — the hypothesis-bound
  identity and the TODO generalized here.
* B. Guillemet–A. Topaz, `Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck`
  — the saturation `Precoverage.Saturate` generating `Precoverage.toGrothendieck`.
-/

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace Sieve

-- Reference: J. Riou, `Mathlib.CategoryTheory.Sites.Over`, definition of
-- `Sieve.overEquiv` (the sieve bijection of SGA 4, Exposé III, §5.2.1).
/-- The order isomorphism `Sieve.overEquiv Y` is definitionally the functor
pushforward along `Over.forget X`. -/
lemma overEquiv_apply_eq_functorPushforward_forget {X : C} (Y : Over X) (S : Sieve Y) :
    Sieve.overEquiv Y S = S.functorPushforward (Over.forget X) := rfl

end Sieve

namespace GrothendieckTopology

-- Reference: SGA 4, Exposé III, §5.2.1 (the topology on `C/X`), as cited by
-- J. Riou, `Mathlib.CategoryTheory.Sites.Over`.
-- REVIEW(citation): the proposition number 5.2.1 is taken from the Mathlib
-- docstring; web mirrors of SGA 4 Exposé III confirm that §5 treats the
-- induced topology on `C/X` ("site induit C/X", III 5.1), but the literal
-- string "5.2.1" was not directly quotable from searchable text.
/-- For a Grothendieck topology `J` on `C`, membership in the precoverage
underlying the over-topology `J.over X` is membership in the comap of
`J.toPrecoverage` along `Over.forget X`. -/
theorem mem_over_toPrecoverage_iff_comap_forget (J : GrothendieckTopology C) (X : C)
    (V : Over X) (Q : Presieve V) :
    Q ∈ (J.over X).toPrecoverage V ↔
      Q ∈ (J.toPrecoverage).comap (Over.forget X) V := by
  have hgen : Sieve.overEquiv V (Sieve.generate Q) =
      Sieve.generate (Q.map (Over.forget X)) :=
    (Sieve.overEquiv_apply_eq_functorPushforward_forget V (Sieve.generate Q)).trans
      (Sieve.generate_map_eq_functorPushforward (Over.forget X) (s := Q)).symm
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h1 : Sieve.overEquiv V (Sieve.generate Q) ∈ J V.left := h
    have h2 : Sieve.generate (Q.map (Over.forget X)) ∈ J V.left := Eq.subst hgen h1
    exact h2
  · have h1 : Sieve.generate (Q.map (Over.forget X)) ∈ J V.left := h
    have h2 : Sieve.overEquiv V (Sieve.generate Q) ∈ J V.left := Eq.subst hgen.symm h1
    exact h2

end GrothendieckTopology

namespace Precoverage

-- Reference: SGA 4, Exposé III, §5.2.1 (via J. Riou,
-- `Mathlib.CategoryTheory.Sites.Over`, second inequality of
-- `over_toGrothendieck_eq_toGrothendieck_comap_forget`).
-- REVIEW(citation): see the note on `mem_over_toPrecoverage_iff_comap_forget`.
/-- **The half of the over-site identity that holds for arbitrary precoverages.**
For any precoverage `K` on `C` — with no `HasPullbacks` or
`IsStableUnderBaseChange` hypothesis — the Grothendieck topology generated by
the comap of `K` along `Over.forget X` is contained in
`K.toGrothendieck.over X`. -/
theorem comap_forget_toGrothendieck_le_over_toGrothendieck (K : Precoverage C) (X : C) :
    (K.comap (Over.forget X)).toGrothendieck ≤ K.toGrothendieck.over X :=
  (Precoverage.toGrothendieck_le_iff_le_toPrecoverage).mpr (by
    intro V Q hQ
    have hQ' : Q.map (Over.forget X) ∈ K ((Over.forget X).obj V) := hQ
    have hle : K ≤ K.toGrothendieck.toPrecoverage :=
      Precoverage.le_toPrecoverage_toGrothendieck K
    have hQ'' : Q.map (Over.forget X) ∈
        K.toGrothendieck.toPrecoverage ((Over.forget X).obj V) := hle _ hQ'
    exact (GrothendieckTopology.mem_over_toPrecoverage_iff_comap_forget
      K.toGrothendieck X V Q).mpr hQ'')

end Precoverage

/-!
### The reverse inequality fails for arbitrary precoverages

The counterexample category is the poset with objects `W`, `Z`, `Zp`, `X` and
relations `W ≤ Z`, `Zp ≤ Z`, `W ≤ X` (and no others). The precoverage `K` has
the empty presieve as its only covering presieve, at `Z`. No object of
`Over Ob.X` has left component `Z`, so `K.comap (Over.forget Ob.X)` is empty
and generates the bottom topology; but the empty sieve at `W` is a pullback
of the covering sieve `generate ⊥ = ⊥` at `Z` along `a : W ⟶ Z`, hence is
covering for `K.toGrothendieck`, and therefore the empty sieve at
`V = Over.mk v` is covering for `K.toGrothendieck.over Ob.X`.
-/

namespace OverPrecoverageCounterexample

-- Reference: this file, the counterexample poset defined next; the only
-- relations are `W ≤ Z`, `Zp ≤ Z`, `W ≤ X` and reflexivity.
/-- The four objects of the counterexample poset. -/
inductive Ob | W | Z | Zp | X
  deriving DecidableEq

-- Reference: this file, the counterexample poset (`Ob`).
/-- The partial order on the counterexample objects: `a ≤ b` iff `a = b`, or
`(a, b) ∈ {(W, Z), (Zp, Z), (W, X)}`. -/
instance : LE Ob where
  le a b :=
    a = b ∨ (a = Ob.W ∧ b = Ob.Z) ∨ (a = Ob.Zp ∧ b = Ob.Z) ∨ (a = Ob.W ∧ b = Ob.X)

-- Reference: this file, the counterexample poset (`Ob`, the `LE` instance).
/-- The preorder structure on the counterexample objects. -/
instance : Preorder Ob where
  le_refl a := Or.inl rfl
  le_trans {a b c} h1 h2 := by
    rcases h1 with h | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
    · subst h; exact h2
    · subst ha; subst hb
      rcases h2 with h | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩
      · subst h; exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · exact Ob.noConfusion h
      · exact Ob.noConfusion h
      · exact Ob.noConfusion h
    · subst ha; subst hb
      rcases h2 with h | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩
      · subst h; exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
      · exact Ob.noConfusion h
      · exact Ob.noConfusion h
      · exact Ob.noConfusion h
    · subst ha; subst hb
      rcases h2 with h | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩
      · subst h; exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
      · exact Ob.noConfusion h
      · exact Ob.noConfusion h
      · exact Ob.noConfusion h

-- Reference: this file, the counterexample poset: `W ≤ Z`.
/-- The inequality `W ≤ Z` in the counterexample poset. -/
lemma le_W_Z : Ob.W ≤ Ob.Z := Or.inr (Or.inl ⟨rfl, rfl⟩)

-- Reference: this file, the counterexample poset: `Zp ≤ Z`.
/-- The inequality `Zp ≤ Z` in the counterexample poset. -/
lemma le_Zp_Z : Ob.Zp ≤ Ob.Z := Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))

-- Reference: this file, the counterexample poset: `W ≤ X`.
/-- The inequality `W ≤ X` in the counterexample poset. -/
lemma le_W_X : Ob.W ≤ Ob.X := Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))

-- Reference: this file, the counterexample poset: `W` has no
-- `≤`-predecessor but itself.
/-- If `a ≤ W` in the counterexample poset, then `a = W`. -/
lemma eq_of_le_W {a : Ob} (h : a ≤ Ob.W) : a = Ob.W := by
  rcases h with h | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩
  · exact h
  · exact Ob.noConfusion h
  · exact Ob.noConfusion h
  · exact Ob.noConfusion h

-- Reference: this file, the counterexample poset: `W ≰ Zp`.
/-- There is no inequality `W ≤ Zp` in the counterexample poset. -/
lemma not_le_W_Zp : ¬ (Ob.W ≤ Ob.Zp) := by
  intro h
  rcases h with h | ⟨_, h⟩ | ⟨h, _⟩ | ⟨_, h⟩
  · exact Ob.noConfusion h
  · exact Ob.noConfusion h
  · exact Ob.noConfusion h
  · exact Ob.noConfusion h

-- Reference: this file, the counterexample poset: `Z ≰ X`.
/-- There is no inequality `Z ≤ X` in the counterexample poset; hence no object
of `Over Ob.X` has left component `Z`. -/
lemma not_le_Z_X : ¬ (Ob.Z ≤ Ob.X) := by
  intro h
  rcases h with h | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩
  · exact Ob.noConfusion h
  · exact Ob.noConfusion h
  · exact Ob.noConfusion h
  · exact Ob.noConfusion h

-- Reference: this file, the counterexample poset (`le_W_Z`).
/-- The morphism `W ⟶ Z` in the counterexample category. -/
def a : Ob.W ⟶ Ob.Z := homOfLE le_W_Z

-- Reference: this file, the counterexample poset (`le_W_X`).
/-- The morphism `W ⟶ X` in the counterexample category. -/
def v : Ob.W ⟶ Ob.X := homOfLE le_W_X

-- Reference: this file, the counterexample (the precoverage with the empty
-- presieve as its only covering presieve, at `Z`).
/-- The precoverage on the counterexample category whose only covering presieve
is the empty presieve at `Z`. -/
def K : Precoverage Ob where
  coverings Y := if Y = Ob.Z then {(⊥ : Presieve Y)} else ∅

-- Reference: this file, the counterexample over-object `V = (W ⟶ X)`.
/-- The object `(W, v)` of `Over Ob.X` in the counterexample. -/
def V : Over Ob.X := Over.mk v

-- Reference: this file, the counterexample poset (`not_le_Z_X`).
/-- No object of `Over Ob.X` has left component `Z`. -/
lemma left_ne_Z (U : Over Ob.X) : U.left ≠ Ob.Z := by
  intro h
  have hle : Ob.Z ≤ Ob.X := Eq.subst (motive := fun x => x ≤ Ob.X) h U.hom.down.down
  exact not_le_Z_X hle

-- Reference: this file, the counterexample (definition of `K`, `left_ne_Z`).
/-- The comap of `K` along `Over.forget Ob.X` is below the empty precoverage:
`K` has coverings only at `Z`, and no object of `Over Ob.X` has left `Z`. -/
lemma comap_forget_le_bot : K.comap (Over.forget Ob.X) ≤ (⊥ : Precoverage (Over Ob.X)) := by
  intro U Q hQ
  have hQ' : Q.map (Over.forget Ob.X) ∈ K ((Over.forget Ob.X).obj U) := hQ
  have hne : ((Over.forget Ob.X).obj U) ≠ Ob.Z := left_ne_Z U
  have hif : (if ((Over.forget Ob.X).obj U) = Ob.Z
      then {(⊥ : Presieve ((Over.forget Ob.X).obj U))}
      else (∅ : Set (Presieve ((Over.forget Ob.X).obj U)))) =
      (∅ : Set (Presieve ((Over.forget Ob.X).obj U))) := ite_eq_right hne
  have hK : K ((Over.forget Ob.X).obj U) = (∅ : Set (Presieve ((Over.forget Ob.X).obj U))) := hif
  exfalso
  exact (Set.mem_empty_iff_false _).mp
    (Eq.subst (motive := fun t => Q.map (Over.forget Ob.X) ∈ t) hK hQ')

-- Reference: this file, the counterexample; the saturation generating
-- `Precoverage.toGrothendieck` (Guillemet–Topaz,
-- `Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck`).
/-- The topology generated by the comap of `K` is the bottom topology. -/
lemma comap_forget_toGrothendieck_eq_bot :
    (K.comap (Over.forget Ob.X)).toGrothendieck = (⊥ : GrothendieckTopology (Over Ob.X)) := by
  have hle : (K.comap (Over.forget Ob.X)).toGrothendieck ≤
      (⊥ : GrothendieckTopology (Over Ob.X)) :=
    Eq.subst Precoverage.toGrothendieck_bot
      (Precoverage.toGrothendieck_monotone comap_forget_le_bot)
  exact le_antisymm hle bot_le

-- Reference: this file, the counterexample: the `pullback` constructor of
-- `Precoverage.Saturate` (Guillemet–Topaz,
-- `Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck`) applied to the
-- covering sieve `generate ⊥ = ⊥` at `Z` along `a : W ⟶ Z`.
/-- The empty sieve at `W` is covering for `K.toGrothendieck`: it is the
pullback of the covering sieve `⊥` at `Z` along `a`. -/
lemma bot_mem_toGrothendieck_W : (⊥ : Sieve Ob.W) ∈ K.toGrothendieck Ob.W := by
  have hZ : (⊥ : Presieve Ob.Z) ∈ K Ob.Z := by
    have hif : (if Ob.Z = Ob.Z then {(⊥ : Presieve Ob.Z)} else (∅ : Set (Presieve Ob.Z))) =
        {(⊥ : Presieve Ob.Z)} := ite_eq_left rfl
    exact Eq.subst (motive := fun t => (⊥ : Presieve Ob.Z) ∈ t) hif.symm
      (Set.mem_singleton_iff.mpr rfl)
  have hgen : Sieve.generate (⊥ : Presieve Ob.Z) ∈ K.toGrothendieck Ob.Z :=
    Precoverage.generate_mem_toGrothendieck hZ
  have hsat : K.Saturate Ob.Z (⊥ : Sieve Ob.Z) := Eq.subst Sieve.generate_bot hgen
  have hpull : K.Saturate Ob.W ((⊥ : Sieve Ob.Z).pullback a) :=
    .pullback _ _ hsat Ob.W a
  exact Eq.subst (Sieve.pullback_bot a) hpull

-- Reference: SGA 4, Exposé III, §5.2.1 (a sieve of `Y : C/X` is covering for
-- the over-topology iff its image is), as cited by J. Riou,
-- `Mathlib.CategoryTheory.Sites.Over`.
-- REVIEW(citation): see the note on `mem_over_toPrecoverage_iff_comap_forget`.
/-- The empty sieve at `V` is covering for `K.toGrothendieck.over Ob.X`. -/
lemma bot_mem_over : (⊥ : Sieve V) ∈ (K.toGrothendieck.over Ob.X) V := by
  change Sieve.overEquiv V (⊥ : Sieve V) ∈ K.toGrothendieck V.left
  have hb : Sieve.overEquiv V (⊥ : Sieve V) = (⊥ : Sieve Ob.W) := by
    change (⊥ : Sieve V).functorPushforward (Over.forget Ob.X) = (⊥ : Sieve Ob.W)
    exact Sieve.functorPushforward_bot (F := Over.forget Ob.X) (X := V)
  exact Eq.subst hb.symm bot_mem_toGrothendieck_W

-- Reference: this file, the counterexample (`comap_forget_toGrothendieck_eq_bot`).
/-- The empty sieve at `V` is **not** covering for
`(K.comap (Over.forget Ob.X)).toGrothendieck`, since that topology is the
bottom topology, which contains only the top sieve. -/
lemma not_bot_mem_comap_toGrothendieck :
    (⊥ : Sieve V) ∉ ((K.comap (Over.forget Ob.X)).toGrothendieck) V := by
  intro h
  have h1 : (⊥ : Sieve V) ∈ (⊥ : GrothendieckTopology (Over Ob.X)) V :=
    Eq.subst (motive := fun J => (⊥ : Sieve V) ∈ J V) comap_forget_toGrothendieck_eq_bot h
  have h2 : (⊥ : Sieve V) = ⊤ := GrothendieckTopology.bot_covering.mp h1
  exact bot_ne_top h2

-- Reference: this file, the counterexample; the Mathlib TODO above the
-- precoverage section of J. Riou's `Mathlib.CategoryTheory.Sites.Over`
-- ("Generalize this section to arbitrary precoverages"), quoted verbatim in
-- issue #45.
/-- **The generalization of the Mathlib over-site identity to arbitrary
precoverages is false.** For the precoverage `K` on the four-object poset
with a single covering presieve (the empty presieve at `Z`), the two
topologies on `Over Ob.X` differ. -/
theorem over_toGrothendieck_ne_comap_forget_toGrothendieck :
    K.toGrothendieck.over Ob.X ≠ (K.comap (Over.forget Ob.X)).toGrothendieck := by
  intro heq
  have h1 : (⊥ : Sieve V) ∈ ((K.comap (Over.forget Ob.X)).toGrothendieck) V :=
    Eq.subst (motive := fun J => (⊥ : Sieve V) ∈ J V) heq bot_mem_over
  exact not_bot_mem_comap_toGrothendieck h1

-- Reference: this file, the counterexample
-- `over_toGrothendieck_ne_comap_forget_toGrothendieck`.
/-- The identity `K.toGrothendieck.over X = (K.comap (Over.forget X)).toGrothendieck`
does **not** hold for all precoverages `K`: this is the obstruction to the
Mathlib TODO "generalize this section to arbitrary precoverages" in
`Mathlib.CategoryTheory.Sites.Over` (issue #45). -/
theorem not_forall_over_toGrothendieck_eq_comap_forget_toGrothendieck :
    ¬ (∀ {C : Type} [Category.{0} C] (K : Precoverage.{0} C) (X : C),
        K.toGrothendieck.over X = (K.comap (Over.forget X)).toGrothendieck) :=
  fun h => over_toGrothendieck_ne_comap_forget_toGrothendieck (h K Ob.X)

end OverPrecoverageCounterexample

end CategoryTheory
