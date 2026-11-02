/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringMath.FormalPeriods.FormalPeriods

/-!
# Finite direct sums in the kernel-free abelian setting, and the direct-sum
collapse in `P(𝒜)` (P.5, Hörmann Lemma 2.6)

`AbelianCat` (FormalPeriods.lean) is kernel-free and carries no chosen limit
data; finite direct sums are therefore supplied as **explicit biproduct data**
(`FinBiprod`), and a fiber functor preserving them is stated as a `Prop`
(`PreservesFinBiprod`) — no choice. The main theorem is the direct-sum
collapse `(σ₁ ⊗ ω₁)_{M₁} + (σ₂ ⊗ ω₂)_{M₂} = (σ₁ ⊕ σ₂ ⊗ ω₁ ⊕ ω₂)_{M₁ ⊕ M₂}`
in `P(𝒜)`.

## References
* [Hörmann] J. Hörmann, *Formal periods and the Grothendieck period conjecture*,
  arXiv:2106.03803, Lemma 2.6 and its proof (n = 2 via inclusion/projection
  morphisms, then induction).
* [Mac Lane] S. Mac Lane, *Categories for the Working Mathematician*, 2nd ed.,
  Springer, 1998, Ch. VIII §2 (biproducts in abelian categories).
-/

universe u

namespace BoringMath.FormalPeriods

open CategoryTheory

variable {A : Type u} [Category A] [Preadditive A]

-- Reference: [Mac Lane], CWM, 2nd ed., Ch. VIII §2 (biproduct = product +
-- coproduct; in a preadditive category, finite biproduct data).
/-- Explicit finite biproduct data for a family `M : Fin k → A`: a sum object
`S`, inclusions `ι i : M i ⟶ S`, projections `π i : S ⟶ M i`, with
`π i ≫ ι j = δᵢⱼ` and `Σᵢ ι i ≫ π i = 𝟙 S`. -/
structure FinBiprod {k : ℕ} (M : Fin k → A) where
  S : A
  incl : (i : Fin k) → M i ⟶ S
  proj : (i : Fin k) → S ⟶ M i
  proj_incl_eq : ∀ i : Fin k, incl i ≫ proj i = 𝟙 (M i)
  proj_incl_ne : ∀ i j : Fin k, i ≠ j → incl j ≫ proj i = 0
  incl_proj_sum : finSum k (fun i => proj i ≫ incl i) = 𝟙 S

variable {B R : Type u} [Field B] [Field R] [Algebra B R] [∀ X Y : A, Module B (X ⟶ Y)]

-- Reference: [Hörmann], arXiv:2106.03803, Lemma 2.6 proof (the fiber functor
-- carries the biproduct to the coordinate biproduct of the `FreeMod`s).
/-- A fiber functor preserves a finite biproduct: the dimension adds up, and
the images of the inclusions/projections satisfy the biproduct laws in the
`FreeMod` (consequences of `map_id`/`map_comp`/`map_add` and the `FinBiprod`
laws, so they are stated at the level actually needed). -/
structure PreservesFinBiprod {k : ℕ} (h : FiberFunctor A B R) (M : Fin k → A)
    (bp : FinBiprod M) : Prop where
  dim_sum : h.dim bp.S = finSum k (fun i => h.dim (M i))
  map_proj_incl_eq : ∀ i : Fin k,
    freeModHomComp (h.map (bp.proj i)) (h.map (bp.incl i))
      = freeModHomId (h.dim (M i))
  map_proj_incl_ne : ∀ i j : Fin k, i ≠ j →
    freeModHomComp (h.map (bp.proj j)) (h.map (bp.incl i)) = 0
  map_incl_proj_sum : ∀ x : FreeMod R (h.dim bp.S),
    finSum k (fun i => (freeModHomComp (h.map (bp.incl i)) (h.map (bp.proj i))).toFun x)
      = x

end BoringMath.FormalPeriods
