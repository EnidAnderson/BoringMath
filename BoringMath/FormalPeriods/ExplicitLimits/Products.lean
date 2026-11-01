/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Algebra.Group.Prod
import BoringMath.FormalPeriods.FreeMod
import BoringMath.FormalPeriods.ExplicitLimits.Basic
import BoringMath.FormalPeriods.ExplicitLimits.Pushouts

/-!
# Terminal object, binary products, and biproducts

The terminal object `FreeMod K 0` and binary products of carriers as data
(Mac Lane, CWM 2nd ed., Ch. III §5), with projections, pairing, and the
uniqueness laws; then biproducts: `biInl`/`biInr` together with the product
projections.
-/

universe u

namespace BoringMath

variable {K : Type u} [Field K]

/-! ## Terminal object and binary products (hence finite products) -/

-- Reference: Mac Lane, CWM 2nd ed., Ch. III §5 (p. 72, categories with finite
-- products: terminal object + binary products); Hörmann, arXiv:2106.03803,
-- Def. 2.1 (f.d.-`K`-Vect; the zero space).
/-- The terminal basis-carrying space: `FreeMod K 0`, the zero-dimensional
space. -/
abbrev freeModTerminal (K : Type u) [Field K] := FreeMod K 0

-- Reference: Mac Lane, CWM 2nd ed., Ch. III §5 (p. 72); Axler, Ch. 1.
/-- The unique map into the terminal space (every vector maps to the empty
tuple). -/
def freeModTerminalHom (n : ℕ) : FreeModHom K n 0 where
  toFun := fun _ i => Fin.elim0 i
  map_add' := fun _ _ => funext fun i => Fin.elim0 i
  map_smul' := fun _ _ => funext fun i => Fin.elim0 i

-- Reference: Mac Lane, CWM 2nd ed., Ch. III §5 (p. 72, universal property of
-- the terminal object).
/-- Any two maps into the terminal space are equal. -/
theorem freeModTerminalHom_unique (n : ℕ) (f : FreeModHom K n 0) :
    f = freeModTerminalHom n :=
  freeModHom_ext (fun _ => funext fun i => Fin.elim0 i)

-- Reference: Mac Lane, CWM 2nd ed., Ch. III §4 (p. 68, products); Axler,
-- Ch. 1.
/-- The first projection of a product of carriers, as an explicit linear
map. -/
def prodFstVec (M N : Type u) [Add M] [Zero M] [SMul K M] [Add N] [Zero N] [SMul K N] :
    VecHom K (M × N) M where
  toFun := Prod.fst
  map_add' := fun p q => Prod.fst_add p q
  map_smul' := fun c p => Prod.smul_fst c p

-- Reference: definitional peel of `prodFstVec`.
/-- The first projection applies as `Prod.fst`. -/
theorem prodFstVec_apply (M N : Type u) [Add M] [Zero M] [SMul K M] [Add N] [Zero N]
    [SMul K N] (p : M × N) :
    prodFstVec (K := K) M N p = p.1 := rfl

-- Reference: Mac Lane, CWM 2nd ed., Ch. III §4 (p. 68, products).
/-- The second projection of a product of carriers, as an explicit linear
map. -/
def prodSndVec (M N : Type u) [Add M] [Zero M] [SMul K M] [Add N] [Zero N] [SMul K N] :
    VecHom K (M × N) N where
  toFun := Prod.snd
  map_add' := fun p q => Prod.snd_add p q
  map_smul' := fun c p => Prod.smul_snd c p

-- Reference: definitional peel of `prodSndVec`.
/-- The second projection applies as `Prod.snd`. -/
theorem prodSndVec_apply (M N : Type u) [Add M] [Zero M] [SMul K M] [Add N] [Zero N]
    [SMul K N] (p : M × N) :
    prodSndVec (K := K) M N p = p.2 := rfl

-- Reference: Mac Lane, CWM 2nd ed., Ch. III §4 (p. 68, the pairing
-- ⟨f, g⟩ of two maps into a product).
/-- The pairing of two explicit linear maps into a product: `x ↦ (f x, g x)`. -/
def prodPairVec {Q M N : Type u} [Add Q] [Zero Q] [SMul K Q] [Add M] [Zero M] [SMul K M]
    [Add N] [Zero N] [SMul K N] (f : VecHom K Q M) (g : VecHom K Q N) :
    VecHom K Q (M × N) where
  toFun := fun x => (f x, g x)
  -- Prod.ext with the two pointwise linearity proofs of `f` and `g`.
  map_add' := fun x y => Prod.ext (f.map_add' x y) (g.map_add' x y)
  map_smul' := fun c x => Prod.ext (f.map_smul' c x) (g.map_smul' c x)

-- Reference: definitional peel of `prodPairVec`.
/-- The pairing applies as the ordered pair of values. -/
theorem prodPairVec_apply {Q M N : Type u} [Add Q] [Zero Q] [SMul K Q] [Add M] [Zero M]
    [SMul K M] [Add N] [Zero N] [SMul K N] (f : VecHom K Q M) (g : VecHom K Q N) (x : Q) :
    prodPairVec f g x = (f x, g x) := rfl
-- Reference: definitional peels of `vecHomComp`, `prodPairVec`, `prodFstVec`.
/-- First projection of a pairing, pointwise. -/
theorem prodFstVec_pair_apply {Q M N : Type u} [Add Q] [Zero Q] [SMul K Q] [Add M] [Zero M]
    [SMul K M] [Add N] [Zero N] [SMul K N] (f : VecHom K Q M) (g : VecHom K Q N) (x : Q) :
    vecHomComp (prodFstVec M N) (prodPairVec f g) x = f x :=
  Eq.trans (vecHomComp_apply (prodFstVec M N) (prodPairVec f g) x)
    (Eq.trans (congrArg (prodFstVec M N) (prodPairVec_apply f g x))
      (prodFstVec_apply M N (f x, g x)))

-- Reference: definitional peels of `vecHomComp`, `prodPairVec`, `prodSndVec`.
/-- Second projection of a pairing, pointwise. -/
theorem prodSndVec_pair_apply {Q M N : Type u} [Add Q] [Zero Q] [SMul K Q] [Add M] [Zero M]
    [SMul K M] [Add N] [Zero N] [SMul K N] (f : VecHom K Q M) (g : VecHom K Q N) (x : Q) :
    vecHomComp (prodSndVec M N) (prodPairVec f g) x = g x :=
  Eq.trans (vecHomComp_apply (prodSndVec M N) (prodPairVec f g) x)
    (Eq.trans (congrArg (prodSndVec M N) (prodPairVec_apply f g x))
      (prodSndVec_apply M N (f x, g x)))

-- Reference: definitional peels of `vecHomComp` and `prodFstVec`.
/-- First projection of a composed map, pointwise. -/
theorem vecHomComp_fst_apply {Q M N : Type u} [Add Q] [Zero Q] [SMul K Q] [Add M] [Zero M]
    [SMul K M] [Add N] [Zero N] [SMul K N] (h : VecHom K Q (M × N)) (f : VecHom K Q M)
    (heq : vecHomComp (prodFstVec M N) h = f) (x : Q) : (h x).1 = f x :=
  Eq.trans (prodFstVec_apply M N (h x)).symm
    (Eq.trans (vecHomComp_apply (prodFstVec M N) h x).symm
      (congrFun (congrArg VecHom.toFun heq) x))

-- Reference: definitional peels of `vecHomComp` and `prodSndVec`.
/-- Second projection of a composed map, pointwise. -/
theorem vecHomComp_snd_apply {Q M N : Type u} [Add Q] [Zero Q] [SMul K Q] [Add M] [Zero M]
    [SMul K M] [Add N] [Zero N] [SMul K N] (h : VecHom K Q (M × N)) (g : VecHom K Q N)
    (heq : vecHomComp (prodSndVec M N) h = g) (x : Q) : (h x).2 = g x :=
  Eq.trans (prodSndVec_apply M N (h x)).symm
    (Eq.trans (vecHomComp_apply (prodSndVec M N) h x).symm
      (congrFun (congrArg VecHom.toFun heq) x))


-- Reference: Mac Lane, CWM 2nd ed., Ch. III §4 (p. 68, the product's universal
-- property: π₁ ∘ ⟨f, g⟩ = f).
/-- First projection after pairing is the first map. -/
theorem prodFstVec_comp_pair {Q M N : Type u} [Add Q] [Zero Q] [SMul K Q] [Add M] [Zero M]
    [SMul K M] [Add N] [Zero N] [SMul K N] (f : VecHom K Q M) (g : VecHom K Q N) :
    vecHomComp (prodFstVec M N) (prodPairVec f g) = f :=
  vecHom_ext fun x => prodFstVec_pair_apply f g x

-- Reference: Mac Lane, CWM 2nd ed., Ch. III §4 (p. 68, π₂ ∘ ⟨f, g⟩ = g).
/-- Second projection after pairing is the second map. -/
theorem prodSndVec_comp_pair {Q M N : Type u} [Add Q] [Zero Q] [SMul K Q] [Add M] [Zero M]
    [SMul K M] [Add N] [Zero N] [SMul K N] (f : VecHom K Q M) (g : VecHom K Q N) :
    vecHomComp (prodSndVec M N) (prodPairVec f g) = g :=
  vecHom_ext fun x => prodSndVec_pair_apply f g x

-- Reference: Mac Lane, CWM 2nd ed., Ch. III §4 (p. 68, uniqueness of the
-- pairing).
/-- Uniqueness of the pairing: a map into the product is determined by its two
projections. -/
theorem prodPairVec_unique {Q M N : Type u} [Add Q] [Zero Q] [SMul K Q] [Add M] [Zero M]
    [SMul K M] [Add N] [Zero N] [SMul K N] (f : VecHom K Q M) (g : VecHom K Q N)
    (h : VecHom K Q (M × N))
    (h1 : vecHomComp (prodFstVec M N) h = f) (h2 : vecHomComp (prodSndVec M N) h = g) :
    h = prodPairVec f g :=
  vecHom_ext fun x => Prod.ext (vecHomComp_fst_apply h f h1 x) (vecHomComp_snd_apply h g h2 x)

/-! ## Biproducts -/

-- Reference: Mac Lane, CWM 2nd ed., Ch. VIII §2 (p. 194, additive categories:
-- finite products are biproducts); Hörmann, arXiv:2106.03803 (the `M^m`
-- direct sums of the chase).
/-- The left injection of the biproduct `M × N`. -/
def biInl (M N : Type u) [AddZeroClass M] [SMulZeroClass K M]
    [AddZeroClass N] [SMulZeroClass K N] : VecHom K M (M × N) := inlVec M N

-- Reference: Mac Lane, CWM 2nd ed., Ch. VIII §2 (p. 194).
/-- The right injection of the biproduct `M × N`. -/
def biInr (M N : Type u) [AddZeroClass M] [SMulZeroClass K M]
    [AddZeroClass N] [SMulZeroClass K N] : VecHom K N (M × N) := inrVec M N

-- Reference: definitional peel of `biInl`.
/-- The left biproduct injection applies as `x ↦ (x, 0)`. -/
theorem biInl_apply (M N : Type u) [AddZeroClass M] [SMulZeroClass K M]
    [AddZeroClass N] [SMulZeroClass K N] (x : M) : biInl (K := K) M N x = (x, 0) := rfl

-- Reference: definitional peel of `biInr`.
/-- The right biproduct injection applies as `y ↦ (0, y)`. -/
theorem biInr_apply (M N : Type u) [AddZeroClass M] [SMulZeroClass K M]
    [AddZeroClass N] [SMulZeroClass K N] (y : N) : biInr (K := K) M N y = (0, y) := rfl

-- Reference: Mac Lane, CWM 2nd ed., Ch. VIII §2 (p. 194, the biproduct laws
-- π₁ι₁ = id, π₂ι₁ = 0, π₁ι₂ = 0, π₂ι₂ = id, ι₁π₁ + ι₂π₂ = id).
/-- Biproduct law: `π₁ ∘ ι₁ = id`. -/
theorem biFst_biInl (M N : Type u) [AddZeroClass M] [SMulZeroClass K M]
    [AddZeroClass N] [SMulZeroClass K N]
    (x : M) : vecHomComp (prodFstVec (K := K) M N) (biInl (K := K) M N) x = x :=
  Eq.trans (vecHomComp_apply (prodFstVec (K := K) M N) (biInl (K := K) M N) x)
    (Eq.trans (congrArg (prodFstVec (K := K) M N) (biInl_apply M N x))
      (prodFstVec_apply M N (x, 0)))

-- Reference: Mac Lane, CWM 2nd ed., Ch. VIII §2 (p. 194, π₂ι₁ = 0).
/-- Biproduct law: `π₂ ∘ ι₁ = 0`. -/
theorem biSnd_biInl (M N : Type u) [AddZeroClass M] [SMulZeroClass K M]
    [AddZeroClass N] [SMulZeroClass K N]
    (x : M) : vecHomComp (prodSndVec (K := K) M N) (biInl (K := K) M N) x = 0 :=
  Eq.trans (vecHomComp_apply (prodSndVec (K := K) M N) (biInl (K := K) M N) x)
    (Eq.trans (congrArg (prodSndVec (K := K) M N) (biInl_apply M N x))
      (prodSndVec_apply M N (x, 0)))

-- Reference: Mac Lane, CWM 2nd ed., Ch. VIII §2 (p. 194, π₁ι₂ = 0).
/-- Biproduct law: `π₁ ∘ ι₂ = 0`. -/
theorem biFst_biInr (M N : Type u) [AddZeroClass M] [SMulZeroClass K M]
    [AddZeroClass N] [SMulZeroClass K N]
    (y : N) : vecHomComp (prodFstVec (K := K) M N) (biInr (K := K) M N) y = 0 :=
  Eq.trans (vecHomComp_apply (prodFstVec (K := K) M N) (biInr (K := K) M N) y)
    (Eq.trans (congrArg (prodFstVec (K := K) M N) (biInr_apply M N y))
      (prodFstVec_apply M N (0, y)))

-- Reference: Mac Lane, CWM 2nd ed., Ch. VIII §2 (p. 194, π₂ι₂ = id).
/-- Biproduct law: `π₂ ∘ ι₂ = id`. -/
theorem biSnd_biInr (M N : Type u) [AddZeroClass M] [SMulZeroClass K M]
    [AddZeroClass N] [SMulZeroClass K N]
    (y : N) : vecHomComp (prodSndVec (K := K) M N) (biInr (K := K) M N) y = y :=
  Eq.trans (vecHomComp_apply (prodSndVec (K := K) M N) (biInr (K := K) M N) y)
    (Eq.trans (congrArg (prodSndVec (K := K) M N) (biInr_apply M N y))
      (prodSndVec_apply M N (0, y)))

-- Reference: Mac Lane, CWM 2nd ed., Ch. VIII §2 (p. 194); definitional peels
-- of `biInl`, `biInr`, `prodFstVec`, `prodSndVec`.
/-- The biproduct sum evaluates to the sum of the axis pairs. -/
theorem bi_sum_pair (M N : Type u) [AddZeroClass M] [SMulZeroClass K M]
    [AddZeroClass N] [SMulZeroClass K N] (p : M × N) :
    biInl (K := K) M N (prodFstVec (K := K) M N p)
        + biInr (K := K) M N (prodSndVec (K := K) M N p)
      = (p.1, 0) + (0, p.2) :=
  add_eq_add_of_eq
    (Eq.trans (congrArg (biInl (K := K) M N) (prodFstVec_apply M N p)) (biInl_apply M N p.1))
    (Eq.trans (congrArg (biInr (K := K) M N) (prodSndVec_apply M N p)) (biInr_apply M N p.2))

-- Reference: Mac Lane, CWM 2nd ed., Ch. VIII §2 (p. 194, ι₁π₁ + ι₂π₂ = id).
/-- Biproduct law: `ι₁ π₁ p + ι₂ π₂ p = p`. -/
theorem bi_sum (M N : Type u) [AddZeroClass M] [SMulZeroClass K M]
    [AddZeroClass N] [SMulZeroClass K N]
    (p : M × N) :
    biInl (K := K) M N (prodFstVec (K := K) M N p)
      + biInr (K := K) M N (prodSndVec (K := K) M N p) = p :=
  Eq.trans (bi_sum_pair M N p)
    (Eq.trans (Prod.mk_add_mk p.1 0 0 p.2) (Prod.ext (add_zero p.1) (zero_add p.2)))

end BoringMath
