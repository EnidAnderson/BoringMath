/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Module.Prod
import BoringMath.FormalPeriods.FreeMod

/-!
# Explicit linear maps and subspaces as explicit data

The first part of `BoringMath.FormalPeriods.ExplicitLimits` (ticket P.3, issue
#95): the explicit linear map `VecHom` between arbitrary carriers of
`K`-vector-space operations (generalizing the P.1 `FreeModHom` to subtype and
quotient carriers), its elementary laws, subspaces as data (`Subspace`), and
the pullback subspace of a cospan.
-/

universe u

namespace BoringMath

variable {K : Type u} [Field K]

/-! ## Explicit linear maps on arbitrary carriers -/

-- Reference: Axler, *Linear Algebra Done Right*, 4th ed., Ch. 1 (a linear
-- map is a function with additivity and homogeneity); Mac Lane, CWM 2nd ed.,
-- Ch. VIII §2 (p. 194, hom-sets as data in additive categories).
/-- A linear map between carriers of `K`-vector-space operations, as explicit
data (STYLE §2.3): a function plus its additivity and homogeneity proofs.
`VecHom` generalizes the P.1 `FreeModHom` from `FreeMod` carriers to subtype
and quotient carriers (kernels, images, pullbacks, quotients, colimits). -/
structure VecHom (K : Type u) [Field K] (V W : Type u)
    [Add V] [Zero V] [SMul K V] [Add W] [Zero W] [SMul K W] where
  toFun : V → W
  map_add' : ∀ x y, toFun (x + y) = toFun x + toFun y
  map_smul' : ∀ (c : K) x, toFun (c • x) = c • toFun x

-- Reference: Lean 4 core (coercion to functions); primitive definitional
-- instance.
/-- `VecHom`s are applied as functions. -/
instance vecHomCoeFun (V W : Type u) [Add V] [Zero V] [SMul K V] [Add W] [Zero W]
    [SMul K W] : CoeFun (VecHom K V W) (fun _ => V → W) :=
  ⟨VecHom.toFun⟩

-- Reference: Axler, Ch. 1 (the identity map).
/-- The identity linear map on a carrier. -/
def vecHomId (V : Type u) [Add V] [Zero V] [SMul K V] : VecHom K V V where
  toFun := id
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

-- Reference: Lean 4 core (definitional unfolding of `vecHomId`); primitive
-- definitional lemma.
/-- The identity map applies as the identity function. -/
theorem vecHomId_apply (V : Type u) [Add V] [Zero V] [SMul K V] (x : V) :
    vecHomId (K := K) V x = x :=
  rfl

-- Reference: Axler, Ch. 1 (composition of linear maps).
/-- Composition of explicit linear maps. -/
def vecHomComp {U V W : Type u} [Add U] [Zero U] [SMul K U] [Add V] [Zero V] [SMul K V]
    [Add W] [Zero W] [SMul K W] (f : VecHom K V W) (g : VecHom K U V) : VecHom K U W where
  toFun := fun x => f (g x)
  map_add' := fun x y =>
    Eq.trans (congrArg f (g.map_add' x y)) (f.map_add' (g x) (g y))
  map_smul' := fun r x =>
    Eq.trans (congrArg f (g.map_smul' r x)) (f.map_smul' r (g x))

-- Reference: Lean 4 core (definitional unfolding of `vecHomComp`); primitive
-- definitional lemma.
/-- Composition applies as iterated application. -/
theorem vecHomComp_apply {U V W : Type u} [Add U] [Zero U] [SMul K U] [Add V] [Zero V]
    [SMul K V] [Add W] [Zero W] [SMul K W] (f : VecHom K V W) (g : VecHom K U V) (x : U) :
    vecHomComp f g x = f (g x) :=
  rfl

-- Reference: structure extensionality (Lean 4 core, proof irrelevance for the
-- two proof fields); primitive definitional lemma.
/-- Two explicit linear maps with the same underlying function are equal. -/
theorem vecHom_ext {V W : Type u} [Add V] [Zero V] [SMul K V] [Add W] [Zero W] [SMul K W]
    {f g : VecHom K V W} (h : ∀ x, f x = g x) : f = g := by
  cases f with | mk f₁ f₂ f₃ =>
  cases g with | mk g₁ g₂ g₃ =>
  -- `f₁ = g₁` by `funext h` (defeq through the coercion); the proof fields
  -- agree by proof irrelevance, so the goal closes definitionally.
  have hf : f₁ = g₁ := funext h
  subst hf
  rfl

-- Reference: the P.1 module `BoringMath.FormalPeriods.FreeMod` (`FreeModHom`).
/-- A `FreeModHom` between basis-carrying spaces, regarded as a `VecHom`. -/
def freeModHomVec {m n : ℕ} (f : FreeModHom K m n) :
    VecHom K (FreeMod K m) (FreeMod K n) where
  toFun := f.toFun
  map_add' := f.map_add'
  map_smul' := f.map_smul'

-- Reference: structure extensionality for `FreeModHom` (Lean 4 core, proof
-- irrelevance); primitive definitional lemma.
/-- Two `FreeModHom`s with the same underlying function are equal. -/
theorem freeModHom_ext {m n : ℕ} {f g : FreeModHom K m n} (h : ∀ x, f.toFun x = g.toFun x) :
    f = g := by
  cases f with | mk f₁ f₂ f₃ =>
  cases g with | mk g₁ g₂ g₃ =>
  have hf : f₁ = g₁ := funext h
  subst hf
  rfl

variable {V W : Type u} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
-- Reference: Lean 4 core (`congrArg`); elementary congruence of addition.
/-- Addition respects equality in both arguments. -/
theorem add_eq_add_of_eq {M : Type*} [Add M] {a b c d : M} (h₁ : a = c) (h₂ : b = d) :
    a + b = c + d :=
  Eq.trans (congrArg (fun t => t + b) h₁) (congrArg (fun t => c + t) h₂)

-- Reference: mathlib `add_sub_add_comm`, `sub_self`, `zero_add` (cancellation
-- in an additive group).
/-- Left cancellation: `(z + x) - (z + y) = x - y`. -/
theorem add_sub_add_left_cancel {V : Type*} [AddCommGroup V] (z x y : V) :
    (z + x) - (z + y) = x - y :=
  Eq.trans (add_sub_add_comm z x z y)
    (Eq.trans (congrArg (fun t => t + (x - y)) (sub_self z)) (zero_add (x - y)))

-- Reference: mathlib `add_sub_add_comm`, `sub_self`, `add_zero`.
/-- Right cancellation: `(x + z) - (y + z) = x - y`. -/
theorem add_sub_add_right_cancel {V : Type*} [AddCommGroup V] (x y z : V) :
    (x + z) - (y + z) = x - y :=
  Eq.trans (add_sub_add_comm x z y z)
    (Eq.trans (congrArg (fun t => (x - y) + t) (sub_self z)) (add_zero (x - y)))

-- Reference: mathlib `sub_eq_add_neg`, `neg_add`.
/-- Negation commutes with subtraction: `(-x) - (-y) = -(x - y)`. -/
theorem neg_sub_eq_neg_sub {V : Type*} [AddCommGroup V] (x y : V) :
    (-x) - (-y) = -(x - y) :=
  Eq.trans (sub_eq_add_neg (-x) (-y))
    (Eq.trans (neg_add x (-y)).symm (congrArg (fun t => -t) (sub_eq_add_neg x y).symm))

-- Reference: mathlib `sub_eq_add_neg`, `neg_one_smul`.
/-- Subtraction as addition of a `(-1)`-multiple: `x - y = x + (-1) • y`. -/
theorem sub_eq_add_neg_one_smul {K : Type*} [Field K] {M : Type*} [AddCommGroup M]
    [Module K M] (x y : M) : x - y = x + (-1 : K) • y :=
  Eq.trans (sub_eq_add_neg x y) (congrArg (fun t => x + t) (neg_one_smul K y).symm)

-- Reference: mathlib `neg_one_smul`, `add_neg_cancel`.
/-- `x + (-1) • x = 0` in a module. -/
theorem add_neg_one_smul {K : Type*} [Field K] {M : Type*} [AddCommGroup M] [Module K M]
    (x : M) : x + (-1 : K) • x = 0 :=
  Eq.trans (congrArg (fun t => x + t) (neg_one_smul K x)) (add_neg_cancel x)

-- Reference: mathlib `neg_one_smul` (in `K` as a module over itself `•` is
-- `*`) and `add_neg_cancel`.
/-- `c + (-1) * c = 0` in a ring. -/
theorem add_neg_one_mul {K : Type*} [Field K] (c : K) : c + (-1 : K) * c = 0 :=
  Eq.trans (congrArg (fun t => c + t) (neg_one_smul K c)) (add_neg_cancel c)


-- Reference: Axler, Ch. 1 (a linear map sends `0` to `0`).
/-- An explicit linear map between full vector-space carriers sends `0` to
`0`. -/
theorem vecHom_map_zero (f : VecHom K V W) : f 0 = 0 :=
  Eq.trans (congrArg f (zero_smul K (0 : V)).symm)
    (Eq.trans (f.map_smul' 0 0) (zero_smul K (f 0)))

-- Reference: Axler, Ch. 1 (additivity and the zero law of a linear map).
/-- An explicit linear map satisfies `f x + f (-x) = 0`. -/
theorem vecHom_map_add_neg (f : VecHom K V W) (x : V) : f x + f (-x) = 0 :=
  Eq.trans (f.map_add' x (-x)).symm
    (Eq.subst (motive := fun t => f t = 0) (add_neg_cancel x).symm (vecHom_map_zero f))

-- Reference: Axler, Ch. 1 (linear maps commute with negation).
/-- An explicit linear map commutes with negation. -/
theorem vecHom_map_neg (f : VecHom K V W) (x : V) : f (-x) = -f x :=
  eq_neg_of_add_eq_zero_left
    (Eq.subst (motive := fun t => t = 0) (add_comm (f x) (f (-x))) (vecHom_map_add_neg f x))

-- Reference: Axler, Ch. 1 (linear maps commute with subtraction, first form).
/-- An explicit linear map sends `x - y` to `f x + -f y`. -/
theorem vecHom_map_sub_add_neg (f : VecHom K V W) (x y : V) : f (x - y) = f x + -f y :=
  Eq.trans (congrArg f (sub_eq_add_neg x y))
    (Eq.trans (f.map_add' x (-y)) (congrArg (fun t => f x + t) (vecHom_map_neg f y)))

-- Reference: Axler, Ch. 1 (linear maps commute with subtraction).
/-- An explicit linear map commutes with subtraction. -/
theorem vecHom_map_sub (f : VecHom K V W) (x y : V) : f (x - y) = f x - f y :=
  Eq.trans (vecHom_map_sub_add_neg f x y) (sub_eq_add_neg (f x) (f y)).symm

/-! ## Subspaces as explicit data -/

-- Reference: Mac Lane, CWM 2nd ed., Ch. VIII §1 (p. 191, kernels as
-- subobjects); Axler, Ch. 1 (subspaces).
/-- A subspace of a `K`-vector space, as explicit data (STYLE §2.3): a carrier
predicate with closure under zero, addition, negation, and scalars. -/
structure Subspace (K : Type u) [Field K] (V : Type u) [AddCommGroup V] [Module K V] where
  carrier : V → Prop
  zero_mem : carrier 0
  add_mem : ∀ {x y}, carrier x → carrier y → carrier (x + y)
  neg_mem : ∀ {x}, carrier x → carrier (-x)
  smul_mem : ∀ (c : K) {x}, carrier x → carrier (c • x)

-- Reference: Lean 4 core (`CoeSort` to the subtype); primitive definitional
-- instance.
/-- The carrier of a subspace is the subtype of elements in it. -/
instance subspaceCoeSort (V : Type u) [AddCommGroup V] [Module K V] :
    CoeSort (Subspace K V) (Type u) :=
  ⟨fun S => {x : V // S.carrier x}⟩

-- Reference: Lean 4 core (pointwise operations on subtypes); primitive
-- definitional instances.
/-- Zero of a subspace subtype. -/
instance subspaceZero (S : Subspace K V) : Zero ↥S := ⟨⟨0, S.zero_mem⟩⟩

-- Reference: Lean 4 core (pointwise addition on subtypes).
/-- Addition of a subspace subtype, pointwise. -/
instance subspaceAdd (S : Subspace K V) : Add ↥S :=
  ⟨fun x y => ⟨x.1 + y.1, S.add_mem x.2 y.2⟩⟩

-- Reference: Lean 4 core (pointwise negation on subtypes).
/-- Negation of a subspace subtype, pointwise. -/
instance subspaceNeg (S : Subspace K V) : Neg ↥S :=
  ⟨fun x => ⟨-x.1, S.neg_mem x.2⟩⟩

-- Reference: Lean 4 core (pointwise scalar action on subtypes).
/-- Scalar action on a subspace subtype, pointwise. -/
instance subspaceSMul (S : Subspace K V) : SMul K ↥S :=
  ⟨fun c x => ⟨c • x.1, S.smul_mem c x.2⟩⟩

-- Reference: definitional peels of the subspace instances; primitive
-- definitional lemmas.
/-- The zero of a subspace subtype has underlying value `0`. -/
theorem subspaceZero_val (S : Subspace K V) : ((0 : ↥S) : V) = 0 := rfl

-- Reference: definitional peel of `subspaceAdd`.
/-- Addition in a subspace subtype is pointwise. -/
theorem subspaceAdd_val (S : Subspace K V) (x y : ↥S) : ((x + y : ↥S) : V) = x.1 + y.1 := rfl

-- Reference: definitional peel of `subspaceNeg`.
/-- Negation in a subspace subtype is pointwise. -/
theorem subspaceNeg_val (S : Subspace K V) (x : ↥S) : ((-x : ↥S) : V) = -x.1 := rfl

-- Reference: definitional peel of `subspaceSMul`.
/-- The scalar action in a subspace subtype is pointwise. -/
theorem subspaceSMul_val (S : Subspace K V) (c : K) (x : ↥S) :
    ((c • x : ↥S) : V) = c • x.1 := rfl

-- Reference: Mac Lane, CWM 2nd ed., Ch. VIII §1 (p. 191, the inclusion of a
-- subobject is a monomorphism).
/-- The inclusion of a subspace into its ambient space, as an explicit linear
map. -/
def subspaceIncl (S : Subspace K V) : VecHom K ↥S V where
  toFun := fun x => x.1
  map_add' := fun x y => subspaceAdd_val S x y
  map_smul' := fun c x => subspaceSMul_val S c x

-- Reference: definitional peel of `subspaceIncl`.
/-- The inclusion applies as the underlying value. -/
theorem subspaceIncl_apply (S : Subspace K V) (x : ↥S) : subspaceIncl S x = x.1 := rfl
-- Reference: Axler, Ch. 1; congruence of the additivity law.
/-- Pointwise equal linear maps agree on sums. -/
theorem vecHom_eq_add (f g : VecHom K V W) {x y : V} (hx : f x = g x) (hy : f y = g y) :
    f (x + y) = g (x + y) :=
  Eq.trans (f.map_add' x y)
    (Eq.trans (congrArg (fun t => t + f y) hx)
      (Eq.trans (congrArg (fun t => g x + t) hy) (g.map_add' x y).symm))

-- Reference: Axler, Ch. 1; `vecHom_map_neg`.
/-- Pointwise equal linear maps agree on negations. -/
theorem vecHom_eq_neg (f g : VecHom K V W) {x : V} (hx : f x = g x) : f (-x) = g (-x) :=
  Eq.trans (vecHom_map_neg f x)
    (Eq.trans (congrArg (fun t => -t) hx) (vecHom_map_neg g x).symm)

-- Reference: Axler, Ch. 1; congruence of the homogeneity law.
/-- Pointwise equal linear maps agree on scalar multiples. -/
theorem vecHom_eq_smul (f g : VecHom K V W) (c : K) {x : V} (hx : f x = g x) :
    f (c • x) = g (c • x) :=
  Eq.trans (f.map_smul' c x)
    (Eq.trans (congrArg (fun t => c • t) hx) (g.map_smul' c x).symm)


-- Reference: Mac Lane, CWM 2nd ed., Ch. VIII §1 (p. 191, the kernel of
-- `f - g`); Ch. V §2 (p. 112, equalizers).
/-- The equalizer subspace of `f` and `g`: the kernel of `f - g`, as data. -/
def subspaceKer (f g : VecHom K V W) : Subspace K V where
  carrier := fun x => f x = g x
  zero_mem := Eq.trans (vecHom_map_zero f) (vecHom_map_zero g).symm
  add_mem := fun {_x _y} hx hy => vecHom_eq_add f g hx hy
  neg_mem := fun {_x} hx => vecHom_eq_neg f g hx
  smul_mem := fun c {_x} hx => vecHom_eq_smul f g c hx

-- Reference: Mac Lane, CWM 2nd ed., Ch. VIII §1 (p. 191, images); Hörmann,
-- arXiv:2106.03803, Key Lemma 3.2 (the image construction `N' := p(L')`).
/-- The image of an explicit linear map, as a subspace (carrier: being in the
image). -/
def subspaceImage (f : VecHom K V W) : Subspace K W where
  carrier := fun y => ∃ x, f x = y
  zero_mem := ⟨0, vecHom_map_zero f⟩
  add_mem := fun {_x _y} ⟨a, ha⟩ ⟨b, hb⟩ =>
    ⟨a + b, Eq.trans (f.map_add' a b) (add_eq_add_of_eq ha hb)⟩
  neg_mem := fun {_y} ⟨a, ha⟩ =>
    ⟨-a, Eq.trans (vecHom_map_neg f a) (congrArg (fun t => -t) ha)⟩
  smul_mem := fun c {_y} ⟨a, ha⟩ =>
    ⟨c • a, Eq.trans (f.map_smul' c a) (congrArg (fun t => c • t) ha)⟩

variable {A B C : Type u} [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
  [AddCommGroup C] [Module K C]
-- Reference: Mac Lane, CWM 2nd ed., Ch. III §4 (p. 68); congruence peels of
-- the product operations (`Prod.fst_zero`, `Prod.snd_zero`) and `vecHom_map_zero`.
/-- The zero pair lies in the pullback subspace. -/
theorem pullbackSubspace_zero_mem (f : VecHom K A C) (g : VecHom K B C) :
    f (0 : A × B).1 = g (0 : A × B).2 :=
  Eq.trans (congrArg f Prod.fst_zero)
    (Eq.trans (vecHom_map_zero f)
      (Eq.trans (vecHom_map_zero g).symm (congrArg g Prod.snd_zero).symm))

-- Reference: Mac Lane, CWM 2nd ed., Ch. III §4; `Prod.fst_add`, `Prod.snd_add`.
/-- Addition in the pullback subspace is pointwise. -/
theorem pullbackSubspace_add_mem (f : VecHom K A C) (g : VecHom K B C) {p q : A × B}
    (hp : f p.1 = g p.2) (hq : f q.1 = g q.2) : f (p + q).1 = g (p + q).2 :=
  Eq.trans (congrArg f (Prod.fst_add p q))
    (Eq.trans (f.map_add' p.1 q.1)
      (Eq.trans (add_eq_add_of_eq hp hq)
        (Eq.trans (g.map_add' p.2 q.2).symm (congrArg g (Prod.snd_add p q)).symm)))

-- Reference: Mac Lane, CWM 2nd ed., Ch. III §4; `Prod.fst_neg`, `Prod.snd_neg`,
-- `vecHom_map_neg`.
/-- Negation in the pullback subspace is pointwise. -/
theorem pullbackSubspace_neg_mem (f : VecHom K A C) (g : VecHom K B C) {p : A × B}
    (hp : f p.1 = g p.2) : f (-p).1 = g (-p).2 :=
  Eq.trans (congrArg f (Prod.fst_neg p))
    (Eq.trans (vecHom_map_neg f p.1)
      (Eq.trans (congrArg (fun t => -t) hp)
        (Eq.trans (vecHom_map_neg g p.2).symm (congrArg g (Prod.snd_neg p)).symm)))

-- Reference: Mac Lane, CWM 2nd ed., Ch. III §4; `Prod.smul_fst`, `Prod.smul_snd`.
/-- Scalar action in the pullback subspace is pointwise. -/
theorem pullbackSubspace_smul_mem (f : VecHom K A C) (g : VecHom K B C) (c : K) {p : A × B}
    (hp : f p.1 = g p.2) : f (c • p).1 = g (c • p).2 :=
  Eq.trans (congrArg f (Prod.smul_fst c p))
    (Eq.trans (f.map_smul' c p.1)
      (Eq.trans (congrArg (fun t => c • t) hp)
        (Eq.trans (g.map_smul' c p.2).symm (congrArg g (Prod.smul_snd c p)).symm)))


-- Reference: Mac Lane, CWM 2nd ed., Ch. III §4 (p. 68, pullbacks as limits of
-- cospan diagrams); Hörmann, arXiv:2106.03803, Key Lemma 3.2 and Prop 3.6
-- (pullbacks of monos = intersections `N' ∩ M^n`).
/-- The pullback subspace of `f : A → C` and `g : B → C`: pairs with equal
images — the explicit intersection when `f` and `g` are monomorphisms. -/
def pullbackSubspace (f : VecHom K A C) (g : VecHom K B C) : Subspace K (A × B) where
  carrier := fun p => f p.1 = g p.2
  zero_mem := pullbackSubspace_zero_mem f g
  add_mem := fun {_p _q} hp hq => pullbackSubspace_add_mem f g hp hq
  neg_mem := fun {_p} hp => pullbackSubspace_neg_mem f g hp
  smul_mem := fun c {_p} hp => pullbackSubspace_smul_mem f g c hp

end BoringMath
