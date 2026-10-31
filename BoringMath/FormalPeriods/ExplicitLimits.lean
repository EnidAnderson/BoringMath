/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Data.Quot
import Mathlib.Data.List.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Module.Prod
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Field.Rat
import BoringMath.FormalPeriods.FreeMod
import BoringMath.FormalPeriods.AxiomLint

/-!
# Explicit finite (co)limits for the chase layer + an explicit filtered colimit

Ticket P.3 (issue #95), leaf of the FORMAL PERIODS line. The P.0.4 pin-run
confirmed that mathlib's chosen-limits API (`HasLimit`, `pullback`,
`equalizer`, `HasFiniteLimits`, ...) is `Classical.choice`-backed at the pin
`v4.35.0-rc3` (see `docs/AUDITS/2026-10-30-axiom-lint-pin-run.md`), so this
module builds the computable replacements as DATA-parameterized
constructions (STYLE §2.3: data taken explicitly, never instance-chosen):

* a general explicit linear map `VecHom` between arbitrary carriers of
  vector-space operations (generalizing the P.1 `FreeModHom` to subtype and
  quotient carriers);
* subspaces as data (`Subspace`), and quotients of carriers by subspaces as
  an explicit `Quot` (witness-carrying, `Quot.sound` only — the `FreeTensor`
  precedent);
* the finite (co)limit shapes Hörmann's chase consumes: terminal object and
  binary products (hence finite products, Mac Lane III.5), equalizers
  (kernels of `f - g`), pullbacks of monos (intersections — Key Lemma 3.2,
  Prop 3.6), images (`N' := p(L')`), quotients, pushouts (Prop 3.6), and
  biproducts;
* ONE explicit filtered colimit over a small filtered category of
  basis-carrying spaces: the quotient of the hand-built finitely-supported
  direct sum (an inductive, since `Finsupp.single` is CHOICE-TAINTED at the
  pin) by the diagram-arrow relations — the shape of Theorem 4.1's colimit
  over the span-category `Q̃A`.

Each construction is a named explicit definition plus its universal-property
lemma. The filtered-colimit injection-preservation lemma
(`colimLeg_injective_of_transition_injective`) carries its dies-in-colimit
witness as a finite chain (proof-relevant data, `ColimChain`), per the
constructive form of "filtered colimits preserve injections".

Everything lints CLEAN (`{propext, Quot.sound}` only) — see the
`#lint_axioms` block at the end of this file.

## References
* F. Hörmann, *A note on formal periods*, arXiv:2106.03803 — Key Lemma 3.2
  (pullbacks of monos / intersections `N' ∩ M^n`, images `N' := p(L')`, the
  `(1,…,1,λ)` automorphism), Prop 3.6 (monomorphisms of exact sequences,
  pushouts), Lemma 3.5 (`Q̃A` filtered) and Theorem 4.1 (the colimit over
  `Q̃A`; morphisms map to injections) — verified against the arXiv HTML
  <https://arxiv.org/html/2106.03803>.
* S. Mac Lane, *Categories for the Working Mathematician*, 2nd ed., Springer,
  1998 — Ch. III §3–§4 (p. 62/68: coproducts/colimits, products/limits,
  equalizers, pullbacks, pushouts), Ch. III §5 (p. 72: categories with finite
  products), Ch. V §2 (p. 112: limits by products and equalizers), Ch. VIII
  §1 and §4 (p. 191, 202: kernels/cokernels, the diagram lemmas of the chase),
  Ch. IX §1 (p. 211: filtered (co)limits in Set — the dies-in-colimit
  description of elements). Section titles/pages verified against the book's
  own table of contents <https://d-nb.info/955028914/04>.
  -- REVIEW(citation): pin the exact theorem number inside Mac Lane IX.1 for
  the elementwise description of filtered colimits in Set in review.
* S. Axler, *Linear Algebra Done Right*, 4th ed., Ch. 1 (linear maps,
  subspaces, quotients).
* D. Dummit & R. Foote, *Abstract Algebra*, 3rd ed., §10.4 (generators and
  relations; the quotient construction used by `FreeTensor`).
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

/-! ## Quotients by a subspace, as explicit quotient data -/

-- Reference: Mac Lane, CWM 2nd ed., Ch. VIII §1 (p. 191, cokernels/quotients);
-- the witness-carrying quotient form is the `FreeTensor` precedent (quotient
-- by a data relation, `Quot.sound` only).
/-- The quotient relation of `V` by a subspace `S`: `x` and `y` are related
iff `x - y ∈ S`. -/
def quotRel (S : Subspace K V) (x y : V) : Prop := S.carrier (x - y)

-- Reference: Mac Lane, CWM 2nd ed., Ch. VIII §1 (p. 191); Lean 4 core
-- (`Quot`).
/-- The quotient of a vector-space carrier by a subspace, as an explicit
`Quot` (data-parameterized; only `Quot.sound` is ever used). -/
abbrev VecQuot (S : Subspace K V) : Type u := Quot (quotRel S)

-- Reference: Mac Lane, CWM 2nd ed., Ch. VIII §1 (p. 191, the quotient is a
-- vector space); mathlib `add_sub_add_comm` (cancellation in `V`).
/-- The quotient relation is compatible with addition on the left. -/
theorem quotRelAddLeft (S : Subspace K V) (z x y : V) (h : quotRel S x y) :
    quotRel S (z + x) (z + y) :=
  Eq.subst (motive := S.carrier) (add_sub_add_left_cancel z x y).symm (h : S.carrier (x - y))

-- Reference: Mac Lane, CWM 2nd ed., Ch. VIII §1 (p. 191); mathlib
-- `add_sub_add_comm`, `add_zero`.
/-- The quotient relation is compatible with addition on the right. -/
theorem quotRelAddRight (S : Subspace K V) (x y z : V) (h : quotRel S x y) :
    quotRel S (x + z) (y + z) :=
  Eq.subst (motive := S.carrier) (add_sub_add_right_cancel x y z).symm (h : S.carrier (x - y))

-- Reference: Mac Lane, CWM 2nd ed., Ch. VIII §1 (p. 191); mathlib `smul_sub`.
/-- The quotient relation is compatible with scalar multiplication. -/
theorem quotRelSmul (S : Subspace K V) (c : K) (x y : V) (h : quotRel S x y) :
    quotRel S (c • x) (c • y) :=
  Eq.subst (motive := S.carrier) (smul_sub c x y) (S.smul_mem c h)

-- Reference: Mac Lane, CWM 2nd ed., Ch. VIII §1 (p. 191); mathlib `neg_sub`,
-- `neg_neg`, `sub_eq_add_neg`.
/-- The quotient relation is compatible with negation. -/
theorem quotRelNeg (S : Subspace K V) (x y : V) (h : quotRel S x y) :
    quotRel S (-x) (-y) :=
  Eq.subst (motive := S.carrier) (neg_sub_eq_neg_sub x y).symm (S.neg_mem h)

-- Reference: Lean 4 core (`Quot.map₂`); primitive definitional instance.
/-- Zero of the quotient: the class of `0`. -/
instance quotZero (S : Subspace K V) : Zero (VecQuot S) := ⟨Quot.mk (quotRel S) 0⟩

-- Reference: Lean 4 core (`Quot.map₂`); primitive definitional instance.
/-- Addition on the quotient, descended from addition on `V`. -/
instance quotAdd (S : Subspace K V) : Add (VecQuot S) :=
  ⟨Quot.map₂ (fun x y => x + y) (quotRelAddLeft S) (quotRelAddRight S)⟩

-- Reference: Lean 4 core (`Quot.lift`); Dummit–Foote, §10.4 (the quotient's
-- well-defined operations).
/-- The scalar action on the quotient, descended from the scalar action on
`V`. -/
def quotSmulOp (S : Subspace K V) (c : K) : VecQuot S → VecQuot S :=
  Quot.lift (fun x => Quot.mk (quotRel S) (c • x))
    (fun a b h => Quot.sound (quotRelSmul S c a b h))

-- Reference: Lean 4 core (definitional unfolding of the `SMul` instance).
/-- Scalar multiplication on the quotient. -/
instance quotSMul (S : Subspace K V) : SMul K (VecQuot S) := ⟨quotSmulOp S⟩

-- Reference: Lean 4 core (`Quot.lift`); Mac Lane, CWM 2nd ed., Ch. VIII §1.
/-- Negation on the quotient, descended from negation on `V`. -/
def quotNegOp (S : Subspace K V) : VecQuot S → VecQuot S :=
  Quot.lift (fun x => Quot.mk (quotRel S) (-x))
    (fun a b h => Quot.sound (quotRelNeg S a b h))

-- Reference: Lean 4 core (definitional unfolding of the `Neg` instance).
/-- Negation on the quotient. -/
instance quotNeg (S : Subspace K V) : Neg (VecQuot S) := ⟨quotNegOp S⟩

-- Reference: Lean 4 core (definitional unfolding of the instances); primitive
-- definitional lemmas.
/-- The `0` of the quotient is the class of `0`. -/
theorem quotZeroMk (S : Subspace K V) : (0 : VecQuot S) = Quot.mk (quotRel S) 0 := rfl

-- Reference: mathlib `Mathlib/Data/Quot.lean` (`Quot.map₂_mk`); primitive
-- definitional lemma.
/-- Addition of two classes is the class of the sum. -/
theorem quotAddMk (S : Subspace K V) (x y : V) :
    (Quot.mk (quotRel S) x + Quot.mk (quotRel S) y : VecQuot S)
      = Quot.mk (quotRel S) (x + y) :=
  Quot.map₂_mk (fun a b => a + b) (quotRelAddLeft S) (quotRelAddRight S) x y

-- Reference: Lean 4 core (definitional unfolding of the `SMul` instance);
-- primitive definitional lemma.
/-- The `•` on the quotient unfolds to `quotSmulOp`. -/
theorem quotSmulEq (S : Subspace K V) (c : K) (q : VecQuot S) :
    c • q = quotSmulOp S c q := rfl
-- Reference: mathlib `Mathlib/Data/Quot.lean` (`Quot.lift_mk`); primitive
-- definitional lemma.
/-- `quotSmulOp` applied to a class is the class of the scalar multiple. -/
theorem quotSmulOp_mk (S : Subspace K V) (c : K) (x : V) :
    quotSmulOp S c (Quot.mk (quotRel S) x) = Quot.mk (quotRel S) (c • x) :=
  Quot.lift_mk (fun x => Quot.mk (quotRel S) (c • x))
    (fun a b h => Quot.sound (quotRelSmul S c a b h)) x

-- Reference: Lean 4 core (definitional unfolding of the `Neg` instance);
-- primitive definitional lemma.
/-- The `-` on the quotient unfolds to `quotNegOp`. -/
theorem quotNegEq (S : Subspace K V) (q : VecQuot S) : -q = quotNegOp S q := rfl

-- Reference: mathlib `Mathlib/Data/Quot.lean` (`Quot.lift_mk`); primitive
-- definitional lemma.
/-- `quotNegOp` applied to a class is the class of the negation. -/
theorem quotNegOp_mk (S : Subspace K V) (x : V) :
    quotNegOp S (Quot.mk (quotRel S) x) = Quot.mk (quotRel S) (-x) :=
  Quot.lift_mk (fun x => Quot.mk (quotRel S) (-x))
    (fun a b h => Quot.sound (quotRelNeg S a b h)) x


-- Reference: mathlib `Mathlib/Data/Quot.lean` (`Quot.lift_mk`); primitive
-- definitional lemma.
/-- Scalar multiplication of a class is the class of the scalar multiple. -/
theorem quotSmulMk (S : Subspace K V) (c : K) (x : V) :
    (c • Quot.mk (quotRel S) x : VecQuot S) = Quot.mk (quotRel S) (c • x) :=
  Eq.trans (quotSmulEq S c (Quot.mk (quotRel S) x)) (quotSmulOp_mk S c x)

-- Reference: mathlib `Mathlib/Data/Quot.lean` (`Quot.lift_mk`); primitive
-- definitional lemma.
/-- Negation of a class is the class of the negation. -/
theorem quotNegMk (S : Subspace K V) (x : V) :
    (-Quot.mk (quotRel S) x : VecQuot S) = Quot.mk (quotRel S) (-x) :=
  Eq.trans (quotNegEq S (Quot.mk (quotRel S) x)) (quotNegOp_mk S x)

-- Reference: Mac Lane, CWM 2nd ed., Ch. VIII §1 (p. 191, the quotient map).
/-- The quotient map `V → V/S`, as an explicit linear map. -/
def quotMk (S : Subspace K V) : VecHom K V (VecQuot S) where
  toFun := fun x => Quot.mk (quotRel S) x
  map_add' := fun x y => quotAddMk S x y
  map_smul' := fun c x => quotSmulMk S c x

-- Reference: definitional peel of `quotMk`.
/-- The quotient map sends `x` to its class. -/
theorem quotMk_apply (S : Subspace K V) (x : V) : quotMk S x = Quot.mk (quotRel S) x := rfl

variable {X : Type u} [Add X] [Zero X] [SMul K X]
-- Reference: mathlib `Mathlib/Data/Quot.lean` (`Quot.lift_mk`, `Quot.map₂_mk`);
-- Mac Lane, CWM 2nd ed., Ch. VIII §1 (p. 191, the descended operations).
/-- Additivity of the quotient lift on classes, via the beta rule and
`quotAddMk`. -/
theorem quotLift_add_mk (S : Subspace K V) (h : VecHom K V X)
    (hrel : ∀ x y, quotRel S x y → h x = h y) (a b : V) :
    Quot.lift h (fun x y hab => hrel x y hab)
        (Quot.mk (quotRel S) a + Quot.mk (quotRel S) b)
      = Quot.lift h (fun x y hab => hrel x y hab) (Quot.mk (quotRel S) a)
        + Quot.lift h (fun x y hab => hrel x y hab) (Quot.mk (quotRel S) b) :=
  Eq.trans
    (congrArg (Quot.lift h (fun x y hab => hrel x y hab)) (quotAddMk S a b))
    (Eq.trans (Quot.lift_mk h (fun x y hab => hrel x y hab) (a + b))
      (Eq.trans (h.map_add' a b)
        (add_eq_add_of_eq (Quot.lift_mk h (fun x y hab => hrel x y hab) a)
          (Quot.lift_mk h (fun x y hab => hrel x y hab) b)).symm))

-- Reference: mathlib `Mathlib/Data/Quot.lean` (`Quot.lift_mk`);
-- Mac Lane, CWM 2nd ed., Ch. VIII §1 (p. 191).
/-- Homogeneity of the quotient lift on classes, via the beta rule and
`quotSmulMk`. -/
theorem quotLift_smul_mk (S : Subspace K V) (h : VecHom K V X)
    (hrel : ∀ x y, quotRel S x y → h x = h y) (c : K) (a : V) :
    Quot.lift h (fun x y hab => hrel x y hab) (c • Quot.mk (quotRel S) a)
      = c • Quot.lift h (fun x y hab => hrel x y hab) (Quot.mk (quotRel S) a) :=
  Eq.trans
    (congrArg (Quot.lift h (fun x y hab => hrel x y hab)) (quotSmulMk S c a))
    (Eq.trans (Quot.lift_mk h (fun x y hab => hrel x y hab) (c • a))
      (Eq.trans (h.map_smul' c a)
        (congrArg (fun t => c • t) (Quot.lift_mk h (fun x y hab => hrel x y hab) a)).symm))


-- Reference: Mac Lane, CWM 2nd ed., Ch. VIII §1 (p. 191, the universal
-- property of the quotient); Lean 4 core (`Quot.lift`).
/-- The lift of a linear map `h : V → X` to the quotient `V/S`, given that `h`
respects the quotient relation. -/
def quotLift (S : Subspace K V) (h : VecHom K V X)
    (hrel : ∀ x y, quotRel S x y → h x = h y) : VecHom K (VecQuot S) X where
  toFun := Quot.lift h (fun a b hab => hrel a b hab)
  map_add' := fun q₁ q₂ => Quot.induction_on₂ q₁ q₂ (fun a b => quotLift_add_mk S h hrel a b)
  map_smul' := fun c q => Quot.inductionOn (motive := fun q =>
      Quot.lift h (fun a b hab => hrel a b hab) (c • q)
        = c • Quot.lift h (fun a b hab => hrel a b hab) q) q
    (fun a => quotLift_smul_mk S h hrel c a)

-- Reference: mathlib `Mathlib/Data/Quot.lean` (`Quot.lift_mk`).
/-- Beta rule of the quotient's universal property. -/
theorem quotLift_mk (S : Subspace K V) (h : VecHom K V X)
    (hrel : ∀ x y, quotRel S x y → h x = h y) (x : V) :
    quotLift S h hrel (quotMk S x) = h x :=
  Quot.lift_mk h (fun a b hab => hrel a b hab) x

-- Reference: Mac Lane, CWM 2nd ed., Ch. VIII §1 (p. 191, uniqueness of the
-- factorization through the quotient).
/-- Uniqueness: any explicit linear map out of the quotient agreeing with `h`
on classes is the lift of `h`. -/
theorem quotLift_unique (S : Subspace K V) (h : VecHom K V X)
    (hrel : ∀ x y, quotRel S x y → h x = h y) (k : VecHom K (VecQuot S) X)
    (hk : ∀ x, k (quotMk S x) = h x) : k = quotLift S h hrel :=
  vecHom_ext fun q => Quot.inductionOn q (fun a => hk a)

-- Reference: Mac Lane, CWM 2nd ed., Ch. VIII §1 (p. 191); Axler, Ch. 1.
/-- The kills-form of the quotient's universal property: a linear map that
vanishes on `S` factors through the quotient (target a full vector space). -/
def quotLift_of_kills {Y : Type u} [AddCommGroup Y] [Module K Y] (S : Subspace K V)
    (h : VecHom K V Y) (hS : ∀ s, S.carrier s → h s = 0) : VecHom K (VecQuot S) Y :=
  quotLift S h (fun x y hrel =>
    sub_eq_zero.mp
      (Eq.subst (motive := fun t => t = 0) (vecHom_map_sub h x y) (hS (x - y) hrel)))

-- Reference: Lean 4 core (`Quot.exists_rep`).
/-- Every class in the quotient is the class of some element (surjectivity of
the quotient map). -/
theorem quotMk_surj (S : Subspace K V) (q : VecQuot S) : ∃ x, q = quotMk S x := by
  obtain ⟨x, hx⟩ := Quot.exists_rep q
  exact ⟨x, hx.symm⟩

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

/-! ## Equalizers (kernels of `f - g`) -/

-- Reference: Mac Lane, CWM 2nd ed., Ch. V §2 (p. 112, limits by products and
-- equalizers); Hörmann, arXiv:2106.03803, Key Lemma 3.2.
/-- The equalizer of `f` and `g`: the kernel subspace of `f - g`. -/
def eqSubspace (f g : VecHom K V W) : Subspace K V := subspaceKer f g

-- Reference: Mac Lane, CWM 2nd ed., Ch. V §2 (p. 112, the equalizing arrow).
/-- The inclusion of the equalizer into the source. -/
def eqIncl (f g : VecHom K V W) : VecHom K ↥(eqSubspace f g) V := subspaceIncl _

-- Reference: definitional peel of `eqIncl`.
/-- The equalizer inclusion applies as the underlying value. -/
theorem eqIncl_apply (f g : VecHom K V W) (s : ↥(eqSubspace f g)) :
    eqIncl f g s = s.1 := rfl

-- Reference: Mac Lane, CWM 2nd ed., Ch. V §2 (p. 112, the universal property
-- of the equalizer: any `h` with `f ∘ h = g ∘ h` factors through it).
/-- The factorization of `h` (with `f (h x) = g (h x)`) through the equalizer. -/
def eqLift (f g : VecHom K V W) (h : VecHom K X V)
    (hfg : ∀ x, f (h x) = g (h x)) : VecHom K X ↥(eqSubspace f g) where
  toFun := fun x => ⟨h x, hfg x⟩
  -- Subtype.ext with the pointwise linearity of `h`.
  map_add' := fun x y => Subtype.ext (h.map_add' x y)
  map_smul' := fun c x => Subtype.ext (h.map_smul' c x)

-- Reference: definitional peel of `eqLift`.
/-- The equalizer factorization applies as `x ↦ ⟨h x, _⟩`. -/
theorem eqLift_apply (f g : VecHom K V W) (h : VecHom K X V)
    (hfg : ∀ x, f (h x) = g (h x)) (x : X) : eqLift f g h hfg x = ⟨h x, hfg x⟩ := rfl

-- Reference: definitional peels of `vecHomComp`, `eqLift`, `eqIncl`.
/-- The equalizer inclusion composed with the factorization, pointwise. -/
theorem eqIncl_eqLift_apply (f g : VecHom K V W) (h : VecHom K X V)
    (hfg : ∀ x, f (h x) = g (h x)) (x : X) :
    vecHomComp (eqIncl f g) (eqLift f g h hfg) x = h x :=
  Eq.trans (vecHomComp_apply (eqIncl f g) (eqLift f g h hfg) x)
    (Eq.trans (congrArg (eqIncl f g) (eqLift_apply f g h hfg x))
      (eqIncl_apply f g ⟨h x, hfg x⟩))

-- Reference: definitional peels of `vecHomComp` and `eqIncl`.
/-- The underlying value of a composed equalizer map, pointwise. -/
theorem eqLift_unique_val (f g : VecHom K V W) (h : VecHom K X V)
    (k : VecHom K X ↥(eqSubspace f g)) (hk : vecHomComp (eqIncl f g) k = h) (x : X) :
    (k x).1 = h x :=
  Eq.trans (eqIncl_apply f g (k x)).symm
    (Eq.trans (vecHomComp_apply (eqIncl f g) k x).symm
      (congrFun (congrArg VecHom.toFun hk) x))

-- Reference: Mac Lane, CWM 2nd ed., Ch. V §2 (p. 112, incl ∘ factor = h).
/-- The equalizer inclusion composed with the factorization is `h`. -/
theorem eqIncl_comp_eqLift (f g : VecHom K V W) (h : VecHom K X V)
    (hfg : ∀ x, f (h x) = g (h x)) :
    vecHomComp (eqIncl f g) (eqLift f g h hfg) = h :=
  vecHom_ext fun x => eqIncl_eqLift_apply f g h hfg x

-- Reference: Mac Lane, CWM 2nd ed., Ch. V §2 (p. 112, uniqueness of the
-- equalizer factorization).
/-- Uniqueness of the equalizer factorization. -/
theorem eqLift_unique (f g : VecHom K V W) (h : VecHom K X V)
    (hfg : ∀ x, f (h x) = g (h x)) (k : VecHom K X ↥(eqSubspace f g))
    (hk : vecHomComp (eqIncl f g) k = h) : k = eqLift f g h hfg :=
  vecHom_ext fun x => Subtype.ext (eqLift_unique_val f g h k hk x)

/-! ## Pullbacks of monos (intersections) -/

-- Reference: Mac Lane, CWM 2nd ed., Ch. III §4 (p. 68, the pullback square);
-- Hörmann, arXiv:2106.03803, Key Lemma 3.2 (`N' ∩ M^n` as a pullback of
-- monos), Prop 3.6.
/-- The first projection of the pullback subspace. -/
def pbFst (f : VecHom K A C) (g : VecHom K B C) :
    VecHom K ↥(pullbackSubspace f g) A :=
  vecHomComp (prodFstVec A B) (subspaceIncl (pullbackSubspace f g))

-- Reference: definitional peel of `pbFst`.
/-- The first pullback projection applies as `p ↦ p.1.1`. -/
theorem pbFst_apply (f : VecHom K A C) (g : VecHom K B C)
    (p : ↥(pullbackSubspace f g)) : pbFst f g p = p.1.1 :=
  Eq.trans (vecHomComp_apply (prodFstVec A B) (subspaceIncl (pullbackSubspace f g)) p)
    (Eq.trans (congrArg (prodFstVec A B) (subspaceIncl_apply (pullbackSubspace f g) p))
      (prodFstVec_apply A B p.1))

-- Reference: Mac Lane, CWM 2nd ed., Ch. III §4 (p. 68).
/-- The second projection of the pullback subspace. -/
def pbSnd (f : VecHom K A C) (g : VecHom K B C) :
    VecHom K ↥(pullbackSubspace f g) B :=
  vecHomComp (prodSndVec A B) (subspaceIncl (pullbackSubspace f g))

-- Reference: definitional peel of `pbSnd`.
/-- The second pullback projection applies as `p ↦ p.1.2`. -/
theorem pbSnd_apply (f : VecHom K A C) (g : VecHom K B C)
    (p : ↥(pullbackSubspace f g)) : pbSnd f g p = p.1.2 :=
  Eq.trans (vecHomComp_apply (prodSndVec A B) (subspaceIncl (pullbackSubspace f g)) p)
    (Eq.trans (congrArg (prodSndVec A B) (subspaceIncl_apply (pullbackSubspace f g) p))
      (prodSndVec_apply A B p.1))

-- Reference: Mac Lane, CWM 2nd ed., Ch. III §4 (p. 68, the pullback square
-- commutes: `f ∘ π₁ = g ∘ π₂`).
/-- The pullback square commutes. -/
theorem pb_comm (f : VecHom K A C) (g : VecHom K B C) :
    vecHomComp f (pbFst f g) = vecHomComp g (pbSnd f g) :=
  vecHom_ext fun p => p.2

-- Reference: Mac Lane, CWM 2nd ed., Ch. III §4 (p. 68, the pullback's
-- universal property: the pairing of a commutative pair).
/-- The pairing of a commutative pair `h, k` (with `f ∘ h = g ∘ k`) into the
pullback. -/
def pbPair (f : VecHom K A C) (g : VecHom K B C) (h : VecHom K X A) (k : VecHom K X B)
    (hfg : ∀ x, f (h x) = g (k x)) : VecHom K X ↥(pullbackSubspace f g) where
  toFun := fun x => ⟨(h x, k x), hfg x⟩
  -- Subtype.ext + Prod.ext with the pointwise linearity of `h` and `k`.
  map_add' := fun x y => Subtype.ext (Prod.ext (h.map_add' x y) (k.map_add' x y))
  map_smul' := fun c x => Subtype.ext (Prod.ext (h.map_smul' c x) (k.map_smul' c x))

-- Reference: definitional peel of `pbPair`.
/-- The pullback pairing applies as `x ↦ ⟨(h x, k x), _⟩`. -/
theorem pbPair_apply (f : VecHom K A C) (g : VecHom K B C) (h : VecHom K X A)
    (k : VecHom K X B) (hfg : ∀ x, f (h x) = g (k x)) (x : X) :
    pbPair f g h k hfg x = ⟨(h x, k x), hfg x⟩ := rfl
-- Reference: definitional peels of `vecHomComp`, `pbPair`, `pbFst`.
/-- First pullback projection after pairing, pointwise. -/
theorem pbFst_pbPair_apply (f : VecHom K A C) (g : VecHom K B C) (h : VecHom K X A)
    (k : VecHom K X B) (hfg : ∀ x, f (h x) = g (k x)) (x : X) :
    vecHomComp (pbFst f g) (pbPair f g h k hfg) x = h x :=
  Eq.trans (vecHomComp_apply (pbFst f g) (pbPair f g h k hfg) x)
    (Eq.trans (congrArg (pbFst f g) (pbPair_apply f g h k hfg x))
      (pbFst_apply f g ⟨(h x, k x), hfg x⟩))

-- Reference: definitional peels of `vecHomComp`, `pbPair`, `pbSnd`.
/-- Second pullback projection after pairing, pointwise. -/
theorem pbSnd_pbPair_apply (f : VecHom K A C) (g : VecHom K B C) (h : VecHom K X A)
    (k : VecHom K X B) (hfg : ∀ x, f (h x) = g (k x)) (x : X) :
    vecHomComp (pbSnd f g) (pbPair f g h k hfg) x = k x :=
  Eq.trans (vecHomComp_apply (pbSnd f g) (pbPair f g h k hfg) x)
    (Eq.trans (congrArg (pbSnd f g) (pbPair_apply f g h k hfg x))
      (pbSnd_apply f g ⟨(h x, k x), hfg x⟩))

-- Reference: definitional peels of `vecHomComp` and `pbFst`.
/-- First component of a pullback map composed with `pbFst`, pointwise. -/
theorem pbFst_comp_val (f : VecHom K A C) (g : VecHom K B C)
    (l : VecHom K X ↥(pullbackSubspace f g)) (h : VecHom K X A)
    (hl : vecHomComp (pbFst f g) l = h) (x : X) : (l x).1.1 = h x :=
  Eq.trans (pbFst_apply f g (l x)).symm
    (Eq.trans (vecHomComp_apply (pbFst f g) l x).symm
      (congrFun (congrArg VecHom.toFun hl) x))

-- Reference: definitional peels of `vecHomComp` and `pbSnd`.
/-- Second component of a pullback map composed with `pbSnd`, pointwise. -/
theorem pbSnd_comp_val (f : VecHom K A C) (g : VecHom K B C)
    (l : VecHom K X ↥(pullbackSubspace f g)) (k : VecHom K X B)
    (hl : vecHomComp (pbSnd f g) l = k) (x : X) : (l x).1.2 = k x :=
  Eq.trans (pbSnd_apply f g (l x)).symm
    (Eq.trans (vecHomComp_apply (pbSnd f g) l x).symm
      (congrFun (congrArg VecHom.toFun hl) x))


-- Reference: Mac Lane, CWM 2nd ed., Ch. III §4 (p. 68, π₁ ∘ ⟨h, k⟩ = h).
/-- First pullback projection after pairing is `h`. -/
theorem pbFst_comp_pbPair (f : VecHom K A C) (g : VecHom K B C) (h : VecHom K X A)
    (k : VecHom K X B) (hfg : ∀ x, f (h x) = g (k x)) :
    vecHomComp (pbFst f g) (pbPair f g h k hfg) = h :=
  vecHom_ext fun x => pbFst_pbPair_apply f g h k hfg x

-- Reference: Mac Lane, CWM 2nd ed., Ch. III §4 (p. 68, π₂ ∘ ⟨h, k⟩ = k).
/-- Second pullback projection after pairing is `k`. -/
theorem pbSnd_comp_pbPair (f : VecHom K A C) (g : VecHom K B C) (h : VecHom K X A)
    (k : VecHom K X B) (hfg : ∀ x, f (h x) = g (k x)) :
    vecHomComp (pbSnd f g) (pbPair f g h k hfg) = k :=
  vecHom_ext fun x => pbSnd_pbPair_apply f g h k hfg x

-- Reference: Mac Lane, CWM 2nd ed., Ch. III §4 (p. 68, uniqueness of the
-- pullback pairing).
/-- Uniqueness of the pullback pairing. -/
theorem pbPair_unique (f : VecHom K A C) (g : VecHom K B C) (h : VecHom K X A)
    (k : VecHom K X B) (hfg : ∀ x, f (h x) = g (k x)) (l : VecHom K X ↥(pullbackSubspace f g))
    (hl1 : vecHomComp (pbFst f g) l = h) (hl2 : vecHomComp (pbSnd f g) l = k) :
    l = pbPair f g h k hfg :=
  vecHom_ext fun x =>
    Subtype.ext (Prod.ext (pbFst_comp_val f g l h hl1 x) (pbSnd_comp_val f g l k hl2 x))

-- Reference: Mac Lane, CWM 2nd ed., Ch. III §4 (p. 68, the pullback square
-- commutes); the carrier equalities of the pullback subspace.
/-- Equal second projections force equal first components. -/
theorem pb_fst_eq_of_pbSnd_eq (f : VecHom K A C) (g : VecHom K B C)
    (hf : Function.Injective f) {p q : ↥(pullbackSubspace f g)}
    (hpq : pbSnd f g p = pbSnd f g q) : p.1.1 = q.1.1 :=
  hf (Eq.trans p.2 (Eq.trans (congrArg g hpq) q.2.symm))

-- Reference: Mac Lane, CWM 2nd ed., Ch. III §4 (p. 68: the pullback of a
-- monomorphism is a monomorphism) — the intersection fact behind Hörmann's
-- `N' ∩ M^n` (arXiv:2106.03803, Key Lemma 3.2).
/-- Pullback of a mono is a mono: if `f` is injective, so is the second
projection of the pullback. -/
theorem pbSnd_injective_of_f_injective (f : VecHom K A C) (g : VecHom K B C)
    (hf : Function.Injective f) : Function.Injective (pbSnd f g) :=
  fun _p _q hpq => Subtype.ext (Prod.ext (pb_fst_eq_of_pbSnd_eq f g hf hpq) hpq)

/-! ## Images (the `N' := p(L')` construction) -/

-- Reference: Mac Lane, CWM 2nd ed., Ch. VIII §1 (p. 191, the image as a
-- subobject); Hörmann, arXiv:2106.03803, Key Lemma 3.2 (`N' := p(L')`).
/-- The image subspace of `f`. -/
def imageSubspace (f : VecHom K V W) : Subspace K W := subspaceImage f

-- Reference: Mac Lane, CWM 2nd ed., Ch. VIII §1 (p. 191, image inclusion).
/-- The inclusion of the image into the target. -/
def imageIncl (f : VecHom K V W) : VecHom K ↥(imageSubspace f) W :=
  subspaceIncl (imageSubspace f)

-- Reference: definitional peel of `imageIncl`.
/-- The image inclusion applies as the underlying value. -/
theorem imageIncl_apply (f : VecHom K V W) (s : ↥(imageSubspace f)) :
    imageIncl f s = s.1 := rfl

-- Reference: Mac Lane, CWM 2nd ed., Ch. VIII §1 (p. 191, every map factors
-- through its image); Hörmann, arXiv:2106.03803, Key Lemma 3.2.
/-- The factorization of `f` through its image: `x ↦ ⟨f x, ⟨x, rfl⟩⟩`. -/
def imageFactor (f : VecHom K V W) : VecHom K V ↥(imageSubspace f) where
  toFun := fun x => ⟨f x, ⟨x, rfl⟩⟩
  -- Subtype.ext with the pointwise linearity of `f`.
  map_add' := fun x y => Subtype.ext (f.map_add' x y)
  map_smul' := fun c x => Subtype.ext (f.map_smul' c x)

-- Reference: definitional peel of `imageFactor`.
/-- The image factorization applies as `x ↦ ⟨f x, ⟨x, rfl⟩⟩`. -/
theorem imageFactor_apply (f : VecHom K V W) (x : V) :
    imageFactor f x = ⟨f x, ⟨x, rfl⟩⟩ := rfl

-- Reference: definitional peels of `vecHomComp`, `imageFactor`, `imageIncl`.
/-- The image inclusion composed with the factorization, pointwise. -/
theorem imageIncl_imageFactor_apply (f : VecHom K V W) (x : V) :
    vecHomComp (imageIncl f) (imageFactor f) x = f x :=
  Eq.trans (vecHomComp_apply (imageIncl f) (imageFactor f) x)
    (Eq.trans (congrArg (imageIncl f) (imageFactor_apply f x))
      (imageIncl_apply f ⟨f x, ⟨x, rfl⟩⟩))

-- Reference: Mac Lane, CWM 2nd ed., Ch. VIII §1 (p. 191, image ∘ factor = f).
/-- The image inclusion composed with the factorization is `f`. -/
theorem imageIncl_comp_imageFactor (f : VecHom K V W) :
    vecHomComp (imageIncl f) (imageFactor f) = f :=
  vecHom_ext fun x => imageIncl_imageFactor_apply f x

-- Reference: Mac Lane, CWM 2nd ed., Ch. VIII §1 (p. 191, the image inclusion
-- is a monomorphism).
/-- The image inclusion is injective. -/
theorem imageIncl_injective (f : VecHom K V W) :
    Function.Injective (imageIncl f) :=
  Subtype.val_injective

-- Reference: Mac Lane, CWM 2nd ed., Ch. VIII §1 (p. 191, the factorization is
-- an epimorphism).
/-- The factorization onto the image is surjective. -/
theorem imageFactor_surjective (f : VecHom K V W) :
    Function.Surjective (imageFactor f) := by
  intro y
  -- y : ↥(imageSubspace f); its carrier proof gives a preimage.
  obtain ⟨x, hx⟩ := y.2
  exact ⟨x, Subtype.ext hx⟩

/-! ## Pushouts (Prop 3.6 of Hörmann) -/

variable {Z U T : Type u} [AddCommGroup Z] [Module K Z] [AddCommGroup U] [Module K U]
  [AddCommGroup T] [Module K T]


-- Reference: Axler, Ch. 1; `g.map_add'`, `neg_add`, `Prod.snd_add`.
/-- Second component of the diagonal's additivity law. -/
theorem pushoutDiag_add_snd (f : VecHom K Z U) (g : VecHom K Z T) (z w : Z) :
    -g (z + w) = ((f z, -g z) + (f w, -g w)).2 :=
  Eq.trans (congrArg (fun t => -t) (g.map_add' z w))
    (Eq.trans (neg_add (g z) (g w)) (Prod.snd_add (f z, -g z) (f w, -g w)).symm)

-- Reference: Axler, Ch. 1; `g.map_smul'`, `smul_neg`, `Prod.smul_snd`.
/-- Second component of the diagonal's homogeneity law. -/
theorem pushoutDiag_smul_snd (f : VecHom K Z U) (g : VecHom K Z T) (c : K) (z : Z) :
    -g (c • z) = (c • (f z, -g z)).2 :=
  Eq.trans (congrArg (fun t => -t) (g.map_smul' c z))
    (Eq.trans (smul_neg c (g z)).symm (Prod.smul_snd c (f z, -g z)).symm)

-- Reference: Mac Lane, CWM 2nd ed., Ch. III §3 (p. 62, pushouts as colimits
-- of span diagrams); Hörmann, arXiv:2106.03803, Prop 3.6.
/-- The diagonal `z ↦ (f z, -g z)` into the product, whose image is the
subspace by which the pushout quotients. -/
def pushoutDiag (f : VecHom K Z U) (g : VecHom K Z T) : VecHom K Z (U × T) where
  toFun := fun z => (f z, -g z)
  map_add' := fun z w => Prod.ext (f.map_add' z w) (pushoutDiag_add_snd f g z w)
  map_smul' := fun c z => Prod.ext (f.map_smul' c z) (pushoutDiag_smul_snd f g c z)

-- Reference: definitional peel of `pushoutDiag`.
/-- The diagonal applies as `z ↦ (f z, -g z)`. -/
theorem pushoutDiag_apply (f : VecHom K Z U) (g : VecHom K Z T) (z : Z) :
    pushoutDiag f g z = (f z, -g z) := rfl

-- Reference: Mac Lane, CWM 2nd ed., Ch. III §3 (p. 62, the pushout
-- construction); Hörmann, arXiv:2106.03803, Prop 3.6.
/-- The subspace of `X × Y` by which the pushout quotients: the image of the
diagonal. -/
def pushoutSubspace (f : VecHom K Z U) (g : VecHom K Z T) : Subspace K (U × T) :=
  subspaceImage (pushoutDiag f g)

-- Reference: Mac Lane, CWM 2nd ed., Ch. VIII §1 (p. 191, cokernel of the
-- diagonal = pushout).
/-- The pushout object: `(X × Y) / {(f z, -g z)}`. -/
abbrev PushoutObj (f : VecHom K Z U) (g : VecHom K Z T) : Type u :=
  VecQuot (pushoutSubspace f g)

-- Reference: Axler, Ch. 1 (`x ↦ (x, 0)` is linear).
/-- The left inclusion `X → X × Y`, as an explicit linear map. -/
def inlVec (M N : Type u) [AddZeroClass M] [SMulZeroClass K M]
    [AddZeroClass N] [SMulZeroClass K N] : VecHom K M (M × N) where
  toFun := fun x => (x, 0)
  -- Prod.ext; the second component: `0 = 0 + 0` is `(add_zero 0).symm`.
  map_add' := fun _ _ => Prod.ext rfl (add_zero (0 : N)).symm
  -- Prod.ext; the second component: `0 = c • 0` is `(smul_zero c).symm`.
  map_smul' := fun c _ => Prod.ext rfl (smul_zero c).symm

-- Reference: definitional peel of `inlVec`.
/-- The left inclusion applies as `x ↦ (x, 0)`. -/
theorem inlVec_apply (M N : Type u) [AddZeroClass M] [SMulZeroClass K M]
    [AddZeroClass N] [SMulZeroClass K N] (x : M) : inlVec (K := K) M N x = (x, 0) := rfl

-- Reference: Axler, Ch. 1 (`y ↦ (0, y)` is linear).
/-- The right inclusion `Y → X × Y`, as an explicit linear map. -/
def inrVec (M N : Type u) [AddZeroClass M] [SMulZeroClass K M]
    [AddZeroClass N] [SMulZeroClass K N] : VecHom K N (M × N) where
  toFun := fun y => (0, y)
  -- Prod.ext; the first component: `0 = 0 + 0` is `(add_zero 0).symm`.
  map_add' := fun _ _ => Prod.ext (add_zero (0 : M)).symm rfl
  map_smul' := fun c _ => Prod.ext (smul_zero c).symm rfl

-- Reference: definitional peel of `inrVec`.
/-- The right inclusion applies as `y ↦ (0, y)`. -/
theorem inrVec_apply (M N : Type u) [AddZeroClass M] [SMulZeroClass K M]
    [AddZeroClass N] [SMulZeroClass K N] (y : N) : inrVec (K := K) M N y = (0, y) := rfl

-- Reference: Mac Lane, CWM 2nd ed., Ch. III §3 (p. 62, the pushout's left
-- injection); Hörmann, arXiv:2106.03803, Prop 3.6.
/-- The left injection into the pushout. -/
def poInl (f : VecHom K Z U) (g : VecHom K Z T) :
    VecHom K U (PushoutObj f g) :=
  vecHomComp (quotMk (pushoutSubspace f g)) (inlVec U T)

-- Reference: definitional peel of `poInl`.
/-- The left injection applies as `x ↦ ⟦(x, 0)⟧`. -/
theorem poInl_apply (f : VecHom K Z U) (g : VecHom K Z T) (x : U) :
    poInl f g x = quotMk (pushoutSubspace f g) (x, 0) :=
  Eq.trans (vecHomComp_apply (quotMk (pushoutSubspace f g)) (inlVec U T) x)
    (congrArg (quotMk (pushoutSubspace f g)) (inlVec_apply U T x))

-- Reference: Mac Lane, CWM 2nd ed., Ch. III §3 (p. 62, the pushout's right
-- injection).
/-- The right injection into the pushout. -/
def poInr (f : VecHom K Z U) (g : VecHom K Z T) :
    VecHom K T (PushoutObj f g) :=
  vecHomComp (quotMk (pushoutSubspace f g)) (inrVec U T)

-- Reference: definitional peel of `poInr`.
/-- The right injection applies as `y ↦ ⟦(0, y)⟧`. -/
theorem poInr_apply (f : VecHom K Z U) (g : VecHom K Z T) (y : T) :
    poInr f g y = quotMk (pushoutSubspace f g) (0, y) :=
  Eq.trans (vecHomComp_apply (quotMk (pushoutSubspace f g)) (inrVec U T) y)
    (congrArg (quotMk (pushoutSubspace f g)) (inrVec_apply U T y))

-- Reference: Mac Lane, CWM 2nd ed., Ch. III §3 (p. 62, the pushout square
-- commutes); Hörmann, arXiv:2106.03803, Prop 3.6; `sub_zero`, `zero_sub`.
/-- The difference of the two diagonal representatives is on the diagonal. -/
theorem po_diag_sub (f : VecHom K Z U) (g : VecHom K Z T) (z : Z) :
    (f z, 0) - (0, g z) = (f z, -g z) :=
  Prod.ext (sub_zero (f z)) (zero_sub (g z))

-- Reference: Mac Lane, CWM 2nd ed., Ch. III §3 (p. 62); `Quot.sound`, the
-- diagonal image.
/-- The classes of `(f z, 0)` and `(0, g z)` agree in the pushout quotient. -/
theorem po_rel_diag (f : VecHom K Z U) (g : VecHom K Z T) (z : Z) :
    quotRel (pushoutSubspace f g) (f z, 0) (0, g z) :=
  Eq.subst (motive := (pushoutSubspace f g).carrier) (po_diag_sub f g z).symm ⟨z, rfl⟩

-- Reference: definitional peels of `vecHomComp`, `poInl`, `quotMk`.
/-- The left pushout injection composed with `f`, pointwise. -/
theorem poInl_f_apply (f : VecHom K Z U) (g : VecHom K Z T) (z : Z) :
    vecHomComp (poInl f g) f z
      = Quot.mk (quotRel (pushoutSubspace f g)) (f z, 0) :=
  Eq.trans (vecHomComp_apply (poInl f g) f z)
    (Eq.trans (poInl_apply f g (f z)) (quotMk_apply (pushoutSubspace f g) (f z, 0)))

-- Reference: definitional peels of `vecHomComp`, `poInr`, `quotMk`.
/-- The right pushout injection composed with `g`, pointwise. -/
theorem poInr_g_apply (f : VecHom K Z U) (g : VecHom K Z T) (z : Z) :
    vecHomComp (poInr f g) g z
      = Quot.mk (quotRel (pushoutSubspace f g)) (0, g z) :=
  Eq.trans (vecHomComp_apply (poInr f g) g z)
    (Eq.trans (poInr_apply f g (g z)) (quotMk_apply (pushoutSubspace f g) (0, g z)))

-- Reference: Mac Lane, CWM 2nd ed., Ch. III §3 (p. 62, the pushout square
-- commutes: `poInl ∘ f = poInr ∘ g`); Hörmann, arXiv:2106.03803, Prop 3.6.
/-- The pushout square commutes. -/
theorem po_comm (f : VecHom K Z U) (g : VecHom K Z T) :
    vecHomComp (poInl f g) f = vecHomComp (poInr f g) g :=
  vecHom_ext fun z =>
    Eq.trans (poInl_f_apply f g z)
      (Eq.trans (Quot.sound (po_rel_diag f g z)) (poInr_g_apply f g z).symm)

-- Reference: Axler, Ch. 1; `Prod.fst_add`, `Prod.snd_add`, `add_add_add_comm`.
/-- Additivity of the sum map out of a product. -/
theorem sumVec_add (h : VecHom K U W) (k : VecHom K T W) (p q : U × T) :
    h (p + q).1 + k (p + q).2 = (h p.1 + k p.2) + (h q.1 + k q.2) :=
  Eq.trans
    (add_eq_add_of_eq (congrArg h (Prod.fst_add p q)) (congrArg k (Prod.snd_add p q)))
    (Eq.trans (add_eq_add_of_eq (h.map_add' p.1 q.1) (k.map_add' p.2 q.2))
      (add_add_add_comm (h p.1) (h q.1) (k p.2) (k q.2)))

-- Reference: Axler, Ch. 1; `Prod.smul_fst`, `Prod.smul_snd`, `smul_add`.
/-- Homogeneity of the sum map out of a product. -/
theorem sumVec_smul (h : VecHom K U W) (k : VecHom K T W) (c : K) (p : U × T) :
    h (c • p).1 + k (c • p).2 = c • (h p.1 + k p.2) :=
  Eq.trans
    (add_eq_add_of_eq (congrArg h (Prod.smul_fst c p)) (congrArg k (Prod.smul_snd c p)))
    (Eq.trans (add_eq_add_of_eq (h.map_smul' c p.1) (k.map_smul' c p.2))
      (smul_add c (h p.1) (k p.2)).symm)

-- Reference: Axler, Ch. 1 (the sum of two linear maps out of a product is
-- linear).
/-- The sum of two explicit linear maps out of a product: `p ↦ h p.1 + k p.2`. -/
def sumVec (h : VecHom K U W) (k : VecHom K T W) : VecHom K (U × T) W where
  toFun := fun p => h p.1 + k p.2
  map_add' := fun p q => sumVec_add h k p q
  map_smul' := fun c p => sumVec_smul h k c p

-- Reference: definitional peel of `sumVec`.
/-- The sum map applies as `p ↦ h p.1 + k p.2`. -/
theorem sumVec_apply (h : VecHom K U W) (k : VecHom K T W) (p : U × T) :
    sumVec h k p = h p.1 + k p.2 := rfl

-- Reference: Mac Lane, CWM 2nd ed., Ch. III §3 (p. 62); the diagonal vanishes
-- under `sumVec h k` (`hcomm`, `vecHom_map_neg`, `add_neg_cancel`).
/-- The sum map vanishes on the diagonal image: `sumVec h k (x - y) = 0` when
`x - y` is in the pushout subspace. -/
theorem poLiftRel_sub {W : Type u} [AddCommGroup W] [Module K W] (f : VecHom K Z U)
    (g : VecHom K Z T) (h : VecHom K U W) (k : VecHom K T W)
    (hcomm : ∀ z, h (f z) = k (g z)) (x y : U × T)
    (hrel : quotRel (pushoutSubspace f g) x y) : sumVec h k (x - y) = 0 :=
  (hrel : ∃ z, pushoutDiag f g z = x - y).elim fun z hz =>
    Eq.subst (motive := fun t => sumVec h k t = 0) hz
      (Eq.trans (sumVec_apply h k (pushoutDiag f g z))
        (Eq.trans (add_eq_add_of_eq (hcomm z) (vecHom_map_neg k (g z)))
          (add_neg_cancel (k (g z)))))

-- Reference: Mac Lane, CWM 2nd ed., Ch. III §3 (p. 62, the pushout's
-- universal property); Hörmann, arXiv:2106.03803, Prop 3.6.
/-- The relation-respect proof for the pushout lift: `sumVec h k` respects the
quotient relation because its values on the diagonal image vanish. -/
theorem poLiftRel {W : Type u} [AddCommGroup W] [Module K W] (f : VecHom K Z U)
    (g : VecHom K Z T) (h : VecHom K U W) (k : VecHom K T W)
    (hcomm : ∀ z, h (f z) = k (g z)) :
    ∀ x y, quotRel (pushoutSubspace f g) x y → sumVec h k x = sumVec h k y :=
  fun x y hrel =>
    sub_eq_zero.mp
      (Eq.subst (motive := fun t => t = 0) (vecHom_map_sub (sumVec h k) x y)
        (poLiftRel_sub f g h k hcomm x y hrel))

-- Reference: Mac Lane, CWM 2nd ed., Ch. III §3 (p. 62, the pushout's
-- universal property); Hörmann, arXiv:2106.03803, Prop 3.6.
/-- The lift of a commutative pair `(h, k)` (with `h ∘ f = k ∘ g`) out of the
pushout. -/
def poLift {W : Type u} [AddCommGroup W] [Module K W] (f : VecHom K Z U)
    (g : VecHom K Z T) (h : VecHom K U W) (k : VecHom K T W)
    (hcomm : ∀ z, h (f z) = k (g z)) : VecHom K (PushoutObj f g) W :=
  quotLift (pushoutSubspace f g) (sumVec h k) (poLiftRel f g h k hcomm)

-- Reference: definitional peel of `poLift`.
/-- The pushout lift applies as the `quotLift` of the sum map. -/
theorem poLift_apply {W : Type u} [AddCommGroup W] [Module K W] (f : VecHom K Z U)
    (g : VecHom K Z T) (h : VecHom K U W) (k : VecHom K T W)
    (hcomm : ∀ z, h (f z) = k (g z)) (q : PushoutObj f g) :
    poLift f g h k hcomm q =
      quotLift (pushoutSubspace f g) (sumVec h k) (poLiftRel f g h k hcomm) q := rfl
-- Reference: definitional peels of `vecHomComp`, `poInl`, `poLift`,
-- `quotLift_mk`, `sumVec`; `vecHom_map_zero`, `add_zero`.
/-- The pushout lift composed with the left injection, pointwise. -/
theorem poLift_poInl_apply {W : Type u} [AddCommGroup W] [Module K W] (f : VecHom K Z U)
    (g : VecHom K Z T) (h : VecHom K U W) (k : VecHom K T W)
    (hcomm : ∀ z, h (f z) = k (g z)) (x : U) :
    vecHomComp (poLift f g h k hcomm) (poInl f g) x = h x :=
  Eq.trans (vecHomComp_apply (poLift f g h k hcomm) (poInl f g) x)
    (Eq.trans (congrArg (poLift f g h k hcomm) (poInl_apply f g x))
      (Eq.trans (poLift_apply f g h k hcomm (quotMk (pushoutSubspace f g) (x, 0)))
        (Eq.trans
          (quotLift_mk (pushoutSubspace f g) (sumVec h k) (poLiftRel f g h k hcomm) (x, 0))
          (Eq.trans (sumVec_apply h k (x, 0))
            (Eq.trans (congrArg (fun t => h x + t) (vecHom_map_zero k)) (add_zero (h x)))))))

-- Reference: definitional peels of `vecHomComp`, `poInr`, `poLift`,
-- `quotLift_mk`, `sumVec`; `vecHom_map_zero`, `zero_add`.
/-- The pushout lift composed with the right injection, pointwise. -/
theorem poLift_poInr_apply {W : Type u} [AddCommGroup W] [Module K W] (f : VecHom K Z U)
    (g : VecHom K Z T) (h : VecHom K U W) (k : VecHom K T W)
    (hcomm : ∀ z, h (f z) = k (g z)) (y : T) :
    vecHomComp (poLift f g h k hcomm) (poInr f g) y = k y :=
  Eq.trans (vecHomComp_apply (poLift f g h k hcomm) (poInr f g) y)
    (Eq.trans (congrArg (poLift f g h k hcomm) (poInr_apply f g y))
      (Eq.trans (poLift_apply f g h k hcomm (quotMk (pushoutSubspace f g) (0, y)))
        (Eq.trans
          (quotLift_mk (pushoutSubspace f g) (sumVec h k) (poLiftRel f g h k hcomm) (0, y))
          (Eq.trans (sumVec_apply h k (0, y))
            (Eq.trans (congrArg (fun t => t + k y) (vecHom_map_zero h)) (zero_add (k y)))))))


-- Reference: Mac Lane, CWM 2nd ed., Ch. III §3 (p. 62, poLift ∘ poInl = h).
/-- The pushout lift composed with the left injection is `h`. -/
theorem poLift_comp_poInl {W : Type u} [AddCommGroup W] [Module K W] (f : VecHom K Z U)
    (g : VecHom K Z T) (h : VecHom K U W) (k : VecHom K T W)
    (hcomm : ∀ z, h (f z) = k (g z)) :
    vecHomComp (poLift f g h k hcomm) (poInl f g) = h :=
  vecHom_ext fun x => poLift_poInl_apply f g h k hcomm x

-- Reference: Mac Lane, CWM 2nd ed., Ch. III §3 (p. 62, poLift ∘ poInr = k).
/-- The pushout lift composed with the right injection is `k`. -/
theorem poLift_comp_poInr {W : Type u} [AddCommGroup W] [Module K W] (f : VecHom K Z U)
    (g : VecHom K Z T) (h : VecHom K U W) (k : VecHom K T W)
    (hcomm : ∀ z, h (f z) = k (g z)) :
    vecHomComp (poLift f g h k hcomm) (poInr f g) = k :=
  vecHom_ext fun y => poLift_poInr_apply f g h k hcomm y

-- Reference: Mac Lane, CWM 2nd ed., Ch. III §3 (p. 62); `quotMk_apply`,
-- `quotAddMk`, `Prod.ext`, `add_zero`, `zero_add`.
/-- The class of a pair splits as the sum of the two axis classes. -/
theorem poLift_unique_class (f : VecHom K Z U)
    (g : VecHom K Z T) (p : U × T) :
    quotMk (pushoutSubspace f g) p
      = quotMk (pushoutSubspace f g) (p.1, 0) + quotMk (pushoutSubspace f g) (0, p.2) :=
  Eq.trans (quotMk_apply (pushoutSubspace f g) p)
    ((Eq.trans (add_eq_add_of_eq (quotMk_apply (pushoutSubspace f g) (p.1, 0))
          (quotMk_apply (pushoutSubspace f g) (0, p.2)))
        (Eq.trans (quotAddMk (pushoutSubspace f g) (p.1, 0) (0, p.2))
          (congrArg (Quot.mk (quotRel (pushoutSubspace f g)))
            (Prod.ext (add_zero p.1) (zero_add p.2))))).symm)

-- Reference: Mac Lane, CWM 2nd ed., Ch. III §3 (p. 62, uniqueness of the
-- pushout lift); `poLift_unique_class`, `poInl_apply`, `poInr_apply`.
/-- The pushout lift uniqueness computation on a class of a pair. -/
theorem poLift_unique_apply {W : Type u} [AddCommGroup W] [Module K W] (f : VecHom K Z U)
    (g : VecHom K Z T) (h : VecHom K U W) (k : VecHom K T W)
    (_hcomm : ∀ z, h (f z) = k (g z)) (l : VecHom K (PushoutObj f g) W)
    (hl1 : vecHomComp l (poInl f g) = h) (hl2 : vecHomComp l (poInr f g) = k) (p : U × T) :
    l (quotMk (pushoutSubspace f g) p) = sumVec h k p :=
  Eq.trans (congrArg l (poLift_unique_class f g p))
    (Eq.trans
      (l.map_add' (quotMk (pushoutSubspace f g) (p.1, 0))
        (quotMk (pushoutSubspace f g) (0, p.2)))
      (Eq.trans
        (add_eq_add_of_eq
          (Eq.trans (congrArg l (poInl_apply f g p.1).symm)
            (congrFun (congrArg VecHom.toFun hl1) p.1))
          (Eq.trans (congrArg l (poInr_apply f g p.2).symm)
            (congrFun (congrArg VecHom.toFun hl2) p.2)))
        (sumVec_apply h k p).symm))

-- Reference: Mac Lane, CWM 2nd ed., Ch. III §3 (p. 62, uniqueness of the
-- pushout lift).
/-- Uniqueness of the pushout lift. -/
theorem poLift_unique {W : Type u} [AddCommGroup W] [Module K W] (f : VecHom K Z U)
    (g : VecHom K Z T) (h : VecHom K U W) (k : VecHom K T W)
    (hcomm : ∀ z, h (f z) = k (g z)) (l : VecHom K (PushoutObj f g) W)
    (hl1 : vecHomComp l (poInl f g) = h) (hl2 : vecHomComp l (poInr f g) = k) :
    l = poLift f g h k hcomm :=
  quotLift_unique (pushoutSubspace f g) (sumVec h k) (poLiftRel f g h k hcomm) l
    (fun p => poLift_unique_apply f g h k hcomm l hl1 hl2 p)

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

/-! ## The explicit filtered colimit -/

-- Reference: Mac Lane, CWM 2nd ed., Ch. IX §1 (p. 211, filtered (co)limits);
-- Hörmann, arXiv:2106.03803, Lemma 3.5 (`Q̃A` is filtered) and Theorem 4.1
-- (the colimit over `Q̃A`). All filteredness witnesses are DATA (Sigma
-- types), never instance-chosen (STYLE §2.3).
/-- A small filtered category, as explicit data: objects, hom types,
identity and composition with the three laws, and the filteredness witnesses
as data (a nonempty object, upper bounds, and coequalizing arrows). -/
structure FilteredCat where
  Obj : Type u
  Hom : Obj → Obj → Type u
  id : (i : Obj) → Hom i i
  comp : {i j k : Obj} → Hom j k → Hom i j → Hom i k
  id_comp : ∀ {i j : Obj} (f : Hom i j), comp (id j) f = f
  comp_id : ∀ {i j : Obj} (f : Hom i j), comp f (id i) = f
  assoc : ∀ {i j k l : Obj} (f : Hom i j) (g : Hom j k) (h : Hom k l),
    comp h (comp g f) = comp (comp h g) f
  nonemptyObj : Obj
  upperBound : (i j : Obj) → Σ k : Obj, Hom i k × Hom j k
  coequalize : {i j : Obj} → (f g : Hom i j) → Σ k : Obj, Σ h : Hom j k,
    PLift (comp h f = comp h g)

-- Reference: Hörmann, arXiv:2106.03803, Theorem 4.1 (a diagram over the
-- span-category `Q̃A`); Mac Lane, CWM 2nd ed., Ch. IX §1 (p. 211).
/-- A diagram of basis-carrying spaces over a small filtered category: object
`i` ↦ `FreeMod K (objDim i)`, arrow `f` ↦ a `VecHom`, with functor laws. -/
structure FilteredDiagram (J : FilteredCat) (K : Type u) [Field K] where
  objDim : J.Obj → ℕ
  map : {i j : J.Obj} → J.Hom i j → VecHom K (FreeMod K (objDim i)) (FreeMod K (objDim j))
  map_id : ∀ i, map (J.id i) = vecHomId _
  map_comp : ∀ {i j k : J.Obj} (f : J.Hom i j) (g : J.Hom j k),
    map (J.comp g f) = vecHomComp (map g) (map f)

-- Reference: Hörmann, arXiv:2106.03803, Theorem 4.1 (the colimit as a
-- quotient of a finitely-supported direct sum); built by hand as an inductive
-- because `Finsupp.single` is CHOICE-TAINTED at the pin (P.0.4 census, like
-- `TensorSym` in `FreeTensor`).
/-- The raw formal sums of the free `K`-module on the symbols `⟨i, x⟩` —
the explicit finitely-supported direct sum `⊕ᵢ FreeMod K (objDim i)`. -/
inductive ColimSym (J : FilteredCat) (D : FilteredDiagram J K) : Type u
  | nil : ColimSym J D
  | sym (i : J.Obj) (x : FreeMod K (D.objDim i)) : ColimSym J D
  | add : ColimSym J D → ColimSym J D → ColimSym J D
  | smul : K → ColimSym J D → ColimSym J D

-- Reference: Lean 4 core (definitional instances on the inductive); primitive.
/-- Zero of the formal sums: the empty sum. -/
instance colimSymZero (J : FilteredCat) (D : FilteredDiagram J K) : Zero (ColimSym J D) :=
  ⟨ColimSym.nil⟩

-- Reference: Lean 4 core; primitive definitional instance.
/-- Addition of formal sums. -/
instance colimSymAdd (J : FilteredCat) (D : FilteredDiagram J K) : Add (ColimSym J D) :=
  ⟨ColimSym.add⟩

-- Reference: Lean 4 core; primitive definitional instance.
/-- Scalar multiplication of formal sums. -/
instance colimSymSMul (J : FilteredCat) (D : FilteredDiagram J K) : SMul K (ColimSym J D) :=
  ⟨ColimSym.smul⟩

-- Reference: definitional peels of the `ColimSym` instances; primitive
-- definitional lemmas.
/-- The zero formal sum is `nil`. -/
theorem colimSymZeroEq (J : FilteredCat) (D : FilteredDiagram J K) :
    (0 : ColimSym J D) = ColimSym.nil := rfl

-- Reference: Hörmann, arXiv:2106.03803, Theorem 4.1 (quotient by the
-- relations); the witness-carrying inductive form is the P.DOC ruling
-- (issue #112) and the `TensorChain` precedent in `FreeTensor`.
/-- A witness chain for the equality of two formal sums: data (not a `Prop`),
so the colimit relation carries its proof-relevant finite-chain witness.
Constructors: the congruence laws of the free `K`-module on the symbols, the
linearity of each leg (`addSym`, `smulSym`, `zeroSym`), and the diagram
relations (`arrow`: `sym i x ∼ sym j (D.map f x)`). -/
inductive ColimChain (J : FilteredCat) (D : FilteredDiagram J K) :
    ColimSym J D → ColimSym J D → Type u
  | refl (x : ColimSym J D) : ColimChain J D x x
  | symm {x y : ColimSym J D} (c : ColimChain J D x y) : ColimChain J D y x
  | trans {x y z : ColimSym J D} (c₁ : ColimChain J D x y) (c₂ : ColimChain J D y z) :
      ColimChain J D x z
  | addLeft {x y z : ColimSym J D} (c : ColimChain J D x y) :
      ColimChain J D (ColimSym.add z x) (ColimSym.add z y)
  | addRight {x y z : ColimSym J D} (c : ColimChain J D x y) :
      ColimChain J D (ColimSym.add x z) (ColimSym.add y z)
  | smulC {x y : ColimSym J D} (c : K) (h : ColimChain J D x y) :
      ColimChain J D (ColimSym.smul c x) (ColimSym.smul c y)
  | nilLeft (x : ColimSym J D) : ColimChain J D (ColimSym.add ColimSym.nil x) x
  | nilRight (x : ColimSym J D) : ColimChain J D (ColimSym.add x ColimSym.nil) x
  | addAssoc (x y z : ColimSym J D) :
      ColimChain J D (ColimSym.add (ColimSym.add x y) z)
        (ColimSym.add x (ColimSym.add y z))
  | addComm (x y : ColimSym J D) :
      ColimChain J D (ColimSym.add x y) (ColimSym.add y x)
  | smulNil (c : K) : ColimChain J D (ColimSym.smul c ColimSym.nil) ColimSym.nil
  | smulAdd (c : K) (x y : ColimSym J D) :
      ColimChain J D (ColimSym.smul c (ColimSym.add x y))
        (ColimSym.add (ColimSym.smul c x) (ColimSym.smul c y))
  | addSmul (a b : K) (x : ColimSym J D) :
      ColimChain J D (ColimSym.smul (a + b) x)
        (ColimSym.add (ColimSym.smul a x) (ColimSym.smul b x))
  | oneSmul (x : ColimSym J D) : ColimChain J D (ColimSym.smul 1 x) x
  | zeroSmul (x : ColimSym J D) : ColimChain J D (ColimSym.smul 0 x) ColimSym.nil
  | smulSmul (a b : K) (x : ColimSym J D) :
      ColimChain J D (ColimSym.smul a (ColimSym.smul b x)) (ColimSym.smul (a * b) x)
  | zeroSym (i : J.Obj) : ColimChain J D (ColimSym.sym i 0) ColimSym.nil
  | addSym (i : J.Obj) (x y : FreeMod K (D.objDim i)) :
      ColimChain J D (ColimSym.sym i (x + y))
        (ColimSym.add (ColimSym.sym i x) (ColimSym.sym i y))
  | smulSym (i : J.Obj) (c : K) (x : FreeMod K (D.objDim i)) :
      ColimChain J D (ColimSym.sym i (c • x)) (ColimSym.smul c (ColimSym.sym i x))
  | arrow {i j : J.Obj} (f : J.Hom i j) (x : FreeMod K (D.objDim i)) :
      ColimChain J D (ColimSym.sym i x) (ColimSym.sym j (D.map f x))

-- Reference: Hörmann, arXiv:2106.03803, Theorem 4.1 (the colimit as a
-- quotient); Lean 4 core (`Quot`/`Setoid`).
/-- The colimit relation on formal sums: `x` and `y` are related iff a witness
chain exists (proof-relevant). -/
def colimRel (J : FilteredCat) (D : FilteredDiagram J K) (a b : ColimSym J D) : Prop :=
  Nonempty (ColimChain J D a b)

-- Reference: Lean 4 core (`Setoid`, `Quotient`); the chain constructors give
-- the equivalence laws.
/-- The setoid of formal sums under witness chains. -/
def colimSetoid (J : FilteredCat) (D : FilteredDiagram J K) : Setoid (ColimSym J D) where
  r := colimRel J D
  iseqv := ⟨fun a => ⟨ColimChain.refl a⟩,
    fun {a b} h => by obtain ⟨c⟩ := h; exact ⟨c.symm⟩,
    fun {a b c} h₁ h₂ => by
      obtain ⟨c₁⟩ := h₁; obtain ⟨c₂⟩ := h₂; exact ⟨c₁.trans c₂⟩⟩

-- Reference: Hörmann, arXiv:2106.03803, Theorem 4.1 (the colimit over `Q̃A`);
-- Mac Lane, CWM 2nd ed., Ch. IX §1 (p. 211).
/-- The explicit filtered colimit: the quotient of the finitely-supported
direct sum by the witness-chain relation. -/
abbrev FilteredColim (J : FilteredCat) (D : FilteredDiagram J K) : Type u :=
  Quotient (colimSetoid J D)

-- Reference: Mac Lane, CWM 2nd ed., Ch. IX §1 (p. 211); the chain constructors
-- `addLeft`/`addRight`.
/-- The colimit relation is compatible with formal addition. -/
theorem colimRelAdd (J : FilteredCat) (D : FilteredDiagram J K)
    (a₁ a₂ b₁ b₂ : ColimSym J D) (h₁ : colimRel J D a₁ a₂)
    (h₂ : colimRel J D b₁ b₂) :
    colimRel J D (ColimSym.add a₁ b₁) (ColimSym.add a₂ b₂) := by
  obtain ⟨c₁⟩ := h₁; obtain ⟨c₂⟩ := h₂
  exact ⟨(ColimChain.addRight (z := b₁) c₁).trans (ColimChain.addLeft (z := a₂) c₂)⟩

-- Reference: Mac Lane, CWM 2nd ed., Ch. IX §1 (p. 211); the congruence in the
-- shape expected by `Quotient.map₂`.
/-- The colimit relation is compatible with formal addition, in the
`Quotient.map₂` congruence shape. -/
theorem colimRelAdd' (J : FilteredCat) (D : FilteredDiagram J K)
    ⦃a₁ a₂ : ColimSym J D⦄ (h₁ : colimRel J D a₁ a₂)
    ⦃b₁ b₂ : ColimSym J D⦄ (h₂ : colimRel J D b₁ b₂) :
    colimRel J D (ColimSym.add a₁ b₁) (ColimSym.add a₂ b₂) :=
  colimRelAdd J D a₁ a₂ b₁ b₂ h₁ h₂

-- Reference: Lean 4 core (`Quotient`); primitive definitional instance.
/-- Zero of the colimit: the class of the empty sum. -/
instance colimZero (J : FilteredCat) (D : FilteredDiagram J K) :
    Zero (FilteredColim J D) :=
  ⟨Quotient.mk (colimSetoid J D) ColimSym.nil⟩

-- Reference: Lean 4 core (`Quotient.map₂`); primitive definitional instance.
/-- Addition on the colimit, descended from formal addition. -/
instance colimAdd (J : FilteredCat) (D : FilteredDiagram J K) :
    Add (FilteredColim J D) :=
  ⟨Quotient.map₂ (fun a b => ColimSym.add a b)
    (colimRelAdd' J D)⟩

-- Reference: Lean 4 core (`Quotient.lift`); the chain constructor `smulC`.
/-- The scalar action on the colimit, descended from formal scalar
multiplication. -/
def colimSmulOp (J : FilteredCat) (D : FilteredDiagram J K) (c : K) :
    FilteredColim J D → FilteredColim J D :=
  Quotient.lift (fun a => Quotient.mk (colimSetoid J D) (ColimSym.smul c a))
    (fun a b h => Quotient.sound (by obtain ⟨ch⟩ := h; exact ⟨ColimChain.smulC c ch⟩))

-- Reference: Lean 4 core (definitional unfolding of the `SMul` instance).
/-- Scalar multiplication on the colimit. -/
instance colimSMul (J : FilteredCat) (D : FilteredDiagram J K) :
    SMul K (FilteredColim J D) :=
  ⟨colimSmulOp J D⟩

-- Reference: Lean 4 core (`Quotient.lift`); the chain constructor `smulC` with
-- `c = -1` (negation is `(-1) • _`).
/-- Negation on the colimit, descended from formal negation (`smul (-1)`). -/
def colimNegOp (J : FilteredCat) (D : FilteredDiagram J K) :
    FilteredColim J D → FilteredColim J D :=
  Quotient.lift (fun a => Quotient.mk (colimSetoid J D) (ColimSym.smul (-1 : K) a))
    (fun a b h =>
      Quotient.sound (by obtain ⟨ch⟩ := h; exact ⟨ColimChain.smulC (-1 : K) ch⟩))

-- Reference: Lean 4 core (definitional unfolding of the `Neg` instance).
/-- Negation on the colimit. -/
instance colimNeg (J : FilteredCat) (D : FilteredDiagram J K) :
    Neg (FilteredColim J D) :=
  ⟨colimNegOp J D⟩

-- Reference: Lean 4 core (subtraction is addition of the negation); primitive
-- definitional instance.
/-- Subtraction on the colimit: `a - b = a + -b`. -/
instance colimSub (J : FilteredCat) (D : FilteredDiagram J K) :
    Sub (FilteredColim J D) :=
  ⟨fun a b => a + -b⟩

-- Reference: definitional peel of `colimSub`.
/-- Subtraction on the colimit is addition of the negation. -/
theorem colimSubEq (J : FilteredCat) (D : FilteredDiagram J K) (a b : FilteredColim J D) :
    a - b = a + -b := rfl

-- Reference: Lean 4 core (definitional unfolding of the instances); primitive
-- definitional lemmas.
/-- The `0` of the colimit is the class of `nil`. -/
theorem colimZeroMk (J : FilteredCat) (D : FilteredDiagram J K) :
    (0 : FilteredColim J D) = Quotient.mk (colimSetoid J D) ColimSym.nil := rfl

-- Reference: mathlib (`Quotient.map₂_mk`); primitive definitional lemma.
/-- Addition of two classes is the class of the formal sum. -/
theorem colimAddMk (J : FilteredCat) (D : FilteredDiagram J K) (a b : ColimSym J D) :
    (Quotient.mk (colimSetoid J D) a + Quotient.mk (colimSetoid J D) b
      : FilteredColim J D) =
      Quotient.mk (colimSetoid J D) (ColimSym.add a b) :=
  Quotient.map₂_mk (fun x y => ColimSym.add x y)
    (colimRelAdd' J D) a b

-- Reference: Lean 4 core (definitional unfolding of the `SMul` instance);
-- primitive definitional lemma.
/-- The `•` on the colimit unfolds to `colimSmulOp`. -/
theorem colimSmulEq (J : FilteredCat) (D : FilteredDiagram J K) (c : K)
    (q : FilteredColim J D) : c • q = colimSmulOp J D c q := rfl
-- Reference: Mac Lane, CWM 2nd ed., Ch. IX §1 (p. 211); the chain constructor
-- `smulC`.
/-- The colimit relation is compatible with formal scalar multiplication. -/
theorem colimRel_smulC (J : FilteredCat) (D : FilteredDiagram J K) (c : K)
    {a b : ColimSym J D} (h : (colimSetoid J D).r a b) :
    (colimSetoid J D).r (ColimSym.smul c a) (ColimSym.smul c b) := by
  obtain ⟨ch⟩ := h
  exact ⟨ColimChain.smulC c ch⟩

-- Reference: mathlib (`Quotient.lift_mk`); primitive definitional lemma.
/-- `colimSmulOp` applied to a class is the class of the formal scalar
multiple. -/
theorem colimSmulOp_mk (J : FilteredCat) (D : FilteredDiagram J K) (c : K)
    (a : ColimSym J D) :
    colimSmulOp J D c (Quotient.mk (colimSetoid J D) a)
      = Quotient.mk (colimSetoid J D) (ColimSym.smul c a) :=
  Quotient.lift_mk (fun a => Quotient.mk (colimSetoid J D) (ColimSym.smul c a))
    (fun _a _b h => Quotient.sound (colimRel_smulC J D c h)) a

-- Reference: Lean 4 core (definitional unfolding of the `Neg` instance);
-- primitive definitional lemma.
/-- The `-` on the colimit unfolds to `colimNegOp`. -/
theorem colimNegEq (J : FilteredCat) (D : FilteredDiagram J K) (q : FilteredColim J D) :
    -q = colimNegOp J D q := rfl

-- Reference: mathlib (`Quotient.lift_mk`); primitive definitional lemma.
/-- `colimNegOp` applied to a class is the class of the formal negation. -/
theorem colimNegOp_mk (J : FilteredCat) (D : FilteredDiagram J K) (a : ColimSym J D) :
    colimNegOp J D (Quotient.mk (colimSetoid J D) a)
      = Quotient.mk (colimSetoid J D) (ColimSym.smul (-1 : K) a) :=
  Quotient.lift_mk (fun a => Quotient.mk (colimSetoid J D) (ColimSym.smul (-1 : K) a))
    (fun _a _b h => Quotient.sound (colimRel_smulC J D (-1 : K) h)) a


-- Reference: mathlib (`Quotient.lift_mk`); primitive definitional lemma.
/-- Scalar multiplication of a class is the class of the formal scalar
multiple. -/
theorem colimSmulMk (J : FilteredCat) (D : FilteredDiagram J K) (c : K) (a : ColimSym J D) :
    (c • Quotient.mk (colimSetoid J D) a : FilteredColim J D) =
      Quotient.mk (colimSetoid J D) (ColimSym.smul c a) :=
  Eq.trans (colimSmulEq J D c (Quotient.mk (colimSetoid J D) a)) (colimSmulOp_mk J D c a)

-- Reference: mathlib (`Quotient.lift_mk`); primitive definitional lemma.
/-- Negation of a class is the class of the formal negation. -/
theorem colimNegMk (J : FilteredCat) (D : FilteredDiagram J K) (a : ColimSym J D) :
    (-Quotient.mk (colimSetoid J D) a : FilteredColim J D) =
      Quotient.mk (colimSetoid J D) (ColimSym.smul (-1 : K) a) :=
  Eq.trans (colimNegEq J D (Quotient.mk (colimSetoid J D) a)) (colimNegOp_mk J D a)

-- Reference: Hörmann, arXiv:2106.03803, Theorem 4.1 (the colimit legs);
-- Mac Lane, CWM 2nd ed., Ch. IX §1 (p. 211).
/-- The leg of the colimit cocone at object `i`: `x ↦ ⟦sym i x⟧`. -/
def colimLeg (J : FilteredCat) (D : FilteredDiagram J K) (i : J.Obj) :
    VecHom K (FreeMod K (D.objDim i)) (FilteredColim J D) where
  toFun := fun x => Quotient.mk (colimSetoid J D) (ColimSym.sym i x)
  map_add' := fun x y =>
    Eq.trans (Quotient.sound (s := colimSetoid J D) ⟨ColimChain.addSym i x y⟩)
      (colimAddMk J D (ColimSym.sym i x) (ColimSym.sym i y)).symm
  map_smul' := fun c x =>
    Eq.trans (Quotient.sound (s := colimSetoid J D) ⟨ColimChain.smulSym i c x⟩)
      (colimSmulMk J D c (ColimSym.sym i x)).symm

-- Reference: definitional peel of `colimLeg`.
/-- The leg applies as `x ↦ ⟦sym i x⟧`. -/
theorem colimLeg_apply (J : FilteredCat) (D : FilteredDiagram J K) (i : J.Obj)
    (x : FreeMod K (D.objDim i)) :
    colimLeg J D i x = Quotient.mk (colimSetoid J D) (ColimSym.sym i x) := rfl
-- Reference: definitional peels of `vecHomComp`, `colimLeg`; the `arrow`
-- chain constructor.
/-- The cocone condition pointwise: `colimLeg j (D.map f x) = colimLeg i x`. -/
theorem colimLeg_comp_apply (J : FilteredCat) (D : FilteredDiagram J K) {i j : J.Obj}
    (f : J.Hom i j) (x : FreeMod K (D.objDim i)) :
    vecHomComp (colimLeg J D j) (D.map f) x = colimLeg J D i x :=
  Eq.trans (vecHomComp_apply (colimLeg J D j) (D.map f) x)
    (Eq.trans (colimLeg_apply J D j (D.map f x))
      (Eq.trans (Quotient.sound (s := colimSetoid J D) ⟨ColimChain.arrow f x⟩).symm
        (colimLeg_apply J D i x).symm))


-- Reference: Hörmann, arXiv:2106.03803, Lemma 3.5 + Theorem 4.1 (the cocone
-- condition over `Q̃A`); the chain constructor `arrow`.
/-- The cocone condition: `colimLeg j ∘ D.map f = colimLeg i`. -/
theorem colimLeg_comp (J : FilteredCat) (D : FilteredDiagram J K) {i j : J.Obj}
    (f : J.Hom i j) :
    vecHomComp (colimLeg J D j) (D.map f) = colimLeg J D i :=
  vecHom_ext fun x => colimLeg_comp_apply J D f x

-- Reference: Mac Lane, CWM 2nd ed., Ch. III §3 (p. 62, colimits as
-- cocones); Hörmann, arXiv:2106.03803, Theorem 4.1.
/-- A cocone under the diagram with vertex `W` (a full vector space), as
explicit data. -/
structure ColimCocone (J : FilteredCat) (D : FilteredDiagram J K) (W : Type u)
    [AddCommGroup W] [Module K W] where
  leg : (i : J.Obj) → VecHom K (FreeMod K (D.objDim i)) W
  compat : ∀ {i j : J.Obj} (f : J.Hom i j), vecHomComp (leg j) (D.map f) = leg i

-- Reference: Hörmann, arXiv:2106.03803, Theorem 4.1; Dummit–Foote, §10.4
-- (lift by recursion on formal sums, as `tensorSymLift` in `FreeTensor`).
/-- The lift of a cocone to the raw formal sums: `nil ↦ 0`, `sym i x ↦ leg i x`,
addition and scalar multiplication map to the operations of `W`. -/
def colimSymLift (J : FilteredCat) (D : FilteredDiagram J K)
    (c : ColimCocone J D W) : ColimSym J D → W
  | ColimSym.nil => 0
  | ColimSym.sym i x => c.leg i x
  | ColimSym.add a b => colimSymLift J D c a + colimSymLift J D c b
  | ColimSym.smul r a => r • colimSymLift J D c a

-- Reference: Lean 4 core (definitional unfolding of `colimSymLift`); primitive
-- definitional lemmas.
/-- The lift of `nil` is `0`. -/
theorem colimSymLiftNil (J : FilteredCat) (D : FilteredDiagram J K)
    (c : ColimCocone J D W) : colimSymLift J D c ColimSym.nil = 0 := rfl

-- Reference: definitional peel of `colimSymLift`.
/-- The lift of a symbol is the cocone leg value. -/
theorem colimSymLiftSym (J : FilteredCat) (D : FilteredDiagram J K)
    (c : ColimCocone J D W) (i : J.Obj) (x : FreeMod K (D.objDim i)) :
    colimSymLift J D c (ColimSym.sym i x) = c.leg i x := rfl

-- Reference: definitional peel of `colimSymLift`.
/-- The lift of a formal sum is the sum of the lifts. -/
theorem colimSymLiftAdd (J : FilteredCat) (D : FilteredDiagram J K)
    (c : ColimCocone J D W) (a b : ColimSym J D) :
    colimSymLift J D c (ColimSym.add a b) = colimSymLift J D c a + colimSymLift J D c b := rfl

-- Reference: definitional peel of `colimSymLift`.
/-- The lift of a formal scalar multiple is the scalar multiple of the lift. -/
theorem colimSymLiftSmul (J : FilteredCat) (D : FilteredDiagram J K)
    (c : ColimCocone J D W) (r : K) (a : ColimSym J D) :
    colimSymLift J D c (ColimSym.smul r a) = r • colimSymLift J D c a := rfl

-- Reference: Hörmann, arXiv:2106.03803, Theorem 4.1 (the lift respects the
-- relations); Dummit–Foote, §10.4; the `tensorSymLiftRel` precedent.
/-- The lift of a cocone to the formal sums respects the colimit relation:
each chain constructor is sent to an equality in `W` (module laws of `W` for
the free-module laws, the cocone condition for the `arrow` relations). -/
theorem colimSymLiftRel (J : FilteredCat) (D : FilteredDiagram J K)
    (c : ColimCocone J D W) (a b : ColimSym J D) (h : colimRel J D a b) :
    colimSymLift J D c a = colimSymLift J D c b := by
  obtain ⟨ch⟩ := h
  induction ch
  case refl x => exact Eq.refl _
  case symm x y ch ih => exact Eq.symm ih
  case trans x y z ch₁ ch₂ ih₁ ih₂ => exact Eq.trans ih₁ ih₂
  case addLeft x y z ch ih =>
      calc colimSymLift J D c (ColimSym.add z x)
          = colimSymLift J D c z + colimSymLift J D c x := colimSymLiftAdd J D c z x
        _ = colimSymLift J D c z + colimSymLift J D c y :=
            congrArg (fun w => colimSymLift J D c z + w) ih
        _ = colimSymLift J D c (ColimSym.add z y) := (colimSymLiftAdd J D c z y).symm
  case addRight x y z ch ih =>
      calc colimSymLift J D c (ColimSym.add x z)
          = colimSymLift J D c x + colimSymLift J D c z := colimSymLiftAdd J D c x z
        _ = colimSymLift J D c y + colimSymLift J D c z :=
            congrArg (fun w => w + colimSymLift J D c z) ih
        _ = colimSymLift J D c (ColimSym.add y z) := (colimSymLiftAdd J D c y z).symm
  case smulC x y r ch ih =>
      calc colimSymLift J D c (ColimSym.smul r x) = r • colimSymLift J D c x :=
            colimSymLiftSmul J D c r x
        _ = r • colimSymLift J D c y := congrArg (fun w => r • w) ih
        _ = colimSymLift J D c (ColimSym.smul r y) := (colimSymLiftSmul J D c r y).symm
  case nilLeft x =>
      calc colimSymLift J D c (ColimSym.add ColimSym.nil x)
          = colimSymLift J D c ColimSym.nil + colimSymLift J D c x := colimSymLiftAdd J D c _ x
        _ = 0 + colimSymLift J D c x :=
            congrArg (fun w => w + colimSymLift J D c x) (colimSymLiftNil J D c)
        _ = colimSymLift J D c x := zero_add _
  case nilRight x =>
      calc colimSymLift J D c (ColimSym.add x ColimSym.nil)
          = colimSymLift J D c x + colimSymLift J D c ColimSym.nil := colimSymLiftAdd J D c x _
        _ = colimSymLift J D c x + 0 :=
            congrArg (fun w => colimSymLift J D c x + w) (colimSymLiftNil J D c)
        _ = colimSymLift J D c x := add_zero _
  case addAssoc x y z =>
      calc colimSymLift J D c (ColimSym.add (ColimSym.add x y) z)
          = colimSymLift J D c (ColimSym.add x y) + colimSymLift J D c z :=
            colimSymLiftAdd J D c _ z
        _ = (colimSymLift J D c x + colimSymLift J D c y) + colimSymLift J D c z :=
            congrArg (fun w => w + colimSymLift J D c z) (colimSymLiftAdd J D c x y)
        _ = colimSymLift J D c x + (colimSymLift J D c y + colimSymLift J D c z) :=
            add_assoc _ _ _
        _ = colimSymLift J D c x + colimSymLift J D c (ColimSym.add y z) :=
            congrArg (fun w => colimSymLift J D c x + w) (colimSymLiftAdd J D c y z).symm
        _ = colimSymLift J D c (ColimSym.add x (ColimSym.add y z)) :=
            (colimSymLiftAdd J D c x _).symm
  case addComm x y =>
      calc colimSymLift J D c (ColimSym.add x y)
          = colimSymLift J D c x + colimSymLift J D c y := colimSymLiftAdd J D c x y
        _ = colimSymLift J D c y + colimSymLift J D c x := add_comm _ _
        _ = colimSymLift J D c (ColimSym.add y x) := (colimSymLiftAdd J D c y x).symm
  case smulNil r =>
      calc colimSymLift J D c (ColimSym.smul r ColimSym.nil)
          = r • colimSymLift J D c ColimSym.nil := colimSymLiftSmul J D c r _
        _ = r • 0 := congrArg (fun w => r • w) (colimSymLiftNil J D c)
        _ = 0 := smul_zero _
        _ = colimSymLift J D c ColimSym.nil := (colimSymLiftNil J D c).symm
  case smulAdd r x y =>
      calc colimSymLift J D c (ColimSym.smul r (ColimSym.add x y))
          = r • colimSymLift J D c (ColimSym.add x y) := colimSymLiftSmul J D c r _
        _ = r • (colimSymLift J D c x + colimSymLift J D c y) :=
            congrArg (fun w => r • w) (colimSymLiftAdd J D c x y)
        _ = r • colimSymLift J D c x + r • colimSymLift J D c y := smul_add _ _ _
        _ = colimSymLift J D c (ColimSym.add (ColimSym.smul r x) (ColimSym.smul r y)) :=
            Eq.trans
              (congrArg (fun w => w + colimSymLift J D c (ColimSym.smul r y))
                (colimSymLiftSmul J D c r x).symm)
              (congrArg (fun w => colimSymLift J D c (ColimSym.smul r x) + w)
                (colimSymLiftSmul J D c r y).symm)
            |>.trans (colimSymLiftAdd J D c _ _).symm
  case addSmul a b x =>
      calc colimSymLift J D c (ColimSym.smul (a + b) x)
          = (a + b) • colimSymLift J D c x := colimSymLiftSmul J D c _ x
        _ = a • colimSymLift J D c x + b • colimSymLift J D c x := add_smul _ _ _
        _ = colimSymLift J D c (ColimSym.add (ColimSym.smul a x) (ColimSym.smul b x)) :=
            Eq.trans
              (congrArg (fun w => w + colimSymLift J D c (ColimSym.smul b x))
                (colimSymLiftSmul J D c a x).symm)
              (congrArg (fun w => colimSymLift J D c (ColimSym.smul a x) + w)
                (colimSymLiftSmul J D c b x).symm)
            |>.trans (colimSymLiftAdd J D c _ _).symm
  case oneSmul x =>
      calc colimSymLift J D c (ColimSym.smul 1 x) = 1 • colimSymLift J D c x :=
            colimSymLiftSmul J D c _ x
        _ = colimSymLift J D c x := one_smul K _
  case zeroSmul x =>
      calc colimSymLift J D c (ColimSym.smul 0 x) = 0 • colimSymLift J D c x :=
            colimSymLiftSmul J D c _ x
        _ = 0 := zero_smul K _
        _ = colimSymLift J D c ColimSym.nil := (colimSymLiftNil J D c).symm
  case smulSmul a b x =>
      calc colimSymLift J D c (ColimSym.smul a (ColimSym.smul b x))
          = a • colimSymLift J D c (ColimSym.smul b x) := colimSymLiftSmul J D c _ _
        _ = a • (b • colimSymLift J D c x) :=
            congrArg (fun w => a • w) (colimSymLiftSmul J D c b x)
        _ = (a * b) • colimSymLift J D c x := (mul_smul a b _).symm
        _ = colimSymLift J D c (ColimSym.smul (a * b) x) := (colimSymLiftSmul J D c _ x).symm
  case zeroSym i =>
      calc colimSymLift J D c (ColimSym.sym i 0) = c.leg i 0 := colimSymLiftSym J D c i 0
        _ = 0 := vecHom_map_zero (c.leg i)
        _ = colimSymLift J D c ColimSym.nil := (colimSymLiftNil J D c).symm
  case addSym i x y =>
      calc colimSymLift J D c (ColimSym.sym i (x + y)) = c.leg i (x + y) :=
            colimSymLiftSym J D c i (x + y)
        _ = c.leg i x + c.leg i y := (c.leg i).map_add' x y
        _ = colimSymLift J D c (ColimSym.add (ColimSym.sym i x) (ColimSym.sym i y)) :=
            Eq.trans
              (congrArg (fun w => w + colimSymLift J D c (ColimSym.sym i y))
                (colimSymLiftSym J D c i x).symm)
              (congrArg (fun w => colimSymLift J D c (ColimSym.sym i x) + w)
                (colimSymLiftSym J D c i y).symm)
            |>.trans (colimSymLiftAdd J D c _ _).symm
  case smulSym i r x =>
      calc colimSymLift J D c (ColimSym.sym i (r • x)) = c.leg i (r • x) :=
            colimSymLiftSym J D c i (r • x)
        _ = r • c.leg i x := (c.leg i).map_smul' r x
        _ = colimSymLift J D c (ColimSym.smul r (ColimSym.sym i x)) :=
            Eq.trans (congrArg (fun w => r • w) (colimSymLiftSym J D c i x).symm)
              (colimSymLiftSmul J D c r _).symm
  case arrow i j f x =>
      exact Eq.trans (colimSymLiftSym J D c i x)
        (Eq.trans
          (Eq.subst (motive := fun t => t = c.leg i x) (vecHomComp_apply (c.leg j) (D.map f) x)
            (congrFun (congrArg VecHom.toFun (c.compat f)) x)).symm
          (colimSymLiftSym J D c j (D.map f x)).symm)

-- Reference: mathlib (`Quotient.lift_mk`, `Quotient.map₂_mk`); Hörmann,
-- arXiv:2106.03803, Theorem 4.1 (the descended operations on the colimit).
/-- Additivity of the colimit lift on classes, via the beta rule and
`colimAddMk`. -/
theorem colimLift_add_mk (J : FilteredCat) (D : FilteredDiagram J K)
    (c : ColimCocone J D W) (a b : ColimSym J D) :
    Quotient.lift (colimSymLift J D c) (fun a b h => colimSymLiftRel J D c a b h)
        (Quotient.mk (colimSetoid J D) a + Quotient.mk (colimSetoid J D) b)
      = Quotient.lift (colimSymLift J D c) (fun a b h => colimSymLiftRel J D c a b h)
          (Quotient.mk (colimSetoid J D) a)
        + Quotient.lift (colimSymLift J D c) (fun a b h => colimSymLiftRel J D c a b h)
          (Quotient.mk (colimSetoid J D) b) :=
  Eq.trans
    (congrArg
      (Quotient.lift (colimSymLift J D c) (fun a b h => colimSymLiftRel J D c a b h))
      (colimAddMk J D a b))
    (Eq.trans
      (Quotient.lift_mk (colimSymLift J D c) (fun a b h => colimSymLiftRel J D c a b h)
        (ColimSym.add a b))
      (Eq.trans (colimSymLiftAdd J D c a b)
        (add_eq_add_of_eq
          (Quotient.lift_mk (colimSymLift J D c) (fun a b h => colimSymLiftRel J D c a b h) a)
          (Quotient.lift_mk (colimSymLift J D c) (fun a b h => colimSymLiftRel J D c a b h) b)).symm))

-- Reference: mathlib (`Quotient.lift_mk`); Hörmann, arXiv:2106.03803,
-- Theorem 4.1.
/-- Homogeneity of the colimit lift on classes, via the beta rule and
`colimSmulMk`. -/
theorem colimLift_smul_mk (J : FilteredCat) (D : FilteredDiagram J K)
    (c : ColimCocone J D W) (r : K) (a : ColimSym J D) :
    Quotient.lift (colimSymLift J D c) (fun a b h => colimSymLiftRel J D c a b h)
        (r • Quotient.mk (colimSetoid J D) a)
      = r • Quotient.lift (colimSymLift J D c) (fun a b h => colimSymLiftRel J D c a b h)
          (Quotient.mk (colimSetoid J D) a) :=
  Eq.trans
    (congrArg
      (Quotient.lift (colimSymLift J D c) (fun a b h => colimSymLiftRel J D c a b h))
      (colimSmulMk J D r a))
    (Eq.trans
      (Quotient.lift_mk (colimSymLift J D c) (fun a b h => colimSymLiftRel J D c a b h)
        (ColimSym.smul r a))
      (Eq.trans (colimSymLiftSmul J D c r a)
        (congrArg (fun t => r • t)
          (Quotient.lift_mk (colimSymLift J D c) (fun a b h => colimSymLiftRel J D c a b h)
            a)).symm))

-- Reference: Mac Lane, CWM 2nd ed., Ch. III §3 (p. 62, the colimit's universal
-- property); Hörmann, arXiv:2106.03803, Theorem 4.1; Lean 4 core
-- (`Quotient.lift`).
/-- The lift of a cocone to the filtered colimit (the universal map out of the
colimit). -/
def colimLift (J : FilteredCat) (D : FilteredDiagram J K) (c : ColimCocone J D W) :
    VecHom K (FilteredColim J D) W where
  toFun := Quotient.lift (colimSymLift J D c) (fun a b h => colimSymLiftRel J D c a b h)
  map_add' := fun q₁ q₂ =>
    Quotient.inductionOn₂ q₁ q₂ (fun a b => colimLift_add_mk J D c a b)
  map_smul' := fun r q => Quotient.inductionOn (motive := fun q =>
      Quotient.lift (colimSymLift J D c) (fun a b h => colimSymLiftRel J D c a b h) (r • q)
        = r • Quotient.lift (colimSymLift J D c) (fun a b h => colimSymLiftRel J D c a b h) q)
      q (fun a => colimLift_smul_mk J D c r a)

-- Reference: definitional peel of `colimLift`.
/-- The colimit lift applies as the `Quotient.lift` of the symbol lift. -/
theorem colimLift_apply (J : FilteredCat) (D : FilteredDiagram J K)
    (c : ColimCocone J D W) (q : FilteredColim J D) :
    colimLift J D c q =
      Quotient.lift (colimSymLift J D c) (fun a b h => colimSymLiftRel J D c a b h) q := rfl

-- Reference: Mac Lane, CWM 2nd ed., Ch. III §3 (p. 62, beta rule: the lift
-- sends the class of `a` to the symbol lift of `a`).
/-- Beta rule of the colimit's universal property. -/
theorem colimLift_mk (J : FilteredCat) (D : FilteredDiagram J K)
    (c : ColimCocone J D W) (a : ColimSym J D) :
    colimLift J D c (Quotient.mk (colimSetoid J D) a) = colimSymLift J D c a :=
  Eq.trans (colimLift_apply J D c (Quotient.mk (colimSetoid J D) a))
    (Quotient.lift_mk (colimSymLift J D c) (fun a b h => colimSymLiftRel J D c a b h) a)

-- Reference: Hörmann, arXiv:2106.03803, Theorem 4.1 (the lift of a cocone
-- composed with a leg is the cocone leg).
/-- Beta rule on legs: `colimLift c (colimLeg i x) = c.leg i x`. -/
theorem colimLift_leg (J : FilteredCat) (D : FilteredDiagram J K)
    (c : ColimCocone J D W) (i : J.Obj) (x : FreeMod K (D.objDim i)) :
    colimLift J D c (colimLeg J D i x) = c.leg i x :=
  Eq.trans (congrArg (colimLift J D c) (colimLeg_apply J D i x))
    (Eq.trans (colimLift_mk J D c (ColimSym.sym i x)) (colimSymLiftSym J D c i x))

-- Reference: Mac Lane, CWM 2nd ed., Ch. IX §1 (p. 211); `colimSmulMk`, the
-- chain constructor `zeroSmul`.
/-- `0 • ⟦nil⟧ = ⟦nil⟧` in the filtered colimit. -/
theorem colim_zero_smul_nil (J : FilteredCat) (D : FilteredDiagram J K) :
    (0 : K) • Quotient.mk (colimSetoid J D) ColimSym.nil
      = Quotient.mk (colimSetoid J D) ColimSym.nil :=
  Eq.trans (colimSmulMk J D (0 : K) ColimSym.nil)
    (Quotient.sound (s := colimSetoid J D) ⟨ColimChain.zeroSmul ColimSym.nil⟩)

-- Reference: Mac Lane, CWM 2nd ed., Ch. IX §1 (p. 211); `colim_zero_smul_nil`,
-- `k.map_smul'`, `zero_smul`, `colimSymLiftNil`.
/-- The nil case of the colimit-lift uniqueness induction. -/
theorem colimLift_unique_nil (J : FilteredCat) (D : FilteredDiagram J K)
    (c : ColimCocone J D W) (k : VecHom K (FilteredColim J D) W) :
    k (Quotient.mk (colimSetoid J D) ColimSym.nil) = colimSymLift J D c ColimSym.nil :=
  Eq.subst (motive := fun t => k t = colimSymLift J D c ColimSym.nil) (colim_zero_smul_nil J D)
    (Eq.trans (k.map_smul' (0 : K) (Quotient.mk (colimSetoid J D) ColimSym.nil))
      (Eq.trans (zero_smul K (k (Quotient.mk (colimSetoid J D) ColimSym.nil)))
        (colimSymLiftNil J D c).symm))

-- Reference: Mac Lane, CWM 2nd ed., Ch. IX §1 (p. 211); `colimLeg_apply`.
/-- The symbol case of the colimit-lift uniqueness induction. -/
theorem colimLift_unique_sym (J : FilteredCat) (D : FilteredDiagram J K)
    (c : ColimCocone J D W) (k : VecHom K (FilteredColim J D) W)
    (hk : ∀ i x, k (colimLeg J D i x) = c.leg i x) (i : J.Obj)
    (x : FreeMod K (D.objDim i)) :
    k (Quotient.mk (colimSetoid J D) (ColimSym.sym i x))
      = colimSymLift J D c (ColimSym.sym i x) :=
  Eq.subst (motive := fun t => k t = colimSymLift J D c (ColimSym.sym i x)) (colimLeg_apply J D i x) (hk i x)

-- Reference: Mac Lane, CWM 2nd ed., Ch. IX §1 (p. 211); `colimAddMk`,
-- `colimSymLiftAdd`.
/-- The sum case of the colimit-lift uniqueness induction. -/
theorem colimLift_unique_add (J : FilteredCat) (D : FilteredDiagram J K)
    (c : ColimCocone J D W) (k : VecHom K (FilteredColim J D) W) (a b : ColimSym J D)
    (iha : k (Quotient.mk (colimSetoid J D) a) = colimSymLift J D c a)
    (ihb : k (Quotient.mk (colimSetoid J D) b) = colimSymLift J D c b) :
    k (Quotient.mk (colimSetoid J D) (ColimSym.add a b))
      = colimSymLift J D c (ColimSym.add a b) :=
  Eq.subst (motive := fun t => k t = colimSymLift J D c (ColimSym.add a b)) (colimAddMk J D a b)
    (Eq.trans
      (k.map_add' (Quotient.mk (colimSetoid J D) a) (Quotient.mk (colimSetoid J D) b))
      (Eq.trans (add_eq_add_of_eq iha ihb) (colimSymLiftAdd J D c a b).symm))

-- Reference: Mac Lane, CWM 2nd ed., Ch. IX §1 (p. 211); `colimSmulMk`,
-- `colimSymLiftSmul`.
/-- The scalar case of the colimit-lift uniqueness induction. -/
theorem colimLift_unique_smul (J : FilteredCat) (D : FilteredDiagram J K)
    (c : ColimCocone J D W) (k : VecHom K (FilteredColim J D) W) (r : K) (a : ColimSym J D)
    (ih : k (Quotient.mk (colimSetoid J D) a) = colimSymLift J D c a) :
    k (Quotient.mk (colimSetoid J D) (ColimSym.smul r a))
      = colimSymLift J D c (ColimSym.smul r a) :=
  Eq.subst (motive := fun t => k t = colimSymLift J D c (ColimSym.smul r a)) (colimSmulMk J D r a)
    (Eq.trans (k.map_smul' r (Quotient.mk (colimSetoid J D) a))
      (Eq.trans (congrArg (fun t => r • t) ih) (colimSymLiftSmul J D c r a).symm))

-- Reference: Mac Lane, CWM 2nd ed., Ch. IX §1 (p. 211); structural recursion on
-- the formal sum with the four case lemmas above.
/-- The colimit-lift uniqueness induction, by recursion on the formal sum. -/
theorem colimLift_unique_ind (J : FilteredCat) (D : FilteredDiagram J K)
    (c : ColimCocone J D W) (k : VecHom K (FilteredColim J D) W)
    (hk : ∀ i x, k (colimLeg J D i x) = c.leg i x) :
    (a : ColimSym J D) → k (Quotient.mk (colimSetoid J D) a) = colimSymLift J D c a
  | ColimSym.nil => colimLift_unique_nil J D c k
  | ColimSym.sym i x => colimLift_unique_sym J D c k hk i x
  | ColimSym.add a b =>
      colimLift_unique_add J D c k a b (colimLift_unique_ind J D c k hk a)
        (colimLift_unique_ind J D c k hk b)
  | ColimSym.smul r a => colimLift_unique_smul J D c k r a (colimLift_unique_ind J D c k hk a)

-- Reference: Mac Lane, CWM 2nd ed., Ch. III §3 (p. 62, uniqueness of the
-- colimit map).
/-- Uniqueness: any explicit linear map out of the colimit agreeing with the
cocone on all legs is the lift. -/
theorem colimLift_unique (J : FilteredCat) (D : FilteredDiagram J K)
    (c : ColimCocone J D W) (k : VecHom K (FilteredColim J D) W)
    (hk : ∀ i x, k (colimLeg J D i x) = c.leg i x) : k = colimLift J D c :=
  vecHom_ext fun q =>
    Quotient.inductionOn q (fun a =>
      Eq.trans (colimLift_unique_ind J D c k hk a) (colimLift_mk J D c a).symm)

-- Reference: Mac Lane, CWM 2nd ed., Ch. IX §1 (p. 211); structural recursion on
-- the formal sum, using the chain constructors `nilLeft`, `smulNil`, `addLeft`,
-- `addRight`, `smulSym`, `addSym`, `zeroSym`, `addAssoc`, `addComm`, `smulAdd`,
-- `addSmul`, `smulSmul`, `zeroSmul`.
/-- Witness chain (data): `a + (-1)•a ∼ nil` for every formal sum `a`. -/
def colimChainAddNeg (J : FilteredCat) (D : FilteredDiagram J K) :
    (a : ColimSym J D) →
    ColimChain J D (ColimSym.add a (ColimSym.smul (-1 : K) a)) ColimSym.nil
  | ColimSym.nil =>
      (ColimChain.nilLeft (ColimSym.smul (-1 : K) ColimSym.nil)).trans
        (ColimChain.smulNil (-1 : K))
  | ColimSym.sym i x =>
      (ColimChain.addLeft (z := ColimSym.sym i x)
        (ColimChain.smulSym i (-1 : K) x).symm).trans
        ((ColimChain.addSym i x ((-1 : K) • x)).symm.trans
          (Eq.rec (motive := fun t _ => ColimChain J D (ColimSym.sym i t) ColimSym.nil)
            (ColimChain.zeroSym i) (add_neg_one_smul x).symm))
  | ColimSym.add a b =>
      ColimChain.trans
        (ColimChain.addLeft (z := ColimSym.add a b) (ColimChain.smulAdd (-1 : K) a b))
        (ColimChain.trans
          (ColimChain.addAssoc a b (ColimSym.add (ColimSym.smul (-1 : K) a)
            (ColimSym.smul (-1 : K) b)))
          (ColimChain.trans
            (ColimChain.addLeft (z := a)
              (ColimChain.trans
                (ColimChain.addAssoc b (ColimSym.smul (-1 : K) a)
                  (ColimSym.smul (-1 : K) b)).symm
                (ColimChain.trans
                  (ColimChain.addRight (z := ColimSym.smul (-1 : K) b)
                    (ColimChain.addComm b (ColimSym.smul (-1 : K) a)))
                  (ColimChain.addAssoc (ColimSym.smul (-1 : K) a) b
                    (ColimSym.smul (-1 : K) b)))))
            (ColimChain.trans
              (ColimChain.addAssoc a (ColimSym.smul (-1 : K) a)
                (ColimSym.add b (ColimSym.smul (-1 : K) b))).symm
              (ColimChain.trans
                (ColimChain.addRight (z := ColimSym.add b (ColimSym.smul (-1 : K) b))
                  (colimChainAddNeg J D a))
                (ColimChain.trans
                  (ColimChain.nilLeft (ColimSym.add b (ColimSym.smul (-1 : K) b)))
                  (colimChainAddNeg J D b))))))
  | ColimSym.smul c a =>
      (ColimChain.addLeft (z := ColimSym.smul c a)
        (ColimChain.smulSmul (-1 : K) c a)).trans
        ((ColimChain.addSmul c ((-1 : K) * c) a).symm.trans
          (Eq.rec (motive := fun t _ => ColimChain J D (ColimSym.smul t a) ColimSym.nil)
            (ColimChain.zeroSmul a) (add_neg_one_mul c).symm))

-- Reference: Mac Lane, CWM 2nd ed., Ch. IX §1 (p. 211); `colimNegMk`,
-- `colimAddMk`, `colimZeroMk`, `colimChainAddNeg`.
/-- `⟦a⟧ + -⟦a⟧ = 0` in the filtered colimit. -/
theorem colimAddNeg_mk (J : FilteredCat) (D : FilteredDiagram J K) (a : ColimSym J D) :
    Quotient.mk (colimSetoid J D) a + -Quotient.mk (colimSetoid J D) a = 0 :=
  Eq.trans (congrArg (fun t => Quotient.mk (colimSetoid J D) a + t) (colimNegMk J D a))
    (Eq.trans (colimAddMk J D a (ColimSym.smul (-1 : K) a))
      (Eq.trans (Quotient.sound (s := colimSetoid J D) ⟨colimChainAddNeg J D a⟩)
        (colimZeroMk J D).symm))

-- Reference: Mac Lane, CWM 2nd ed., Ch. IX §1 (p. 211); `colimChainAddNeg`.
/-- In the filtered colimit, `q + -q = 0`. -/
theorem colimAddNeg (J : FilteredCat) (D : FilteredDiagram J K) (q : FilteredColim J D) :
    q + -q = 0 :=
  Quotient.inductionOn q (fun a => colimAddNeg_mk J D a)

-- Reference: Axler, Ch. 1; the chain constructors `addSym`, `smulSym`.
/-- Witness chain: `sym i (x + (-1)•y) ∼ add (sym i x) (smul (-1) (sym i y))`. -/
def colimLeg_add_smul_chain (J : FilteredCat) (D : FilteredDiagram J K) (i : J.Obj)
    (x y : FreeMod K (D.objDim i)) :
    ColimChain J D (ColimSym.sym i (x + (-1 : K) • y))
      (ColimSym.add (ColimSym.sym i x) (ColimSym.smul (-1 : K) (ColimSym.sym i y))) :=
  (ColimChain.addSym i x ((-1 : K) • y)).trans
    (ColimChain.addLeft (z := ColimSym.sym i x) (ColimChain.smulSym i (-1 : K) y))

-- Reference: Mac Lane, CWM 2nd ed., Ch. IX §1 (p. 211); `colimLeg_add_smul_chain`,
-- `colimAddMk`, `colimNegMk`.
/-- The leg commutes with subtraction, first form (classes of symbols). -/
theorem colimLeg_map_sub_mk (J : FilteredCat) (D : FilteredDiagram J K) (i : J.Obj)
    (x y : FreeMod K (D.objDim i)) :
    colimLeg J D i (x - y)
      = Quotient.mk (colimSetoid J D) (ColimSym.sym i x)
        + -Quotient.mk (colimSetoid J D) (ColimSym.sym i y) :=
  Eq.trans (congrArg (colimLeg J D i) (sub_eq_add_neg_one_smul x y))
    (Eq.trans (colimLeg_apply J D i (x + (-1 : K) • y))
      (Eq.trans (Quotient.sound (s := colimSetoid J D) ⟨colimLeg_add_smul_chain J D i x y⟩)
        (Eq.trans
          (colimAddMk J D (ColimSym.sym i x) (ColimSym.smul (-1 : K) (ColimSym.sym i y))).symm
          (congrArg (fun t => Quotient.mk (colimSetoid J D) (ColimSym.sym i x) + t)
            (colimNegMk J D (ColimSym.sym i y)).symm))))

-- Reference: Axler, Ch. 1 (the leg is linear); the chain constructors
-- `addSym`/`smulSym`/`sub_eq_add_neg`/`neg_one_smul`.
/-- The leg commutes with subtraction (the colimit carrier has a descended
negation, and `x - y = x + (-1) • y`). -/
theorem colimLeg_map_sub (J : FilteredCat) (D : FilteredDiagram J K) (i : J.Obj)
    (x y : FreeMod K (D.objDim i)) :
    colimLeg J D i (x - y) = colimLeg J D i x - colimLeg J D i y :=
  Eq.trans (colimLeg_map_sub_mk J D i x y)
    (Eq.trans
      (add_eq_add_of_eq (colimLeg_apply J D i x).symm
        (congrArg (fun t => -t) (colimLeg_apply J D i y).symm))
      (colimSubEq J D (colimLeg J D i x) (colimLeg J D i y)).symm)

/-! ## The dies-in-colimit witness (finite chains) -/


-- Reference: Mac Lane, CWM 2nd ed., Ch. IX §1 (p. 211); the functor law
-- `map_comp` of `FilteredDiagram`, applied pointwise.
/-- Pointwise form of the diagram's functor law. -/
theorem map_comp_apply (J : FilteredCat) (D : FilteredDiagram J K) {i j k : J.Obj}
    (f : J.Hom i j) (g : J.Hom j k) (x : FreeMod K (D.objDim i)) :
    D.map (J.comp g f) x = D.map g (D.map f x) :=
  Eq.subst (motive := fun F => F x = D.map g (D.map f x)) (D.map_comp f g).symm
    (vecHomComp_apply (D.map g) (D.map f) x)

-- Reference: Mac Lane, CWM 2nd ed., Ch. IX §1 (p. 211); the identity law
-- `map_id` of `FilteredDiagram`, applied pointwise.
/-- The diagram map of an identity arrow is the identity, pointwise. -/
theorem map_id_apply (J : FilteredCat) (D : FilteredDiagram J K) (i : J.Obj)
    (x : FreeMod K (D.objDim i)) : D.map (J.id i) x = x :=
  Eq.trans (congrArg (fun F => F x) (D.map_id i)) (vecHomId_apply _ x)

-- Reference: Mac Lane, CWM 2nd ed., Ch. IX §1 (p. 211: elements of a filtered
-- colimit are symbols `⟨i, x⟩`); Hörmann, arXiv:2106.03803, Theorem 4.1.
/-- A symbol of the filtered colimit: a diagram object and a vector (data). -/
abbrev SymPair (J : FilteredCat) (D : FilteredDiagram J K) : Type u :=
  Σ i : J.Obj, FreeMod K (D.objDim i)

-- Reference: Mac Lane, CWM 2nd ed., Ch. IX §1 (p. 211, finite sums at a common
-- upper bound); STYLE §2.3 (the upper bound is data, never instance-chosen).
/-- The formal sum of two symbols at their data upper bound. -/
def pairAdd (J : FilteredCat) (D : FilteredDiagram J K)
    (p q : SymPair J D) : SymPair J D :=
  ⟨(J.upperBound p.1 q.1).1,
    D.map (J.upperBound p.1 q.1).2.1 p.2 + D.map (J.upperBound p.1 q.1).2.2 q.2⟩

-- Reference: primitive definitional peels of `pairAdd`.
/-- The object of `pairAdd p q` is the data upper bound. -/
theorem pairAdd_fst (J : FilteredCat) (D : FilteredDiagram J K)
    (p q : SymPair J D) : (pairAdd J D p q).1 = (J.upperBound p.1 q.1).1 := rfl

-- Reference: primitive definitional peel of `pairAdd`.
/-- The vector of `pairAdd p q` is the sum of the two transported vectors. -/
theorem pairAdd_snd (J : FilteredCat) (D : FilteredDiagram J K)
    (p q : SymPair J D) :
    (pairAdd J D p q).2
      = D.map (J.upperBound p.1 q.1).2.1 p.2 + D.map (J.upperBound p.1 q.1).2.2 q.2 :=
  rfl

-- Reference: Mac Lane, CWM 2nd ed., Ch. IX §1 (p. 211); structural recursion
-- on the formal sum (data), combining symbols at data upper bounds.
/-- Evaluate a formal sum to a single symbol: `nil ↦ ⟨nonemptyObj, 0⟩`,
`sym i x ↦ ⟨i, x⟩`, and sums/scalings combine in the target module. -/
def colimEval (J : FilteredCat) (D : FilteredDiagram J K) :
    ColimSym J D → SymPair J D
  | ColimSym.nil => ⟨J.nonemptyObj, 0⟩
  | ColimSym.sym i x => ⟨i, x⟩
  | ColimSym.add a b => pairAdd J D (colimEval J D a) (colimEval J D b)
  | ColimSym.smul r a => ⟨(colimEval J D a).1, r • (colimEval J D a).2⟩

-- Reference: Lean 4 core (definitional unfolding of `colimEval`); primitive
-- definitional lemmas.
/-- The evaluation of `nil` is the zero symbol at the nonempty object. -/
theorem colimEvalNil (J : FilteredCat) (D : FilteredDiagram J K) :
    colimEval J D ColimSym.nil = ⟨J.nonemptyObj, 0⟩ := rfl

-- Reference: definitional peel of `colimEval`.
/-- The evaluation of a symbol is the symbol itself. -/
theorem colimEvalSym (J : FilteredCat) (D : FilteredDiagram J K) (i : J.Obj)
    (x : FreeMod K (D.objDim i)) : colimEval J D (ColimSym.sym i x) = ⟨i, x⟩ := rfl

-- Reference: definitional peel of `colimEval`.
/-- The evaluation of a formal sum is the `pairAdd` of the evaluations. -/
theorem colimEvalAdd (J : FilteredCat) (D : FilteredDiagram J K) (a b : ColimSym J D) :
    colimEval J D (ColimSym.add a b) = pairAdd J D (colimEval J D a) (colimEval J D b) :=
  rfl

-- Reference: definitional peel of `colimEval`.
/-- The evaluation of a formal scalar multiple scales the evaluated vector. -/
theorem colimEvalSmul (J : FilteredCat) (D : FilteredDiagram J K) (r : K)
    (a : ColimSym J D) :
    colimEval J D (ColimSym.smul r a) = ⟨(colimEval J D a).1, r • (colimEval J D a).2⟩ :=
  rfl

-- Reference: Mac Lane, CWM 2nd ed., Ch. IX §1 (p. 211: two symbols agree in a
-- filtered colimit iff their images agree at a common upper bound);
-- Hörmann, arXiv:2106.03803, Lemma 3.5 (Q̃A is filtered).
/-- Two symbols agree in the filtered colimit iff there is a common upper
bound with equal images (all witnesses data). -/
def colimSymRel (J : FilteredCat) (D : FilteredDiagram J K)
    (p q : SymPair J D) : Prop :=
  ∃ k : J.Obj, ∃ f : J.Hom p.1 k, ∃ g : J.Hom q.1 k, D.map f p.2 = D.map g q.2

-- Reference: Mac Lane, CWM 2nd ed., Ch. IX §1 (p. 211); the identity law via
-- `map_id`.
/-- The symbol relation is reflexive. -/
theorem colimSymRel_refl (J : FilteredCat) (D : FilteredDiagram J K)
    (p : SymPair J D) : colimSymRel J D p p :=
  ⟨p.1, J.id p.1, J.id p.1,
    Eq.trans (map_id_apply J D p.1 p.2) (map_id_apply J D p.1 p.2).symm⟩

-- Reference: Mac Lane, CWM 2nd ed., Ch. IX §1 (p. 211); symmetry by swapping
-- the two arrows.
/-- The symbol relation is symmetric. -/
theorem colimSymRel_symm (J : FilteredCat) (D : FilteredDiagram J K)
    {p q : SymPair J D} (h : colimSymRel J D p q) : colimSymRel J D q p := by
  obtain ⟨k, f, g, e⟩ := h
  exact ⟨k, g, f, e.symm⟩

-- Reference: the associativity law of `FilteredCat` (Mac Lane, CWM 2nd ed.,
-- Ch. I §2).
/-- Reassociation of a threefold composite of diagram arrows. -/
theorem comp_assoc' (J : FilteredCat) {i j k l : J.Obj} (f : J.Hom i j) (g : J.Hom j k)
    (h : J.Hom k l) : J.comp (J.comp h g) f = J.comp h (J.comp g f) :=
  (J.assoc f g h).symm

-- Reference: Mac Lane, CWM 2nd ed., Ch. IX §1 (p. 211); `map_comp_apply`.
/-- Threefold composites of diagram maps compute pointwise. -/
theorem map_comp_comp_apply (J : FilteredCat) (D : FilteredDiagram J K)
    {i j k l : J.Obj} (f : J.Hom i j) (g : J.Hom j k) (h : J.Hom k l)
    (x : FreeMod K (D.objDim i)) :
    D.map (J.comp h (J.comp g f)) x = D.map h (D.map g (D.map f x)) :=
  Eq.trans (map_comp_apply J D (J.comp g f) h x)
    (congrArg (D.map h) (map_comp_apply J D f g x))

-- Reference: Mac Lane, CWM 2nd ed., Ch. IX §1 (p. 211: filteredness —
-- `coequalize`); `map_comp_apply` four times.
/-- The coequalized pair, transported through the diagram maps. -/
theorem colimSymRel_trans_hce (J : FilteredCat) (D : FilteredDiagram J K)
    {q : SymPair J D} {k₁ k₂ m k : J.Obj}
    (g₁ : J.Hom q.1 k₁) (f₂ : J.Hom q.1 k₂) (a : J.Hom k₁ m) (b : J.Hom k₂ m)
    (c : J.Hom m k) (hc : J.comp c (J.comp a g₁) = J.comp c (J.comp b f₂))
    (x : FreeMod K (D.objDim q.1)) :
    D.map c (D.map a (D.map g₁ x)) = D.map c (D.map b (D.map f₂ x)) :=
  Eq.trans
    (Eq.trans (map_comp_apply J D (J.comp a g₁) c x)
      (congrArg (D.map c) (map_comp_apply J D g₁ a x))).symm
    (Eq.trans (congrArg (fun F => D.map F x) hc)
      (Eq.trans (map_comp_apply J D (J.comp b f₂) c x)
        (congrArg (D.map c) (map_comp_apply J D f₂ b x))))

-- Reference: Mac Lane, CWM 2nd ed., Ch. IX §1 (p. 211: transitivity);
-- `map_comp_comp_apply`, `colimSymRel_trans_hce`.
/-- The transitivity computation for the symbol relation. -/
theorem colimSymRel_trans_step (J : FilteredCat) (D : FilteredDiagram J K)
    {p q r : SymPair J D} {k₁ k₂ m k : J.Obj}
    (f₁ : J.Hom p.1 k₁) (g₁ : J.Hom q.1 k₁) (e₁ : D.map f₁ p.2 = D.map g₁ q.2)
    (f₂ : J.Hom q.1 k₂) (g₂ : J.Hom r.1 k₂) (e₂ : D.map f₂ q.2 = D.map g₂ r.2)
    (a : J.Hom k₁ m) (b : J.Hom k₂ m) (c : J.Hom m k)
    (hc : J.comp c (J.comp a g₁) = J.comp c (J.comp b f₂)) :
    D.map (J.comp c (J.comp a f₁)) p.2 = D.map (J.comp c (J.comp b g₂)) r.2 :=
  Eq.trans (map_comp_comp_apply J D f₁ a c p.2)
    (Eq.trans (congrArg (fun t => D.map c (D.map a t)) e₁)
      (Eq.trans (colimSymRel_trans_hce J D g₁ f₂ a b c hc q.2)
        (Eq.trans (congrArg (fun t => D.map c (D.map b t)) e₂)
          (map_comp_comp_apply J D g₂ b c r.2).symm)))

-- Reference: Mac Lane, CWM 2nd ed., Ch. IX §1 (p. 211: transitivity uses that
-- the category is filtered — `upperBound` and `coequalize`); Hörmann,
-- arXiv:2106.03803, Lemma 3.5.
/-- The symbol relation is transitive (filteredness: common upper bounds and
coequalizing arrows, as data). -/
theorem colimSymRel_trans (J : FilteredCat) (D : FilteredDiagram J K)
    {p q r : SymPair J D} (h₁ : colimSymRel J D p q) (h₂ : colimSymRel J D q r) :
    colimSymRel J D p r := by
  obtain ⟨k₁, f₁, g₁, e₁⟩ := h₁
  obtain ⟨k₂, f₂, g₂, e₂⟩ := h₂
  obtain ⟨m, ⟨a, b⟩⟩ := J.upperBound k₁ k₂
  obtain ⟨k, ⟨c, hc⟩⟩ := J.coequalize (J.comp a g₁) (J.comp b f₂)
  exact ⟨k, J.comp c (J.comp a f₁), J.comp c (J.comp b g₂),
    colimSymRel_trans_step J D f₁ g₁ e₁ f₂ g₂ e₂ a b c hc.down⟩



-- Reference: Mac Lane, CWM 2nd ed., Ch. IX §1 (p. 211: sums commute after
-- transporting to a common upper bound); `pairAdd_snd`, `map_comp_apply`,
-- `comp_assoc'`, and the two coequalizing arrows.
/-- The left-hand chain of the `pairAdd` commutativity computation. -/
theorem colimSymRel_add_comm_lhs (J : FilteredCat) (D : FilteredDiagram J K)
    (p q : SymPair J D) {M K K' : J.Obj}
    (u : J.Hom (J.upperBound p.1 q.1).1 M) (v : J.Hom (J.upperBound q.1 p.1).1 M)
    (r : J.Hom M K) (r' : J.Hom K K')
    (hr : J.comp r (J.comp u (J.upperBound p.1 q.1).2.1)
        = J.comp r (J.comp v (J.upperBound q.1 p.1).2.2))
    (hr' : J.comp r' (J.comp r (J.comp u (J.upperBound p.1 q.1).2.2))
        = J.comp r' (J.comp r (J.comp v (J.upperBound q.1 p.1).2.1))) :
    D.map (J.comp r' (J.comp r u)) (pairAdd J D p q).2
      = D.map (J.comp r' (J.comp r (J.comp v (J.upperBound q.1 p.1).2.1))) q.2
        + D.map (J.comp r' (J.comp r (J.comp v (J.upperBound q.1 p.1).2.2))) p.2 :=
  calc D.map (J.comp r' (J.comp r u)) (pairAdd J D p q).2
      = D.map (J.comp r' (J.comp r u))
          (D.map (J.upperBound p.1 q.1).2.1 p.2 + D.map (J.upperBound p.1 q.1).2.2 q.2) :=
        congrArg (D.map (J.comp r' (J.comp r u))) (pairAdd_snd J D p q)
    _ = D.map (J.comp r' (J.comp r u)) (D.map (J.upperBound p.1 q.1).2.1 p.2)
        + D.map (J.comp r' (J.comp r u)) (D.map (J.upperBound p.1 q.1).2.2 q.2) :=
        (D.map (J.comp r' (J.comp r u))).map_add' (D.map (J.upperBound p.1 q.1).2.1 p.2)
          (D.map (J.upperBound p.1 q.1).2.2 q.2)
    _ = D.map (J.comp (J.comp r' (J.comp r u)) (J.upperBound p.1 q.1).2.1) p.2
        + D.map (J.comp (J.comp r' (J.comp r u)) (J.upperBound p.1 q.1).2.2) q.2 :=
        add_eq_add_of_eq
          (map_comp_apply J D (J.upperBound p.1 q.1).2.1 (J.comp r' (J.comp r u)) p.2).symm
          (map_comp_apply J D (J.upperBound p.1 q.1).2.2 (J.comp r' (J.comp r u)) q.2).symm
    _ = D.map (J.comp r' (J.comp r (J.comp u (J.upperBound p.1 q.1).2.1))) p.2
        + D.map (J.comp r' (J.comp r (J.comp u (J.upperBound p.1 q.1).2.2))) q.2 :=
        add_eq_add_of_eq
          (congrArg (fun F => D.map F p.2)
            (Eq.trans (comp_assoc' J (J.upperBound p.1 q.1).2.1 (J.comp r u) r')
              (congrArg (J.comp r') (comp_assoc' J (J.upperBound p.1 q.1).2.1 u r))))
          (congrArg (fun F => D.map F q.2)
            (Eq.trans (comp_assoc' J (J.upperBound p.1 q.1).2.2 (J.comp r u) r')
              (congrArg (J.comp r') (comp_assoc' J (J.upperBound p.1 q.1).2.2 u r))))
    _ = D.map (J.comp r' (J.comp r (J.comp v (J.upperBound q.1 p.1).2.2))) p.2
        + D.map (J.comp r' (J.comp r (J.comp v (J.upperBound q.1 p.1).2.1))) q.2 :=
        add_eq_add_of_eq (congrArg (fun F => D.map (J.comp r' F) p.2) hr)
          (congrArg (fun F => D.map F q.2) hr')
    _ = D.map (J.comp r' (J.comp r (J.comp v (J.upperBound q.1 p.1).2.1))) q.2
        + D.map (J.comp r' (J.comp r (J.comp v (J.upperBound q.1 p.1).2.2))) p.2 :=
        add_comm _ _
-- Reference: Mac Lane, CWM 2nd ed., Ch. IX §1 (p. 211); the right-hand chain of
-- the `pairAdd` commutativity computation.
/-- The right-hand chain of the `pairAdd` commutativity computation. -/
theorem colimSymRel_add_comm_rhs (J : FilteredCat) (D : FilteredDiagram J K)
    (p q : SymPair J D) {M K K' : J.Obj}
    (u : J.Hom (J.upperBound p.1 q.1).1 M) (v : J.Hom (J.upperBound q.1 p.1).1 M)
    (r : J.Hom M K) (r' : J.Hom K K')
    (_hr : J.comp r (J.comp u (J.upperBound p.1 q.1).2.1)
        = J.comp r (J.comp v (J.upperBound q.1 p.1).2.2))
    (_hr' : J.comp r' (J.comp r (J.comp u (J.upperBound p.1 q.1).2.2))
        = J.comp r' (J.comp r (J.comp v (J.upperBound q.1 p.1).2.1))) :
    D.map (J.comp r' (J.comp r v)) (pairAdd J D q p).2
      = D.map (J.comp r' (J.comp r (J.comp v (J.upperBound q.1 p.1).2.1))) q.2
        + D.map (J.comp r' (J.comp r (J.comp v (J.upperBound q.1 p.1).2.2))) p.2 :=
  calc D.map (J.comp r' (J.comp r v)) (pairAdd J D q p).2
      = D.map (J.comp r' (J.comp r v))
          (D.map (J.upperBound q.1 p.1).2.1 q.2 + D.map (J.upperBound q.1 p.1).2.2 p.2) :=
        congrArg (D.map (J.comp r' (J.comp r v))) (pairAdd_snd J D q p)
    _ = D.map (J.comp r' (J.comp r v)) (D.map (J.upperBound q.1 p.1).2.1 q.2)
        + D.map (J.comp r' (J.comp r v)) (D.map (J.upperBound q.1 p.1).2.2 p.2) :=
        (D.map (J.comp r' (J.comp r v))).map_add' (D.map (J.upperBound q.1 p.1).2.1 q.2)
          (D.map (J.upperBound q.1 p.1).2.2 p.2)
    _ = D.map (J.comp (J.comp r' (J.comp r v)) (J.upperBound q.1 p.1).2.1) q.2
        + D.map (J.comp (J.comp r' (J.comp r v)) (J.upperBound q.1 p.1).2.2) p.2 :=
        add_eq_add_of_eq
          (map_comp_apply J D (J.upperBound q.1 p.1).2.1 (J.comp r' (J.comp r v)) q.2).symm
          (map_comp_apply J D (J.upperBound q.1 p.1).2.2 (J.comp r' (J.comp r v)) p.2).symm
    _ = D.map (J.comp r' (J.comp r (J.comp v (J.upperBound q.1 p.1).2.1))) q.2
        + D.map (J.comp r' (J.comp r (J.comp v (J.upperBound q.1 p.1).2.2))) p.2 :=
        add_eq_add_of_eq
          (congrArg (fun F => D.map F q.2)
            (Eq.trans (comp_assoc' J (J.upperBound q.1 p.1).2.1 (J.comp r v) r')
              (congrArg (J.comp r') (comp_assoc' J (J.upperBound q.1 p.1).2.1 v r))))
          (congrArg (fun F => D.map F p.2)
            (Eq.trans (comp_assoc' J (J.upperBound q.1 p.1).2.2 (J.comp r v) r')
              (congrArg (J.comp r') (comp_assoc' J (J.upperBound q.1 p.1).2.2 v r))))

-- Reference: Mac Lane, CWM 2nd ed., Ch. IX §1 (p. 211: sums commute after
-- transporting to a common upper bound); the two arrows out of `p.1` are
-- equalized by the data `coequalize`.
/-- `pairAdd` is commutative up to the symbol relation. -/
theorem colimSymRel_add_comm (J : FilteredCat) (D : FilteredDiagram J K)
    (p q : SymPair J D) :
    colimSymRel J D (pairAdd J D p q) (pairAdd J D q p) := by
  obtain ⟨M, ⟨u, v⟩⟩ :=
    J.upperBound (J.upperBound p.1 q.1).1 (J.upperBound q.1 p.1).1
  obtain ⟨K, ⟨r, hr⟩⟩ := J.coequalize
    (J.comp u (J.upperBound p.1 q.1).2.1) (J.comp v (J.upperBound q.1 p.1).2.2)
  obtain ⟨K', ⟨r', hr'⟩⟩ := J.coequalize
    (J.comp r (J.comp u (J.upperBound p.1 q.1).2.2))
    (J.comp r (J.comp v (J.upperBound q.1 p.1).2.1))
  exact ⟨K', J.comp r' (J.comp r u), J.comp r' (J.comp r v),
    Eq.trans (colimSymRel_add_comm_lhs J D p q u v r r' hr.down hr'.down)
      (colimSymRel_add_comm_rhs J D p q u v r r' hr.down hr'.down).symm⟩

-- Reference: the associativity law of `FilteredCat` (Mac Lane, CWM 2nd ed.,
-- Ch. I §2); fivefold reassociation.
/-- Fivefold reassociation of a composite of diagram arrows. -/
theorem comp_assoc5 (J : FilteredCat) {i j k l m n o : J.Obj}
    (f : J.Hom i j) (g : J.Hom j k) (h : J.Hom k l) (s : J.Hom l m)
    (t : J.Hom m n) (u : J.Hom n o) :
    J.comp (J.comp u (J.comp t (J.comp s (J.comp h g)))) f
      = J.comp u (J.comp t (J.comp s (J.comp h (J.comp g f)))) :=
  Eq.trans (comp_assoc' J f (J.comp t (J.comp s (J.comp h g))) u)
    (congrArg (J.comp u)
      (Eq.trans (comp_assoc' J f (J.comp s (J.comp h g)) t)
        (congrArg (J.comp t)
          (Eq.trans (comp_assoc' J f (J.comp h g) s)
            (congrArg (J.comp s) (comp_assoc' J f g h))))))

-- Reference: Mac Lane, CWM 2nd ed., Ch. IX §1 (p. 211); `map_comp_comp_apply`
-- and the relation `e`.
/-- The `c f` / `c g` transport in the left-respect computation. -/
theorem colimSymRel_add_left_s1 (J : FilteredCat) (D : FilteredDiagram J K)
    {p q : SymPair J D} {k N N₁ : J.Obj}
    (f : J.Hom p.1 k) (g : J.Hom q.1 k) (e : D.map f p.2 = D.map g q.2)
    (c : J.Hom k N) (r₁ : J.Hom N N₁) :
    D.map (J.comp r₁ (J.comp c f)) p.2 = D.map (J.comp r₁ (J.comp c g)) q.2 :=
  Eq.trans (map_comp_comp_apply J D f c r₁ p.2)
    (Eq.trans (congrArg (fun t => D.map r₁ (D.map c t)) e)
      (map_comp_comp_apply J D g c r₁ q.2).symm)

-- Reference: Mac Lane, CWM 2nd ed., Ch. IX §1 (p. 211: filteredness —
-- `coequalize`); `colimSymRel_add_left_s1` and the two coequalizing arrows.
/-- The first coequalized transport in the left-respect computation. -/
theorem colimSymRel_add_left_t1 (J : FilteredCat) (D : FilteredDiagram J K)
    {p q : SymPair J D} (r : SymPair J D) {k M N N₁ N₂ : J.Obj}
    (f : J.Hom p.1 k) (g : J.Hom q.1 k) (e : D.map f p.2 = D.map g q.2)
    (u : J.Hom (J.upperBound p.1 r.1).1 M) (v : J.Hom (J.upperBound q.1 r.1).1 M)
    (c : J.Hom k N) (w : J.Hom M N) (r₁ : J.Hom N N₁) (r₂ : J.Hom N₁ N₂)
    (hr₁ : J.comp r₁ (J.comp w (J.comp u (J.upperBound p.1 r.1).2.1))
        = J.comp r₁ (J.comp c f))
    (hr₂ : J.comp r₂ (J.comp r₁ (J.comp c g))
        = J.comp r₂ (J.comp r₁ (J.comp w (J.comp v (J.upperBound q.1 r.1).2.1)))) :
    D.map (J.comp r₂ (J.comp r₁ (J.comp w (J.comp u (J.upperBound p.1 r.1).2.1)))) p.2
      = D.map (J.comp r₂ (J.comp r₁ (J.comp w (J.comp v (J.upperBound q.1 r.1).2.1)))) q.2 :=
  Eq.trans
    (map_comp_apply J D (J.comp r₁ (J.comp w (J.comp u (J.upperBound p.1 r.1).2.1))) r₂ p.2)
    (Eq.trans
      (congrArg (D.map r₂)
        (Eq.trans (congrArg (fun F => D.map F p.2) hr₁)
          (colimSymRel_add_left_s1 J D f g e c r₁)))
      (Eq.trans (map_comp_apply J D (J.comp r₁ (J.comp c g)) r₂ q.2).symm
        (congrArg (fun F => D.map F q.2) hr₂)))

-- Reference: Mac Lane, CWM 2nd ed., Ch. IX §1 (p. 211); `map_comp_apply` and
-- `colimSymRel_add_left_t1`.
/-- The `p.2`-component equality in the left-respect computation. -/
theorem colimSymRel_add_left_eA (J : FilteredCat) (D : FilteredDiagram J K)
    {p q : SymPair J D} (r : SymPair J D) {k M N N₁ N₂ K : J.Obj}
    (f : J.Hom p.1 k) (g : J.Hom q.1 k) (e : D.map f p.2 = D.map g q.2)
    (u : J.Hom (J.upperBound p.1 r.1).1 M) (v : J.Hom (J.upperBound q.1 r.1).1 M)
    (c : J.Hom k N) (w : J.Hom M N) (r₁ : J.Hom N N₁) (r₂ : J.Hom N₁ N₂) (r₃ : J.Hom N₂ K)
    (hr₁ : J.comp r₁ (J.comp w (J.comp u (J.upperBound p.1 r.1).2.1))
        = J.comp r₁ (J.comp c f))
    (hr₂ : J.comp r₂ (J.comp r₁ (J.comp c g))
        = J.comp r₂ (J.comp r₁ (J.comp w (J.comp v (J.upperBound q.1 r.1).2.1)))) :
    D.map (J.comp r₃ (J.comp r₂ (J.comp r₁ (J.comp w (J.comp u (J.upperBound p.1 r.1).2.1)))))
        p.2
      = D.map (J.comp r₃ (J.comp r₂ (J.comp r₁ (J.comp w (J.comp v (J.upperBound q.1 r.1).2.1)))))
        q.2 :=
  Eq.trans
    (map_comp_apply J D (J.comp r₂ (J.comp r₁ (J.comp w (J.comp u (J.upperBound p.1 r.1).2.1))))
      r₃ p.2)
    (Eq.trans
      (congrArg (D.map r₃) (colimSymRel_add_left_t1 J D r f g e u v c w r₁ r₂ hr₁ hr₂))
      (map_comp_apply J D (J.comp r₂ (J.comp r₁ (J.comp w (J.comp v (J.upperBound q.1 r.1).2.1))))
        r₃ q.2).symm)

-- Reference: Mac Lane, CWM 2nd ed., Ch. IX §1 (p. 211: filteredness —
-- `coequalize`); the third coequalizing arrow.
/-- The `r.2`-component equality in the left-respect computation. -/
theorem colimSymRel_add_left_eB (J : FilteredCat) (D : FilteredDiagram J K)
    {p q : SymPair J D} (r : SymPair J D) {M N N₁ N₂ K : J.Obj}
    (u : J.Hom (J.upperBound p.1 r.1).1 M) (v : J.Hom (J.upperBound q.1 r.1).1 M)
    (w : J.Hom M N) (r₁ : J.Hom N N₁) (r₂ : J.Hom N₁ N₂) (r₃ : J.Hom N₂ K)
    (hr₃ : J.comp r₃ (J.comp r₂ (J.comp r₁ (J.comp w (J.comp u (J.upperBound p.1 r.1).2.2))))
        = J.comp r₃ (J.comp r₂ (J.comp r₁ (J.comp w (J.comp v (J.upperBound q.1 r.1).2.2))))) :
    D.map (J.comp r₃ (J.comp r₂ (J.comp r₁ (J.comp w (J.comp u (J.upperBound p.1 r.1).2.2)))))
        r.2
      = D.map (J.comp r₃ (J.comp r₂ (J.comp r₁ (J.comp w (J.comp v (J.upperBound q.1 r.1).2.2)))))
        r.2 :=
  congrArg (fun F => D.map F r.2) hr₃

-- Reference: Mac Lane, CWM 2nd ed., Ch. IX §1 (p. 211: sums respect the symbol
-- relation); `pairAdd_snd`, `map_comp_apply`, `comp_assoc5`,
-- `colimSymRel_add_left_eA`, `colimSymRel_add_left_eB`.
/-- The left-hand chain of the `pairAdd` left-respect computation. -/
theorem colimSymRel_add_left_lhs (J : FilteredCat) (D : FilteredDiagram J K)
    {p q : SymPair J D} (r : SymPair J D) {k M N N₁ N₂ K : J.Obj}
    (f : J.Hom p.1 k) (g : J.Hom q.1 k) (e : D.map f p.2 = D.map g q.2)
    (u : J.Hom (J.upperBound p.1 r.1).1 M) (v : J.Hom (J.upperBound q.1 r.1).1 M)
    (c : J.Hom k N) (w : J.Hom M N) (r₁ : J.Hom N N₁) (r₂ : J.Hom N₁ N₂) (r₃ : J.Hom N₂ K)
    (hr₁ : J.comp r₁ (J.comp w (J.comp u (J.upperBound p.1 r.1).2.1))
        = J.comp r₁ (J.comp c f))
    (hr₂ : J.comp r₂ (J.comp r₁ (J.comp c g))
        = J.comp r₂ (J.comp r₁ (J.comp w (J.comp v (J.upperBound q.1 r.1).2.1))))
    (hr₃ : J.comp r₃ (J.comp r₂ (J.comp r₁ (J.comp w (J.comp u (J.upperBound p.1 r.1).2.2))))
        = J.comp r₃ (J.comp r₂ (J.comp r₁ (J.comp w (J.comp v (J.upperBound q.1 r.1).2.2))))) :
    D.map (J.comp r₃ (J.comp r₂ (J.comp r₁ (J.comp w u)))) (pairAdd J D p r).2
      = D.map (J.comp r₃ (J.comp r₂ (J.comp r₁ (J.comp w (J.comp v (J.upperBound q.1 r.1).2.1)))))
          q.2
        + D.map (J.comp r₃ (J.comp r₂ (J.comp r₁ (J.comp w (J.comp v (J.upperBound q.1 r.1).2.2)))))
          r.2 :=
  calc D.map (J.comp r₃ (J.comp r₂ (J.comp r₁ (J.comp w u)))) (pairAdd J D p r).2
      = D.map (J.comp r₃ (J.comp r₂ (J.comp r₁ (J.comp w u))))
          (D.map (J.upperBound p.1 r.1).2.1 p.2 + D.map (J.upperBound p.1 r.1).2.2 r.2) :=
        congrArg (D.map (J.comp r₃ (J.comp r₂ (J.comp r₁ (J.comp w u))))) (pairAdd_snd J D p r)
    _ = D.map (J.comp r₃ (J.comp r₂ (J.comp r₁ (J.comp w u))))
          (D.map (J.upperBound p.1 r.1).2.1 p.2)
        + D.map (J.comp r₃ (J.comp r₂ (J.comp r₁ (J.comp w u))))
          (D.map (J.upperBound p.1 r.1).2.2 r.2) :=
        (D.map (J.comp r₃ (J.comp r₂ (J.comp r₁ (J.comp w u))))).map_add'
          (D.map (J.upperBound p.1 r.1).2.1 p.2) (D.map (J.upperBound p.1 r.1).2.2 r.2)
    _ = D.map (J.comp (J.comp r₃ (J.comp r₂ (J.comp r₁ (J.comp w u))))
          (J.upperBound p.1 r.1).2.1) p.2
        + D.map (J.comp (J.comp r₃ (J.comp r₂ (J.comp r₁ (J.comp w u))))
          (J.upperBound p.1 r.1).2.2) r.2 :=
        add_eq_add_of_eq
          (map_comp_apply J D (J.upperBound p.1 r.1).2.1
            (J.comp r₃ (J.comp r₂ (J.comp r₁ (J.comp w u)))) p.2).symm
          (map_comp_apply J D (J.upperBound p.1 r.1).2.2
            (J.comp r₃ (J.comp r₂ (J.comp r₁ (J.comp w u)))) r.2).symm
    _ = D.map (J.comp r₃ (J.comp r₂ (J.comp r₁ (J.comp w (J.comp u (J.upperBound p.1 r.1).2.1)))))
          p.2
        + D.map (J.comp r₃ (J.comp r₂ (J.comp r₁ (J.comp w (J.comp u (J.upperBound p.1 r.1).2.2)))))
          r.2 :=
        add_eq_add_of_eq
          (congrArg (fun F => D.map F p.2)
            (comp_assoc5 J (J.upperBound p.1 r.1).2.1 u w r₁ r₂ r₃))
          (congrArg (fun F => D.map F r.2)
            (comp_assoc5 J (J.upperBound p.1 r.1).2.2 u w r₁ r₂ r₃))
    _ = D.map (J.comp r₃ (J.comp r₂ (J.comp r₁ (J.comp w (J.comp v (J.upperBound q.1 r.1).2.1)))))
          q.2
        + D.map (J.comp r₃ (J.comp r₂ (J.comp r₁ (J.comp w (J.comp v (J.upperBound q.1 r.1).2.2)))))
          r.2 :=
        add_eq_add_of_eq
          (colimSymRel_add_left_eA J D r f g e u v c w r₁ r₂ r₃ hr₁ hr₂)
          (colimSymRel_add_left_eB J D r u v w r₁ r₂ r₃ hr₃)

-- Reference: Mac Lane, CWM 2nd ed., Ch. IX §1 (p. 211); the right-hand chain of
-- the `pairAdd` left-respect computation.
/-- The right-hand chain of the `pairAdd` left-respect computation. -/
theorem colimSymRel_add_left_rhs (J : FilteredCat) (D : FilteredDiagram J K)
    {p q : SymPair J D} (r : SymPair J D) {M N N₁ N₂ K : J.Obj}
    (_u : J.Hom (J.upperBound p.1 r.1).1 M) (v : J.Hom (J.upperBound q.1 r.1).1 M)
    (w : J.Hom M N) (r₁ : J.Hom N N₁) (r₂ : J.Hom N₁ N₂) (r₃ : J.Hom N₂ K) :
    D.map (J.comp r₃ (J.comp r₂ (J.comp r₁ (J.comp w v)))) (pairAdd J D q r).2
      = D.map (J.comp r₃ (J.comp r₂ (J.comp r₁ (J.comp w (J.comp v (J.upperBound q.1 r.1).2.1)))))
          q.2
        + D.map (J.comp r₃ (J.comp r₂ (J.comp r₁ (J.comp w (J.comp v (J.upperBound q.1 r.1).2.2)))))
          r.2 :=
  calc D.map (J.comp r₃ (J.comp r₂ (J.comp r₁ (J.comp w v)))) (pairAdd J D q r).2
      = D.map (J.comp r₃ (J.comp r₂ (J.comp r₁ (J.comp w v))))
          (D.map (J.upperBound q.1 r.1).2.1 q.2 + D.map (J.upperBound q.1 r.1).2.2 r.2) :=
        congrArg (D.map (J.comp r₃ (J.comp r₂ (J.comp r₁ (J.comp w v))))) (pairAdd_snd J D q r)
    _ = D.map (J.comp r₃ (J.comp r₂ (J.comp r₁ (J.comp w v))))
          (D.map (J.upperBound q.1 r.1).2.1 q.2)
        + D.map (J.comp r₃ (J.comp r₂ (J.comp r₁ (J.comp w v))))
          (D.map (J.upperBound q.1 r.1).2.2 r.2) :=
        (D.map (J.comp r₃ (J.comp r₂ (J.comp r₁ (J.comp w v))))).map_add'
          (D.map (J.upperBound q.1 r.1).2.1 q.2) (D.map (J.upperBound q.1 r.1).2.2 r.2)
    _ = D.map (J.comp (J.comp r₃ (J.comp r₂ (J.comp r₁ (J.comp w v))))
          (J.upperBound q.1 r.1).2.1) q.2
        + D.map (J.comp (J.comp r₃ (J.comp r₂ (J.comp r₁ (J.comp w v))))
          (J.upperBound q.1 r.1).2.2) r.2 :=
        add_eq_add_of_eq
          (map_comp_apply J D (J.upperBound q.1 r.1).2.1
            (J.comp r₃ (J.comp r₂ (J.comp r₁ (J.comp w v)))) q.2).symm
          (map_comp_apply J D (J.upperBound q.1 r.1).2.2
            (J.comp r₃ (J.comp r₂ (J.comp r₁ (J.comp w v)))) r.2).symm
    _ = D.map (J.comp r₃ (J.comp r₂ (J.comp r₁ (J.comp w (J.comp v (J.upperBound q.1 r.1).2.1)))))
          q.2
        + D.map (J.comp r₃ (J.comp r₂ (J.comp r₁ (J.comp w (J.comp v (J.upperBound q.1 r.1).2.2)))))
          r.2 :=
        add_eq_add_of_eq
          (congrArg (fun F => D.map F q.2)
            (comp_assoc5 J (J.upperBound q.1 r.1).2.1 v w r₁ r₂ r₃))
          (congrArg (fun F => D.map F r.2)
            (comp_assoc5 J (J.upperBound q.1 r.1).2.2 v w r₁ r₂ r₃))
-- Reference: Mac Lane, CWM 2nd ed., Ch. IX §1 (p. 211: sums respect the symbol
-- relation); filteredness (`upperBound` + `coequalize`) aligns all arrows.
/-- `pairAdd` respects the symbol relation in its left argument. -/
theorem colimSymRel_add_left (J : FilteredCat) (D : FilteredDiagram J K)
    {p q : SymPair J D} (r : SymPair J D) (h : colimSymRel J D p q) :
    colimSymRel J D (pairAdd J D p r) (pairAdd J D q r) := by
  obtain ⟨k, f, g, e⟩ := h
  obtain ⟨M, ⟨u, v⟩⟩ :=
    J.upperBound (J.upperBound p.1 r.1).1 (J.upperBound q.1 r.1).1
  obtain ⟨N, ⟨c, w⟩⟩ := J.upperBound k M
  obtain ⟨N₁, ⟨r₁, hr₁⟩⟩ := J.coequalize
    (J.comp w (J.comp u (J.upperBound p.1 r.1).2.1)) (J.comp c f)
  obtain ⟨N₂, ⟨r₂, hr₂⟩⟩ := J.coequalize (J.comp r₁ (J.comp c g))
    (J.comp r₁ (J.comp w (J.comp v (J.upperBound q.1 r.1).2.1)))
  obtain ⟨K, ⟨r₃, hr₃⟩⟩ := J.coequalize
    (J.comp r₂ (J.comp r₁ (J.comp w (J.comp u (J.upperBound p.1 r.1).2.2))))
    (J.comp r₂ (J.comp r₁ (J.comp w (J.comp v (J.upperBound q.1 r.1).2.2))))
  exact ⟨K, J.comp r₃ (J.comp r₂ (J.comp r₁ (J.comp w u))),
    J.comp r₃ (J.comp r₂ (J.comp r₁ (J.comp w v))),
    Eq.trans
      (colimSymRel_add_left_lhs J D r f g e u v c w r₁ r₂ r₃ hr₁.down hr₂.down hr₃.down)
      (colimSymRel_add_left_rhs J D r u v w r₁ r₂ r₃).symm⟩

-- Reference: Mac Lane, CWM 2nd ed., Ch. IX §1 (p. 211); derived from
-- commutativity and left-addition.
/-- `pairAdd` respects the symbol relation in its right argument. -/
theorem colimSymRel_add_right (J : FilteredCat) (D : FilteredDiagram J K)
    {r s : SymPair J D} (p : SymPair J D) (h : colimSymRel J D r s) :
    colimSymRel J D (pairAdd J D p r) (pairAdd J D p s) :=
  colimSymRel_trans J D (colimSymRel_add_comm J D p r)
    (colimSymRel_trans J D (colimSymRel_add_left J D p h)
      (colimSymRel_add_comm J D s p))

-- Reference: Mac Lane, CWM 2nd ed., Ch. IX §1 (p. 211); congruence of sums.
/-- `pairAdd` respects the symbol relation in both arguments. -/
theorem colimSymRel_add (J : FilteredCat) (D : FilteredDiagram J K)
    {p₁ q₁ p₂ q₂ : SymPair J D} (h₁ : colimSymRel J D p₁ q₁)
    (h₂ : colimSymRel J D p₂ q₂) :
    colimSymRel J D (pairAdd J D p₁ p₂) (pairAdd J D q₁ q₂) :=
  colimSymRel_trans J D (colimSymRel_add_left J D p₂ h₁) (colimSymRel_add_right J D q₁ h₂)

-- Reference: Mac Lane, CWM 2nd ed., Ch. IX §1 (p. 211); scalar multiples via
-- `map_smul'`.
/-- Scaling respects the symbol relation. -/
theorem colimSymRel_smul (J : FilteredCat) (D : FilteredDiagram J K) (r : K)
    {p q : SymPair J D} (h : colimSymRel J D p q) :
    colimSymRel J D ⟨p.1, r • p.2⟩ ⟨q.1, r • q.2⟩ := by
  obtain ⟨k, f, g, e⟩ := h
  exact ⟨k, f, g, Eq.trans ((D.map f).map_smul' r p.2)
    (Eq.trans (congrArg (fun t => r • t) e) ((D.map g).map_smul' r q.2).symm)⟩

-- Reference: Mac Lane, CWM 2nd ed., Ch. IX §1 (p. 211); `map_id_apply`,
-- `vecHom_map_zero`, `zero_add`.
/-- The empty sum is neutral on the left: the computation. -/
theorem colimSymRel_nil_left_step (J : FilteredCat) (D : FilteredDiagram J K)
    (p : SymPair J D) :
    D.map (J.id (J.upperBound J.nonemptyObj p.1).1)
        (D.map (J.upperBound J.nonemptyObj p.1).2.1 0
          + D.map (J.upperBound J.nonemptyObj p.1).2.2 p.2)
      = D.map (J.upperBound J.nonemptyObj p.1).2.2 p.2 :=
  Eq.trans (map_id_apply J D (J.upperBound J.nonemptyObj p.1).1 _)
    (Eq.trans
      (congrArg (fun t => t + D.map (J.upperBound J.nonemptyObj p.1).2.2 p.2)
        (vecHom_map_zero (D.map (J.upperBound J.nonemptyObj p.1).2.1)))
      (zero_add _))

-- Reference: Mac Lane, CWM 2nd ed., Ch. IX §1 (p. 211); the zero symbol maps
-- to `0` (`vecHom_map_zero`).
/-- The empty sum is neutral on the left up to the symbol relation. -/
theorem colimSymRel_nil_left (J : FilteredCat) (D : FilteredDiagram J K)
    (p : SymPair J D) :
    colimSymRel J D (pairAdd J D ⟨J.nonemptyObj, 0⟩ p) p :=
  ⟨(J.upperBound J.nonemptyObj p.1).1, J.id _,
    (J.upperBound J.nonemptyObj p.1).2.2,
    Eq.trans (congrArg (D.map (J.id (J.upperBound J.nonemptyObj p.1).1))
        (pairAdd_snd J D ⟨J.nonemptyObj, 0⟩ p))
      (colimSymRel_nil_left_step J D p)⟩

-- Reference: Mac Lane, CWM 2nd ed., Ch. IX §1 (p. 211); `map_id_apply`,
-- `vecHom_map_zero`, `add_zero`.
/-- The empty sum is neutral on the right: the computation. -/
theorem colimSymRel_nil_right_step (J : FilteredCat) (D : FilteredDiagram J K)
    (p : SymPair J D) :
    D.map (J.id (J.upperBound p.1 J.nonemptyObj).1)
        (D.map (J.upperBound p.1 J.nonemptyObj).2.1 p.2
          + D.map (J.upperBound p.1 J.nonemptyObj).2.2 0)
      = D.map (J.upperBound p.1 J.nonemptyObj).2.1 p.2 :=
  Eq.trans (map_id_apply J D (J.upperBound p.1 J.nonemptyObj).1 _)
    (Eq.trans
      (congrArg (fun t => D.map (J.upperBound p.1 J.nonemptyObj).2.1 p.2 + t)
        (vecHom_map_zero (D.map (J.upperBound p.1 J.nonemptyObj).2.2)))
      (add_zero _))

-- Reference: Mac Lane, CWM 2nd ed., Ch. IX §1 (p. 211); `vecHom_map_zero`.
/-- The empty sum is neutral on the right up to the symbol relation. -/
theorem colimSymRel_nil_right (J : FilteredCat) (D : FilteredDiagram J K)
    (p : SymPair J D) :
    colimSymRel J D (pairAdd J D p ⟨J.nonemptyObj, 0⟩) p :=
  ⟨(J.upperBound p.1 J.nonemptyObj).1, J.id _,
    (J.upperBound p.1 J.nonemptyObj).2.1,
    Eq.trans (congrArg (D.map (J.id (J.upperBound p.1 J.nonemptyObj).1))
        (pairAdd_snd J D p ⟨J.nonemptyObj, 0⟩))
      (colimSymRel_nil_right_step J D p)⟩

