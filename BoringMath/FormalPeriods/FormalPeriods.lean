/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Quot
import BoringMath.FormalPeriods.FreeMod
import BoringMath.FormalPeriods.FreeTensor
import BoringMath.FormalPeriods.AxiomLint

/-!
# The formal-periods setting: the quadruple (𝒜, H_B, H_dR, ∫), P(𝒜) and eval_∫

This module formalizes Hörmann's formal-periods setting (ticket P.4,
definitions only; the theorems are P.5+).  Over an abstract abelian category
`𝒜` (carried by typeclass hypotheses, never axioms — and stated kernel-free,
because the `kernel`/`limit` family is `Classical.choice`-tainted at the pin,
see `docs/AUDITS/2026-10-30-axiom-lint-pin-run.md`), a **quadruple**
`(𝒜, H_B, H_dR, ∫)` consists of two fiber functors into P.1's basis-carrying
vector spaces (`FreeMod B (dim M)`, resp. `FreeMod K (dim M)` — the base fields
`B` (Hörmann's ℚ) and `K` (Hörmann's K ⊆ ℂ) are carried as variables, because
the concrete `Rat.instField` instance is choice-tainted at the pin) and a
natural isomorphism `∫ : H_B ⊗_B L ≅ H_dR ⊗_K L` after base change to a field
extension `L` of `K` (Hörmann takes `L = ℂ`; stated abstractly per the ticket).

The **space of formal periods** `P(𝒜)` is the quotient of the finitely-supported
direct sum `⨁_M H_B(M) ⊗_B H_dR(M)∨` by the morphism relations
`(σ ⊗ α∨(ω))_M = (α(σ) ⊗ ω)_N`.  Following the P.1 pattern, the direct sum is
the quotient of the free `B`-module on abstract symbols `sym M σ ω` by the
bilinearity relations, and the morphism relations are added as generators of a
witness-carrying inductive relation `PeriodChain` (a relation holds iff an
explicit chain exists — built here, not deferred to P.2.3).  `P(𝒜) = Quot` by
that relation; `P(M)` is the image of the `M`-summand in `P(𝒜)`.

Finite sums over `Fin n` are computed as `finSum n f = ((List.finRange n).map
f).sum`: the `Finset` induction/congruence lemmas are `Classical.choice`-tainted
at the pin (P.0.4 census), so the list lemmas used here are proved by hand by
`List` induction, which lints CLEAN.

The evaluation `eval_∫ : P(𝒜) → L`, `(σ ⊗ ω)_M ↦ ω(∫_M σ)`, is defined by
`Quot.lift`, and its well-definedness on the quotient — the main theorem of this
ticket — is proved by induction on the witness chain, the morphism-relation
case being exactly the naturality of `∫`.

## References
* F. Hörmann, *A note on formal periods*, arXiv:2106.03803 (verified against
  the arXiv HTML, v2): Def 2.1 (fiber functor: ℚ-linear, exact, faithful functor
  into f.d.-K-Vect), 2.2 (the quadruple and the natural isomorphism
  `∫ : H_B ⊗_ℚ ℂ ≅ H_dR ⊗_K ℂ`), Def 2.3 (P(𝒜) as the quotient of
  `⨁_M H_B(M) ⊗_ℚ H_dR(M)∨` by the relations (2), and `P(M)` as the image of
  `H_B(M) ⊗_ℚ H_dR(M)∨` in `P(𝒜)`), Def 2.5 (the period conjecture;
  `eval_∫ : P(𝒜) → ℂ`, `(σ⊗ω)_M ↦ ω(∫_M(σ))`).
* S. Mac Lane, *Categories for the Working Mathematician*, 2nd ed., Ch. VIII
  §1 (abelian categories — stated here kernel-free: kernels/cokernels via
  their universal properties, monics are kernels, epics are cokernels) and
  Ch. VIII (exact functors; in abelian categories exactness is equivalent to
  preserving monomorphisms and epimorphisms).
* D. Dummit & R. Foote, *Abstract Algebra*, 3rd ed., §10.4 (tensor products by
  generators and relations; the universal property used for `Quot.lift`).
* S. Axler, *Linear Algebra Done Right*, 4th ed., Ch. 2 (the standard basis of
  `F^n`: every vector is a linear combination of the standard basis).
* Lean 4 core, `Init/Prelude.lean` (`Quot`, `Quot.mk`, `Quot.sound`,
  `Quot.lift`, `Quot.inductionOn`); mathlib, `Mathlib/Data/Quot.lean`
  (`Quot.map₂`, `Quot.map₂_mk`, `Quot.lift_mk`).
-/

universe u

namespace BoringMath.FormalPeriods

open CategoryTheory

/-! ## Finite sums over `Fin n` (list-based, choice-free) -/

-- Reference: the P.0.4 pin-run census (docs/AUDITS/2026-10-30-axiom-lint-pin-run.md):
-- the `Finset` congruence/induction lemmas (`Finset.sum_congr`, `sum_insert`,
-- `Finset.induction`, `sum_ite_eq`) route through `Classical.choice` at the pin,
-- so finite sums over `Fin n` are computed as list sums over `List.finRange`
-- (which lints CLEAN); Axler, LADR 4th ed., Ch. 2 (the standard basis is indexed
-- by `Fin n`).
/-- The finite sum `∑ i : Fin n, f i`, computed as the list sum over
`List.finRange n` (avoiding the choice-tainted `Finset` lemmas at the pin). -/
def finSum {M : Type u} [AddCommMonoid M] (n : ℕ) (f : Fin n → M) : M :=
  ((List.finRange n).map f).sum

-- Reference: Lean 4 core, `Init/Data/List/Basic.lean` (`List.map_cons`, `List.sum_cons`);
-- peel of the `rw [List.map_cons, List.sum_cons]` step in the list-sum inductions.
/-- Peel: the sum over a cons cell is the head summand plus the tail sum. -/
theorem listMapConsSum {N : Type u} [AddCommMonoid N] {α : Type} (f : α → N) (a : α)
    (l : List α) : ((a :: l).map f).sum = f a + (l.map f).sum :=
  Eq.trans (congrArg (fun w : List N => w.sum) (List.map_cons (f := f) (a := a) (l := l)))
    (List.sum_cons (a := f a) (l := l.map f))

-- Reference: Lean 4 core, `Init/Data/List/Basic.lean` (`List.map_nil`, `List.sum_nil`);
-- peel of the `rw [List.map_nil, List.sum_nil]` step in the list-sum inductions.
/-- Peel: the sum over the empty list is `0`. -/
theorem listMapNilSum {N : Type u} [AddCommMonoid N] {α : Type} (f : α → N) :
    (([] : List α).map f).sum = (0 : N) :=
  Eq.trans (congrArg (fun w : List N => w.sum) (List.map_nil (f := f))) (List.sum_nil (α := N))

-- Reference: Lean 4 core, `Init/Data/List/Basic.lean` (`List.map_nil`, `List.sum_nil`,
-- `add_zero`); peel of the nil case of `listSum_map_add`.
/-- Peel: the empty sum distributes over addition. -/
theorem listMapNilSumAdd {N : Type u} [AddCommMonoid N] {α : Type} (f g : α → N) :
    (([] : List α).map f).sum + (([] : List α).map g).sum = (0 : N) :=
  Eq.trans (congrArg (fun w => w + (([] : List α).map g).sum) (listMapNilSum f))
    (Eq.trans (congrArg (fun w => (0 : N) + w) (listMapNilSum g)) (add_zero 0))

-- Reference: Lean 4 core, `Init/Data/List/Basic.lean` (`List.map_nil`, `List.sum_nil`,
-- `mul_zero`); peel of the nil case of `listSum_map_mul_left`.
/-- Peel: a constant factor times the empty sum is `0`. -/
theorem listMapNilMul {R : Type u} [Semiring R] {α : Type} (c : R) (f : α → R) :
    c * (([] : List α).map f).sum = (0 : R) :=
  Eq.trans (congrArg (fun w => c * w) (listMapNilSum f)) (mul_zero c)

-- Reference: Lean 4 core, `Init/Data/List/Basic.lean` (`List.rec`); the list-sum
-- lemmas below are proved by hand by `List` induction (clean at the pin).
/-- List sums respect pointwise equality of the summands. -/
theorem listSum_congr {N : Type u} [AddCommMonoid N] {n : ℕ} (l : List (Fin n))
    (f g : Fin n → N) (h : ∀ a, f a = g a) : (l.map f).sum = (l.map g).sum := by
  induction l with
  | nil => exact Eq.trans (listMapNilSum f) (listMapNilSum g).symm
  | cons a l ih =>
      exact Eq.trans (listMapConsSum f a l)
        (Eq.trans (congrArg (fun w => w + (l.map f).sum) (h a))
          (Eq.trans (congrArg (fun w => g a + w) ih) (listMapConsSum g a l).symm))


-- Reference: Lean 4 core (`List.rec`, `add_add_add_comm`).
/-- List sums distribute over addition of the summands. -/
theorem listSum_map_add {N : Type u} [AddCommMonoid N] {n : ℕ} (l : List (Fin n))
    (f g : Fin n → N) :
    (l.map (fun a => f a + g a)).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => exact Eq.trans (listMapNilSum (fun a => f a + g a)) (listMapNilSumAdd f g).symm
  | cons a l ih =>
      exact Eq.trans (listMapConsSum (fun a => f a + g a) a l)
        (Eq.trans (congrArg (fun w => (f a + g a) + w) ih)
          (Eq.trans (add_add_add_comm (f a) (g a) ((l.map f).sum) ((l.map g).sum))
            (Eq.trans (congrArg (fun w => w + ((a :: l).map g).sum) (listMapConsSum f a l))
              (congrArg (fun w => (f a + (l.map f).sum) + w) (listMapConsSum g a l))).symm))

-- Reference: Lean 4 core (`List.rec`, `mul_add`).
/-- A constant factor pulls out of a list sum on the left. -/
theorem listSum_map_mul_left {R : Type u} [Semiring R] {n : ℕ} (l : List (Fin n))
    (c : R) (f : Fin n → R) : (l.map (fun a => c * f a)).sum = c * (l.map f).sum := by
  induction l with
  | nil => exact Eq.trans (listMapNilSum (fun a => c * f a)) (listMapNilMul c f).symm
  | cons a l ih =>
      exact Eq.trans (listMapConsSum (fun a => c * f a) a l)
        (Eq.trans (congrArg (fun w => (c * f a) + w) ih)
          (Eq.trans (mul_add c (f a) ((l.map f).sum)).symm
            (congrArg (fun w => c * w) (listMapConsSum f a l)).symm))

-- Reference: Lean 4 core (`List.rec`, `Pi.add_apply`).
/-- A list sum of functions, evaluated pointwise. -/
theorem listSum_apply {n m : ℕ} {M : Type u} [AddCommMonoid M] (l : List (Fin n))
    (f : Fin n → Fin m → M) (j : Fin m) :
    ((l.map f).sum) j = (l.map (fun a => f a j)).sum := by
  induction l with
  | nil =>
      exact Eq.trans (congrArg (fun w : Fin m → M => w j) (listMapNilSum f))
        (Eq.trans (Pi.zero_apply j) (listMapNilSum (fun a => f a j)).symm)
  | cons a l ih =>
      exact Eq.trans (congrArg (fun w : Fin m → M => w j) (listMapConsSum f a l))
        (Eq.trans (Pi.add_apply (f a) ((l.map f).sum) j)
          (Eq.trans (congrArg (fun w => f a j + w) ih)
            (listMapConsSum (fun a => f a j) a l).symm))

-- Reference: Lean 4 core (`List.rec`, `add_zero`).
/-- A list sum of zeros is zero. -/
theorem listSum_zero {N : Type u} [AddCommMonoid N] {n : ℕ} (l : List (Fin n)) :
    (l.map (fun _ => (0 : N))).sum = 0 := by
  induction l with
  | nil => exact listMapNilSum (fun _ => (0 : N))
  | cons a l ih =>
      exact Eq.trans (listMapConsSum (fun _ => (0 : N)) a l)
        (Eq.trans (congrArg (fun w => (0 : N) + w) ih) (add_zero 0))

-- Reference: line 165-169 (listSum_ite_zero, cons case with `j ≠ a`).
/-- Peel: the cons step of `listSum_ite_zero` when `j ≠ a`. -/
theorem listSumIteZeroConsNe {M : Type u} [AddCommMonoid M] {n : ℕ} {a j : Fin n}
    {l : List (Fin n)} {x : Fin n → M} (h : ¬ j = a)
    (ih : j ∉ l → (l.map (fun i => if j = i then x i else 0)).sum = 0)
    (hj : j ∉ a :: l) :
    ((a :: l).map (fun i => if j = i then x i else 0)).sum = 0 :=
  Eq.trans (listMapConsSum (fun i => if j = i then x i else 0) a l)
    (Eq.trans (congrArg (fun w => w + (l.map (fun i => if j = i then x i else 0)).sum)
        (ite_eq_right h))
      (Eq.trans (zero_add (l.map (fun i => if j = i then x i else 0)).sum)
        (ih (fun hjl => hj (List.mem_cons.mpr (Or.inr hjl))))))

-- Reference: Lean 4 core (`List.rec`, `List.nodup_cons`, `ite` laws).  The
-- membership of `j` is carried as a `Prop` hypothesis (never a `Decidable`
-- instance — the list-membership instance at the pin falls back to
-- `Classical.propDecidable`, which would taint the declaration).
/-- If `j ∉ l`, the sum of `if j = i then x i else 0` over `l` is `0`. -/
theorem listSum_ite_zero {M : Type u} [AddCommMonoid M] {n : ℕ} (l : List (Fin n))
    (j : Fin n) (x : Fin n → M) (hj : j ∉ l) :
    (l.map (fun i => if j = i then x i else 0)).sum = 0 := by
  revert hj
  induction l with
  | nil => intro _; exact listMapNilSum _
  | cons a l ih =>
      intro hj
      cases (inferInstance : Decidable (j = a)) with
      | isTrue h => exact absurd (List.mem_cons.mpr (Or.inl h)) hj
      | isFalse h => exact listSumIteZeroConsNe h ih hj

-- Reference: line 186-188 (listSum_ite_mem, cons case with `j = a`).
/-- Peel: the cons step of `listSum_ite_mem` when `j = a`. -/
theorem listSumIteMemConsEq {M : Type u} [AddCommMonoid M] {n : ℕ} {a j : Fin n}
    {l : List (Fin n)} {x : Fin n → M} (ha : a ∉ l) (h : j = a) :
    ((a :: l).map (fun i => if j = i then x i else 0)).sum = x j :=
  Eq.trans (listMapConsSum (fun i => if j = i then x i else 0) a l)
    (Eq.trans (congrArg (fun w => w + (l.map (fun i => if j = i then x i else 0)).sum)
        (ite_eq_left h))
      (Eq.trans (congrArg (fun w => x a + w)
          (listSum_ite_zero l j x (fun hjl => ha (Eq.subst h hjl))))
        (Eq.trans (add_zero (x a)) (congrArg x h).symm)))

-- Reference: line 189-190 (listSum_ite_mem, cons case with `j ≠ a`).
/-- Peel: the cons step of `listSum_ite_mem` when `j ≠ a`. -/
theorem listSumIteMemConsNe {M : Type u} [AddCommMonoid M] {n : ℕ} {a j : Fin n}
    {l : List (Fin n)} {x : Fin n → M} (hnd : l.Nodup) (h : ¬ j = a)
    (ih : l.Nodup → j ∈ l → (l.map (fun i => if j = i then x i else 0)).sum = x j)
    (hj : j ∈ a :: l) :
    ((a :: l).map (fun i => if j = i then x i else 0)).sum = x j :=
  Eq.trans (listMapConsSum (fun i => if j = i then x i else 0) a l)
    (Eq.trans (congrArg (fun w => w + (l.map (fun i => if j = i then x i else 0)).sum)
        (ite_eq_right h))
      (Eq.trans (zero_add (l.map (fun i => if j = i then x i else 0)).sum)
        (ih hnd ((List.mem_cons.mp hj).resolve_left h))))

-- Reference: Lean 4 core (`List.rec`, `List.nodup_cons`, `ite` laws).
/-- If `j ∈ l` with `l` nodup, the sum of `if j = i then x i else 0` over `l`
is `x j`. -/
theorem listSum_ite_mem {M : Type u} [AddCommMonoid M] {n : ℕ} (l : List (Fin n))
    (hnd : l.Nodup) (j : Fin n) (x : Fin n → M) (hj : j ∈ l) :
    (l.map (fun i => if j = i then x i else 0)).sum = x j := by
  revert hnd hj
  induction l with
  | nil => intro _ hj; exact absurd hj List.not_mem_nil
  | cons a l ih =>
      intro hnd hj
      have hl : a ∉ l ∧ l.Nodup := List.nodup_cons.mp hnd
      cases (inferInstance : Decidable (j = a)) with
      | isTrue h => exact listSumIteMemConsEq hl.1 h
      | isFalse h => exact listSumIteMemConsNe hl.2 h ih hj

-- Reference: Axler, LADR 4th ed., Ch. 2 (the standard basis spans `F^n`);
-- mathlib (`List.mem_finRange`, `List.nodup_finRange`).
/-- The single-occurrence sum over `Fin n`: `∑ i, (if j = i then x i else 0) = x j`. -/
theorem finSum_ite {M : Type u} [AddCommMonoid M] {n : ℕ} (j : Fin n) (x : Fin n → M) :
    finSum n (fun i => if j = i then x i else 0) = x j :=
  listSum_ite_mem (List.finRange n) (List.nodup_finRange n) j x (List.mem_finRange j)


-- Reference: mathlib (`RingHom` is an `AddMonoidHomClass`; `map_add`, `map_zero`);
-- proved by hand by `List` induction (the `Finset` version `map_sum` is
-- choice-tainted at the pin).
/-- A ring homomorphism commutes with list sums. -/
theorem mapListSum {R L : Type u} [Semiring R] [Semiring L] (φ : R →+* L) {k : ℕ}
    (f : Fin k → R) (l : List (Fin k)) :
    φ ((l.map f).sum) = (l.map (fun i => φ (f i))).sum := by
  induction l with
  | nil =>
      exact Eq.trans (congrArg φ (listMapNilSum f))
        (Eq.trans (map_zero φ) (listMapNilSum (fun i => φ (f i))).symm)
  | cons a l ih =>
      exact Eq.trans (congrArg φ (listMapConsSum f a l))
        (Eq.trans (map_add φ (f a) ((l.map f).sum))
          (Eq.trans (congrArg (fun w => φ (f a) + w) ih)
            (listMapConsSum (fun i => φ (f i)) a l).symm))

/-! ## The ℚ-linear abelian category, carried by typeclass hypotheses -/

-- Reference: Hörmann, arXiv:2106.03803, Def 2.1 ("ℚ-linear" category: Hom sets
-- are ℚ-vector spaces and composition is ℚ-bilinear); Mac Lane, CWM, 2nd ed.,
-- Ch. VIII §1 (additive category = preadditive).  The base field is the variable
-- `B` (Hörmann's ℚ) because `Rat.instField` is choice-tainted at the pin.
/-- A `B`-linear (Hörmann: ℚ-linear) preadditive category: every Hom set is a
`B`-module and composition is `B`-bilinear. -/
class LinearCat (A : Type u) [Category A] [Preadditive A]
    (B : Type u) [Field B] [∀ X Y : A, Module B (X ⟶ Y)] : Prop where
  comp_smul_left : ∀ {X Y Z : A} (c : B) (f : X ⟶ Y) (g : Y ⟶ Z),
    (c • f) ≫ g = c • (f ≫ g)
  comp_smul_right : ∀ {X Y Z : A} (c : B) (f : X ⟶ Y) (g : Y ⟶ Z),
    f ≫ (c • g) = c • (f ≫ g)

-- Reference: Mac Lane, CWM, 2nd ed., Ch. VIII §1 (definition of an abelian
-- category), stated kernel-free: a kernel of `f` is a morphism `k` with
-- `k ≫ f = 0` through which every `g` with `g ≫ f = 0` factors uniquely — this
-- avoids the `kernel`/`HasLimit` names, which are `Classical.choice`-tainted at
-- the pin (P.0.4 pin-run census).
/-- An abelian category, in the kernel-free formulation of Mac Lane, CWM,
2nd ed., Ch. VIII §1: a preadditive category where every morphism has a kernel
and a cokernel (via their universal properties), every monomorphism is a
kernel and every epimorphism is a cokernel. -/
class AbelianCat (A : Type u) [Category A] [Preadditive A] : Prop where
  has_kernel : ∀ {X Y : A} (f : X ⟶ Y), ∃ (K : A) (k : K ⟶ X),
    (k ≫ f = 0) ∧ ∀ {Z : A} (g : Z ⟶ X), g ≫ f = 0 → ∃! h : Z ⟶ K, h ≫ k = g
  has_cokernel : ∀ {X Y : A} (f : X ⟶ Y), ∃ (C : A) (p : Y ⟶ C),
    (f ≫ p = 0) ∧ ∀ {Z : A} (g : Y ⟶ Z), f ≫ g = 0 → ∃! h : C ⟶ Z, p ≫ h = g
  mono_is_kernel : ∀ {X Y : A} (m : X ⟶ Y), Mono m →
    ∃ (Q : A) (p : Y ⟶ Q), (m ≫ p = 0) ∧
      ∀ {Z : A} (g : Z ⟶ Y), g ≫ p = 0 → ∃! h : Z ⟶ X, h ≫ m = g
  epi_is_cokernel : ∀ {X Y : A} (e : X ⟶ Y), Epi e →
    ∃ (Q : A) (k : Q ⟶ X), (k ≫ e = 0) ∧
      ∀ {Z : A} (g : X ⟶ Z), k ≫ g = 0 → ∃! h : Y ⟶ Z, e ≫ h = g

variable {B K L : Type u} [Field B] [Field K] [Field L] [Algebra B K] [Algebra K L]
variable {A : Type u} [Category A] [Preadditive A] [AbelianCat A]
variable [∀ X Y : A, Module B (X ⟶ Y)]
variable [LinearCat A B]
variable {m n : ℕ}


/-! ## Pointwise module structure on `FreeModHom` -/

-- Reference: Axler, LADR 4th ed., Ch. 1 (linear maps form a vector space:
-- pointwise operations); Hörmann, arXiv:2106.03803, Def 2.1 (the target category
-- of a fiber functor is f.d.-K-Vect, so its Hom sets carry the pointwise
-- module structure).
/-- The zero linear map between basis-carrying free modules. -/
instance freeModHomZeroInst : Zero (FreeModHom K m n) :=
  ⟨⟨fun _ => 0, fun _ _ => (add_zero (0 : FreeMod K n)).symm,
    fun c _ => (smul_zero c).symm⟩⟩

-- Reference: line 273 (freeModHomAddInst, map_add' field: `rw [f.map_add' x y, g.map_add' x y]`).
/-- Peel: pointwise addition unfolds both homs on `x + y`. -/
theorem freeModHomAddMapAdd (f g : FreeModHom K m n) (x y : FreeMod K m) :
    f.toFun (x + y) + g.toFun (x + y)
      = (f.toFun x + g.toFun x) + (f.toFun y + g.toFun y) :=
  Eq.trans (congrArg (fun w => w + g.toFun (x + y)) (f.map_add' x y))
    (Eq.trans (congrArg (fun w => (f.toFun x + f.toFun y) + w) (g.map_add' x y))
      (add_add_add_comm (f.toFun x) (f.toFun y) (g.toFun x) (g.toFun y)))

-- Reference: line 277 (freeModHomAddInst, map_smul' field: `rw [f.map_smul' c x, g.map_smul' c x]`).
/-- Peel: pointwise addition unfolds both homs on `c • x`. -/
theorem freeModHomAddMapSmul (f g : FreeModHom K m n) (c : K) (x : FreeMod K m) :
    f.toFun (c • x) + g.toFun (c • x) = c • (f.toFun x + g.toFun x) :=
  Eq.trans (congrArg (fun w => w + g.toFun (c • x)) (f.map_smul' c x))
    (Eq.trans (congrArg (fun w => c • f.toFun x + w) (g.map_smul' c x))
      (smul_add c (f.toFun x) (g.toFun x)).symm)

-- Reference: line 288 (freeModHomSMulKInst, map_add' field: `rw [f.map_add' x y]`).
/-- Peel: pointwise `K`-scaling unfolds `f` on `x + y`. -/
theorem freeModHomSmulKMapAdd (c : K) (f : FreeModHom K m n) (x y : FreeMod K m) :
    c • f.toFun (x + y) = c • f.toFun x + c • f.toFun y :=
  Eq.trans (congrArg (fun w => c • w) (f.map_add' x y)) (smul_add c (f.toFun x) (f.toFun y))

-- Reference: line 292 (freeModHomSMulKInst, map_smul' field: `rw [f.map_smul' d x]`).
/-- Peel: pointwise `K`-scaling unfolds `f` on `d • x`. -/
theorem freeModHomSmulKMapSmul (c d : K) (f : FreeModHom K m n) (x : FreeMod K m) :
    c • f.toFun (d • x) = d • (c • f.toFun x) :=
  Eq.trans (congrArg (fun w => c • w) (f.map_smul' d x)) (smul_comm c d (f.toFun x))

-- Reference: line 304 (freeModHomSMulBInst, map_add' field: `rw [f.map_add' x y]`).
/-- Peel: pointwise `B`-scaling unfolds `f` on `x + y`. -/
theorem freeModHomSmulBMapAdd (c : B) (f : FreeModHom K m n) (x y : FreeMod K m) :
    algebraMap B K c • f.toFun (x + y)
      = algebraMap B K c • f.toFun x + algebraMap B K c • f.toFun y :=
  Eq.trans (congrArg (fun w => algebraMap B K c • w) (f.map_add' x y))
    (smul_add (algebraMap B K c) (f.toFun x) (f.toFun y))

-- Reference: line 308 (freeModHomSMulBInst, map_smul' field: `rw [f.map_smul' d x]`).
/-- Peel: pointwise `B`-scaling unfolds `f` on `d • x`. -/
theorem freeModHomSmulBMapSmul (c : B) (d : K) (f : FreeModHom K m n) (x : FreeMod K m) :
    algebraMap B K c • f.toFun (d • x) = d • (algebraMap B K c • f.toFun x) :=
  Eq.trans (congrArg (fun w => algebraMap B K c • w) (f.map_smul' d x))
    (smul_comm (algebraMap B K c) d (f.toFun x))

-- Reference: Axler, LADR 4th ed., Ch. 1 (sum of linear maps, pointwise).
/-- Pointwise addition of morphisms of basis-carrying free modules. -/
instance freeModHomAddInst : Add (FreeModHom K m n) :=
  ⟨fun f g => ⟨fun x => f.toFun x + g.toFun x,
    fun x y => freeModHomAddMapAdd f g x y,
    fun c x => freeModHomAddMapSmul f g c x⟩⟩

-- Reference: Axler, LADR 4th ed., Ch. 1 (scalar multiple of a linear map,
-- pointwise).
/-- Pointwise scalar multiplication of morphisms of basis-carrying free
modules by a scalar of `K`. -/
instance freeModHomSMulKInst : SMul K (FreeModHom K m n) :=
  ⟨fun c f => ⟨fun x => c • f.toFun x,
    fun x y => freeModHomSmulKMapAdd c f x y,
    fun d x => freeModHomSmulKMapSmul c d f x⟩⟩

-- Reference: Hörmann, arXiv:2106.03803, Def 2.1 (a fiber functor over `K` is
-- ℚ-linear, i.e. `B`-linear for the base field `B` embedded in `K`); Axler,
-- LADR 4th ed., Ch. 1 (restriction of scalars along `B → K`).
/-- Pointwise scalar multiplication of morphisms of basis-carrying free
`K`-modules by a scalar of the base field `B` (via `algebraMap B K`). -/
instance freeModHomSMulBInst : SMul B (FreeModHom K m n) :=
  ⟨fun c f => ⟨fun x => algebraMap B K c • f.toFun x,
    fun x y => freeModHomSmulBMapAdd c f x y,
    fun d x => freeModHomSmulBMapSmul c d f x⟩⟩

-- Reference: Axler, LADR 4th ed., Ch. 1 (a linear map kills zero); the proof
-- mirrors `TensorBilMap.map_zero_left` in `BoringMath.FormalPeriods.FreeTensor`.
/-- A morphism of basis-carrying free modules sends `0` to `0`. -/
theorem freeModHomMapZero (f : FreeModHom K m n) : f.toFun 0 = 0 :=
  Eq.trans (congrArg f.toFun (zero_smul K (0 : FreeMod K m)).symm)
    (Eq.trans (f.map_smul' (0 : K) 0) (zero_smul K (f.toFun 0)))

-- Reference: definitional peel of `Pi.single` — primitive definitional lemma.
/-- Pointwise unfolding of `Pi.single`. -/
theorem piSingleApply {K : Type u} [Field K] {n : ℕ} (i j : Fin n) (a : K) :
    (Pi.single i a : Fin n → K) j = if j = i then a else (0 : K) := Pi.single_apply i a j

-- Reference: line 334 (freeModEqSumSingle, inner pointwise step).
/-- Peel: `(x • eᵢ) j = if j = i then x else 0`. -/
theorem smulSingleApply {K : Type u} [Field K] {n : ℕ} (x : K) (i j : Fin n) :
    (x • Pi.single i (1 : K)) j = if j = i then x else 0 := by
  cases (inferInstance : Decidable (j = i)) with
  | isTrue h =>
      exact Eq.trans (Pi.smul_apply x (Pi.single (M := fun _ => K) i (1 : K)) j)
        (Eq.trans (smul_eq_mul x (Pi.single (M := fun _ => K) i (1 : K) j))
          (Eq.trans (congrArg (fun w : K => x * w)
              (Eq.trans (congrArg (Pi.single (M := fun _ => K) i (1 : K)) h)
                (Pi.single_eq_same (M := fun _ => K) i (1 : K))))
            (Eq.trans (mul_one x) (ite_eq_left h).symm)))
  | isFalse h =>
      exact Eq.trans (Pi.smul_apply x (Pi.single (M := fun _ => K) i (1 : K)) j)
        (Eq.trans (smul_eq_mul x (Pi.single (M := fun _ => K) i (1 : K) j))
          (Eq.trans (congrArg (fun w : K => x * w)
              (Pi.single_eq_of_ne (M := fun _ => K) h (1 : K)))
            (Eq.trans (mul_zero x) (ite_eq_right h).symm)))

-- Reference: line 325-327 (freeModEqSumSingle, the `h1` step via `listSum_apply`).
/-- Peel: the applied sum equals the sum of the applied summands. -/
theorem finSumSingleApplyEq {K : Type u} [Field K] {n : ℕ} (x : FreeMod K n) (j : Fin n) :
    (((List.finRange n).map (fun i => x i • Pi.single i (1 : K))).sum) j
      = ((List.finRange n).map (fun i => (x i • Pi.single i (1 : K)) j)).sum :=
  listSum_apply (List.finRange n) (fun i => x i • Pi.single i 1) j

-- Reference: line 331-335 (freeModEqSumSingle, the `listSum_congr` step).
/-- Peel: the applied summands equal the `ite` summands. -/
theorem finSumSingleApplyCongr {K : Type u} [Field K] {n : ℕ} (x : FreeMod K n) (j : Fin n) :
    ((List.finRange n).map (fun i => (x i • Pi.single i (1 : K)) j)).sum
      = ((List.finRange n).map (fun i => if j = i then x i else 0)).sum :=
  listSum_congr (List.finRange n) (fun i => (x i • Pi.single i (1 : K)) j)
    (fun i => if j = i then x i else 0) (fun i => smulSingleApply (x i) i j)

-- Reference: line 336 (freeModEqSumSingle, the final `listSum_ite_mem` step).
/-- Peel: the pointwise basis expansion of `x`. -/
theorem freeModEqSumSinglePoint {K : Type u} [Field K] {n : ℕ} (x : FreeMod K n) (j : Fin n) :
    x j = (((List.finRange n).map (fun i => x i • Pi.single i (1 : K))).sum) j :=
  Eq.trans
    (listSum_ite_mem (List.finRange n) (List.nodup_finRange n) j x (List.mem_finRange j)).symm
    (Eq.trans (finSumSingleApplyCongr x j).symm (finSumSingleApplyEq x j).symm)

-- Reference: Axler, LADR 4th ed., Ch. 2 (the standard basis of `F^n`: every
-- vector is the linear combination `∑ i, x i • eᵢ` of the standard basis).
/-- Basis expansion in the standard basis: `x = ∑ i, x i • eᵢ` in `FreeMod K n`. -/
theorem freeModEqSumSingle {K : Type u} [Field K] {n : ℕ} (x : FreeMod K n) :
    x = finSum n (fun i => x i • Pi.single i 1) := by
  funext j
  unfold finSum
  exact freeModEqSumSinglePoint x j


-- Reference: Axler, LADR 4th ed., Ch. 1 (linearity extends to finite sums);
-- proved by hand by `List` induction (`freeModHomMapListSum`).
/-- A morphism of basis-carrying free modules commutes with list sums. -/
theorem freeModHomMapListSum (f : FreeModHom K m n) (k : ℕ) (g : Fin k → FreeMod K m)
    (l : List (Fin k)) :
    f.toFun ((l.map g).sum) = (l.map (fun i => f.toFun (g i))).sum := by
  induction l with
  | nil =>
      exact Eq.trans (congrArg f.toFun (listMapNilSum g))
        (Eq.trans (freeModHomMapZero f) (listMapNilSum (fun i => f.toFun (g i))).symm)
  | cons a l ih =>
      exact Eq.trans (congrArg f.toFun (listMapConsSum g a l))
        (Eq.trans (f.map_add' (g a) ((l.map g).sum))
          (Eq.trans (congrArg (fun w => f.toFun (g a) + w) ih)
            (listMapConsSum (fun i => f.toFun (g i)) a l).symm))

-- Reference: Axler, LADR 4th ed., Ch. 1 (linearity extends to finite sums).
/-- A morphism of basis-carrying free modules commutes with finite sums. -/
theorem freeModHomMapSum (f : FreeModHom K m n) (k : ℕ) (g : Fin k → FreeMod K m) :
    f.toFun (finSum k g) = finSum k (fun i => f.toFun (g i)) :=
  freeModHomMapListSum f k g (List.finRange k)

/-! ## The dual (contragredient) map and the dual pairing -/

-- Reference: line 372 (precompDual, map_add' field: `rw [f.map_add' x y]`).
/-- Peel: precomposition unfolds `f` on `x + y`. -/
theorem precompDualMapAdd (f : FreeModHom K m n) (ω : FreeModDual K n) (x y : FreeMod K m) :
    ω.toFun (f.toFun (x + y)) = ω.toFun (f.toFun x) + ω.toFun (f.toFun y) :=
  Eq.trans (congrArg ω.toFun (f.map_add' x y)) (ω.map_add' (f.toFun x) (f.toFun y))

-- Reference: line 376 (precompDual, map_smul' field: `rw [f.map_smul' c x]`).
/-- Peel: precomposition unfolds `f` on `c • x`. -/
theorem precompDualMapSmul (f : FreeModHom K m n) (ω : FreeModDual K n) (c : K) (x : FreeMod K m) :
    ω.toFun (f.toFun (c • x)) = c • ω.toFun (f.toFun x) :=
  Eq.trans (congrArg ω.toFun (f.map_smul' c x)) (ω.map_smul' c (f.toFun x))

-- Reference: Axler, LADR 4th ed., Ch. 3 (precomposition `ω ↦ ω ∘ α` is a linear
-- map into the one-dimensional target); Hörmann, arXiv:2106.03803, Def 2.3
-- (the relation uses `α∨`).
/-- Precomposition of a dual vector by `f`: the underlying map of `f∨(ω)`. -/
def precompDual (f : FreeModHom K m n) (ω : FreeModDual K n) : FreeModDual K m :=
  ⟨fun x => ω.toFun (f.toFun x),
    fun x y => precompDualMapAdd f ω x y,
    fun c x => precompDualMapSmul f ω c x⟩

-- Reference: Hörmann, arXiv:2106.03803, Def 2.3 (the relation uses `α∨`, the
-- dual of `α : M → N` acting on `H_dR(N)∨`); Axler, LADR 4th ed., Ch. 3 (the
-- dual map `T ↦ T'` is precomposition).
/-- The dual (contragredient) of a morphism of basis-carrying free modules:
precomposition, `α∨(ω) = ω ∘ α`. -/
def dualMap (f : FreeModHom K m n) : FreeModDual K n → FreeModDual K m :=
  fun ω => precompDual f ω

-- Reference: Axler, LADR 4th ed., Ch. 3 (a linear functional on `F^n` is
-- evaluated by its values on the standard basis); Hörmann, arXiv:2106.03803,
-- Def 2.5 (`eval_∫` evaluates `ω` at `∫_M(σ)`).
/-- The scalar value of a dual vector `ω : FreeModDual K n` at `x : FreeMod K n`:
the `0`-th coordinate of `ω x` in the one-dimensional target `FreeMod K 1`. -/
def dualVal (ω : FreeModDual K n) (x : FreeMod K n) : K := (ω.toFun x) 0

-- Reference: Axler, LADR 4th ed., Ch. 3 (precomposition unfolds definitionally);
-- primitive definitional lemma.
/-- The dual pairing unfolds through the dual map: `α∨(ω)(x) = ω(α x)`. -/
theorem dualValDualMap (f : FreeModHom K m n) (ω : FreeModDual K n) (x : FreeMod K m) :
    dualVal (dualMap f ω) x = dualVal ω (f.toFun x) := rfl

-- Reference: Axler, LADR 4th ed., Ch. 3; mathlib (`Pi.add_apply`).
/-- The dual pairing is additive in the dual argument. -/
theorem dualValAdd (ω₁ ω₂ : FreeModDual K n) (x : FreeMod K n) :
    dualVal (ω₁ + ω₂) x = dualVal ω₁ x + dualVal ω₂ x :=
  Pi.add_apply (ω₁.toFun x) (ω₂.toFun x) 0

-- Reference: Axler, LADR 4th ed., Ch. 3; mathlib (`Pi.smul_apply`, `smul_eq_mul`).
/-- The dual pairing is `K`-linear in the dual argument. -/
theorem dualValSmul (c : K) (ω : FreeModDual K n) (x : FreeMod K n) :
    dualVal (c • ω) x = c * dualVal ω x :=
  Eq.trans (Pi.smul_apply c (ω.toFun x) 0) (smul_eq_mul c (dualVal ω x))

-- Reference: Axler, LADR 4th ed., Ch. 3; mathlib (`Pi.zero_apply`).
/-- The zero dual vector pairs to zero. -/
theorem dualValZero (x : FreeMod K n) : dualVal (0 : FreeModDual K n) x = 0 :=
  Pi.zero_apply 0

-- Reference: Axler, LADR 4th ed., Ch. 2–3 (a linear functional is determined by
-- its values on the standard basis: `ω(x) = ∑ j, x j * ω(eⱼ)`); Hörmann,
-- arXiv:2106.03803, Def 2.5 (the period pairing `ω(∫_M σ)`).
/-- The dual pairing expands in the standard basis:
`ω(x) = ∑ j, x j * ω(eⱼ)`. -/
theorem dualValEqSum (ω : FreeModDual K n) (x : FreeMod K n) :
    dualVal ω x = finSum n (fun j => x j * dualVal ω (Pi.single j 1)) := by
  have h1 : ω.toFun x = finSum n (fun j => x j • ω.toFun (Pi.single j (1 : K))) :=
    Eq.trans (congrArg ω.toFun (freeModEqSumSingle x))
      (Eq.trans (freeModHomMapSum ω n (fun j => x j • Pi.single j (1 : K)))
        (listSum_congr (List.finRange n) _ _ (fun j => ω.map_smul' (x j) (Pi.single j (1 : K)))))
  calc (ω.toFun x) 0
      = (finSum n (fun j => x j • ω.toFun (Pi.single j (1 : K)))) 0 :=
          congrArg (fun v : FreeMod K 1 => v 0) h1
    _ = finSum n (fun j => (x j • ω.toFun (Pi.single j (1 : K))) 0) :=
          listSum_apply (List.finRange n) (fun j => x j • ω.toFun (Pi.single j (1 : K))) 0
    _ = finSum n (fun j => x j * (ω.toFun (Pi.single j (1 : K))) 0) :=
          listSum_congr (List.finRange n) _ _ (fun j =>
            Eq.trans (Pi.smul_apply (x j) (ω.toFun (Pi.single j (1 : K))) 0)
              (smul_eq_mul (x j) ((ω.toFun (Pi.single j (1 : K))) 0)))

/-! ## Base change along a ring homomorphism -/

-- Reference: Hörmann, arXiv:2106.03803, 2.2 (`∫` is a natural isomorphism after
-- base change to `ℂ`; here to the abstract extension `L` of `K`, with `B → L`
-- the composite `B → K → L`); mathlib (`RingHom.comp`).
/-- The composite ring homomorphism `B → K → L` (Hörmann's `ℚ → K → ℂ`). -/
def algBL (B K L : Type u) [Field B] [Field K] [Field L] [Algebra B K] [Algebra K L] :
    B →+* L :=
  (algebraMap K L).comp (algebraMap B K)

-- Reference: Dummit–Foote, §10.4 / base change of modules (extension of
-- scalars: `x ↦ φ ∘ x` on coordinates); Axler, LADR 4th ed., Ch. 2.
/-- Base change of a basis-carrying vector along `φ : R →+* L`:
coordinates are mapped by `φ` (the basis is unchanged: `eᵢ ↦ eᵢ ⊗ 1`). -/
def baseChangeOf {R L : Type u} [Field R] [Field L] (φ : R →+* L) {m : ℕ}
    (x : FreeMod R m) : FreeMod L m := fun i => φ (x i)

-- Reference: line 463 (baseChangeOfAdd: `rw [Pi.add_apply, map_add, Pi.add_apply]`).
/-- Peel: base change is additive, pointwise. -/
theorem baseChangeOfAddPoint {R L : Type u} [Field R] [Field L] (φ : R →+* L) {m : ℕ}
    (x y : FreeMod R m) (i : Fin m) :
    (baseChangeOf φ (x + y)) i = (baseChangeOf φ x + baseChangeOf φ y) i :=
  Eq.trans (Eq.trans (congrArg (fun w : R => φ w) (Pi.add_apply x y i))
      (map_add φ (x i) (y i)))
    (Pi.add_apply (baseChangeOf φ x) (baseChangeOf φ y) i).symm

-- Reference: line 473 (baseChangeOfSmul: `rw [Pi.smul_apply, smul_eq_mul, map_mul, ...]`).
/-- Peel: base change is linear, pointwise. -/
theorem baseChangeOfSmulPoint {R L : Type u} [Field R] [Field L] (φ : R →+* L) {m : ℕ}
    (c : R) (x : FreeMod R m) (i : Fin m) :
    (baseChangeOf φ (c • x)) i = (φ c • baseChangeOf φ x) i :=
  Eq.trans (congrArg (fun w : R => φ w) (Pi.smul_apply c x i))
    (Eq.trans (congrArg φ (smul_eq_mul c (x i)))
      (Eq.trans (map_mul φ c (x i))
        (Eq.trans (Pi.smul_apply (φ c) (baseChangeOf φ x) i)
          (smul_eq_mul (φ c) ((baseChangeOf φ x) i))).symm))

-- Reference: line 482 (baseChangeOfZero: `rw [Pi.zero_apply, map_zero, Pi.zero_apply]`).
/-- Peel: base change kills zero, pointwise. -/
theorem baseChangeOfZeroPoint {R L : Type u} [Field R] [Field L] (φ : R →+* L) {m : ℕ}
    (i : Fin m) : (baseChangeOf φ (0 : FreeMod R m)) i = ((0 : FreeMod L m)) i :=
  Eq.trans (congrArg (fun w : R => φ w) (Pi.zero_apply i))
    (Eq.trans (map_zero φ) (Pi.zero_apply (M := fun _ => L) i).symm)

-- Reference: base change is a ring-homomorphism on coordinates; mathlib
-- (`Pi.add_apply`, `map_add`).
/-- Base change is additive. -/
theorem baseChangeOfAdd {R L : Type u} [Field R] [Field L] (φ : R →+* L) {m : ℕ}
    (x y : FreeMod R m) : baseChangeOf φ (x + y) = baseChangeOf φ x + baseChangeOf φ y := by
  funext i
  exact baseChangeOfAddPoint φ x y i

-- Reference: base change is a ring-homomorphism on coordinates; mathlib
-- (`Pi.smul_apply`, `smul_eq_mul`, `map_mul`).
/-- Base change is `R`-linear: `φ (c • x) = φ c • φ x`. -/
theorem baseChangeOfSmul {R L : Type u} [Field R] [Field L] (φ : R →+* L) {m : ℕ} (c : R)
    (x : FreeMod R m) : baseChangeOf φ (c • x) = φ c • baseChangeOf φ x := by
  funext i
  exact baseChangeOfSmulPoint φ c x i

-- Reference: base change kills zero; mathlib (`Pi.zero_apply`, `map_zero`).
/-- Base change sends `0` to `0`. -/
theorem baseChangeOfZero {R L : Type u} [Field R] [Field L] (φ : R →+* L) {m : ℕ} :
    baseChangeOf φ (0 : FreeMod R m) = (0 : FreeMod L m) := by
  funext i
  exact baseChangeOfZeroPoint φ i

-- Reference: Axler, LADR 4th ed., Ch. 3 (a linear map in bases is its matrix
-- `x ↦ ∑ i, x i • f eᵢ`, with entries mapped by `φ`).
/-- The base change of a hom, as a function on coordinates:
`(φ f)(x)ⱼ = ∑ i, x i * φ ((f eᵢ) j)`. -/
def baseChangeHomOfFun {R L : Type u} [Field R] [Field L] (φ : R →+* L) {m n : ℕ}
    (f : FreeModHom R m n) (x : FreeMod L m) (j : Fin n) : L :=
  finSum m (fun i => x i * φ ((f.toFun (Pi.single i (1 : R))) j))

-- Reference: Axler, LADR 4th ed., Ch. 3; list lemmas (`listSum_congr`,
-- `listSum_map_add`, `Pi.add_apply`, `add_mul`).
/-- The base-changed hom is additive in the vector argument. -/
theorem baseChangeHomOfFunAdd {R L : Type u} [Field R] [Field L] (φ : R →+* L) {m n : ℕ}
    (f : FreeModHom R m n) (x y : FreeMod L m) (j : Fin n) :
    baseChangeHomOfFun φ f (x + y) j
      = baseChangeHomOfFun φ f x j + baseChangeHomOfFun φ f y j := by
  unfold baseChangeHomOfFun
  calc finSum m (fun i => (x + y) i * φ ((f.toFun (Pi.single i (1 : R))) j))
      = finSum m (fun i => (x i + y i) * φ ((f.toFun (Pi.single i (1 : R))) j)) :=
          listSum_congr (List.finRange m) _ _ (fun i =>
            congrArg (fun t => t * φ ((f.toFun (Pi.single i (1 : R))) j)) (Pi.add_apply x y i))
    _ = finSum m (fun i => (x i * φ ((f.toFun (Pi.single i (1 : R))) j)
          + y i * φ ((f.toFun (Pi.single i (1 : R))) j))) :=
          listSum_congr (List.finRange m) _ _ (fun i => add_mul (x i) (y i) _)
    _ = finSum m (fun i => x i * φ ((f.toFun (Pi.single i (1 : R))) j))
        + finSum m (fun i => y i * φ ((f.toFun (Pi.single i (1 : R))) j)) :=
          listSum_map_add (List.finRange m) _ _

-- Reference: Axler, LADR 4th ed., Ch. 3; list lemmas (`listSum_congr`,
-- `listSum_map_mul_left`, `Pi.smul_apply`, `smul_eq_mul`, `mul_assoc`).
/-- The base-changed hom is linear in the vector argument. -/
theorem baseChangeHomOfFunSmul {R L : Type u} [Field R] [Field L] (φ : R →+* L) {m n : ℕ}
    (f : FreeModHom R m n) (c : L) (x : FreeMod L m) (j : Fin n) :
    baseChangeHomOfFun φ f (c • x) j = c • baseChangeHomOfFun φ f x j := by
  unfold baseChangeHomOfFun
  calc finSum m (fun i => (c • x) i * φ ((f.toFun (Pi.single i (1 : R))) j))
      = finSum m (fun i => (c * x i) * φ ((f.toFun (Pi.single i (1 : R))) j)) :=
          listSum_congr (List.finRange m) _ _ (fun i =>
            congrArg (fun t => t * φ ((f.toFun (Pi.single i (1 : R))) j))
              (Eq.trans (Pi.smul_apply c x i) (smul_eq_mul c (x i))))
    _ = finSum m (fun i => c * (x i * φ ((f.toFun (Pi.single i (1 : R))) j))) :=
          listSum_congr (List.finRange m) _ _ (fun i => mul_assoc c (x i) _)
    _ = c * finSum m (fun i => x i * φ ((f.toFun (Pi.single i (1 : R))) j)) :=
          listSum_map_mul_left (List.finRange m) c _

-- Reference: base change of a linear map in bases (the matrix entries are
-- mapped by `φ`); Dummit–Foote, §10.4 (extension of scalars of a linear map).
/-- Base change of a morphism of basis-carrying free modules along
`φ : R →+* L`: in the standard bases, the matrix entries are mapped by `φ`. -/
def baseChangeHomOf {R L : Type u} [Field R] [Field L] (φ : R →+* L) {m n : ℕ}
    (f : FreeModHom R m n) : FreeModHom L m n where
  toFun := fun x j => baseChangeHomOfFun φ f x j
  map_add' := fun x y => by
    funext j
    exact baseChangeHomOfFunAdd φ f x y j
  map_smul' := fun c x => by
    funext j
    exact baseChangeHomOfFunSmul φ f c x j

-- Reference: definitional peel of `baseChangeHomOf` — primitive definitional lemma.
/-- Pointwise unfolding of the base change of a hom. -/
theorem baseChangeHomOfToFunApply {R L : Type u} [Field R] [Field L] (φ : R →+* L) {m n : ℕ}
    (f : FreeModHom R m n) (x : FreeMod L m) (j : Fin n) :
    (baseChangeHomOf φ f).toFun x j = baseChangeHomOfFun φ f x j := rfl

-- Reference: definitional peel of `baseChangeHomOfFun` — primitive definitional lemma.
/-- Unfolding of the base-changed hom on coordinates. -/
theorem baseChangeHomOfFunEq {R L : Type u} [Field R] [Field L] (φ : R →+* L) {m n : ℕ}
    (f : FreeModHom R m n) (x : FreeMod L m) (j : Fin n) :
    baseChangeHomOfFun φ f x j
      = finSum m (fun i => x i * φ ((f.toFun (Pi.single i (1 : R))) j)) := rfl

-- Reference: Axler, LADR 4th ed., Ch. 2–3 (matrix expansion
-- `f x = ∑ i, x i • f eᵢ`); list lemmas (`listSum_congr`, `listSum_apply`,
-- `Pi.smul_apply`, `smul_eq_mul`).
/-- Base change of a hom decomposes: `(φ f)(x) = ∑ i, x i • φ (f eᵢ)`. -/
theorem baseChangeHomOfDecomp {R L : Type u} [Field R] [Field L] (φ : R →+* L) {m n : ℕ}
    (f : FreeModHom R m n) (x : FreeMod L m) :
    (baseChangeHomOf φ f).toFun x
      = finSum m (fun i => x i • baseChangeOf φ (f.toFun (Pi.single i (1 : R)))) := by
  funext j
  calc (baseChangeHomOf φ f).toFun x j
      = baseChangeHomOfFun φ f x j := baseChangeHomOfToFunApply φ f x j
    _ = finSum m (fun i => x i * φ ((f.toFun (Pi.single i (1 : R))) j)) :=
          baseChangeHomOfFunEq φ f x j
    _ = finSum m (fun i => (x i • baseChangeOf φ (f.toFun (Pi.single i (1 : R)))) j) :=
          listSum_congr (List.finRange m) _ _ (fun i =>
            (Eq.trans (Pi.smul_apply (x i) (baseChangeOf φ (f.toFun (Pi.single i (1 : R)))) j)
              (smul_eq_mul (x i) ((baseChangeOf φ (f.toFun (Pi.single i (1 : R)))) j))).symm)
    _ = (finSum m (fun i => x i • baseChangeOf φ (f.toFun (Pi.single i (1 : R))))) j :=
          (listSum_apply (List.finRange m)
            (fun i => x i • baseChangeOf φ (f.toFun (Pi.single i (1 : R)))) j).symm

-- Reference: Axler, LADR 4th ed., Ch. 2–3 (matrix times vector:
-- `φ (f x) = (φ f)(φ x)` — base change commutes with linear maps);
-- Hörmann, arXiv:2106.03803, 2.2 (naturality of `∫` after base change); list
-- lemmas and `mapListSum`.
/-- Base change of a hom applied to a base-changed vector equals the base
change of the value: `φ (f x) = (φ f)(φ x)`. -/
theorem baseChangeHomOfApply {R L : Type u} [Field R] [Field L] (φ : R →+* L) {m n : ℕ}
    (f : FreeModHom R m n) (x : FreeMod R m) :
    baseChangeOf φ (f.toFun x) = (baseChangeHomOf φ f).toFun (baseChangeOf φ x) := by
  funext j
  have h1 : f.toFun x = finSum m (fun i => x i • f.toFun (Pi.single i (1 : R))) :=
    Eq.trans (congrArg f.toFun (freeModEqSumSingle x))
      (Eq.trans (freeModHomMapSum f m (fun i => x i • Pi.single i (1 : R)))
        (listSum_congr (List.finRange m) _ _
          (fun i => f.map_smul' (x i) (Pi.single i (1 : R)))))
  calc φ ((f.toFun x) j)
      = φ ((finSum m (fun i => x i • f.toFun (Pi.single i (1 : R)))) j) :=
          congrArg (fun v : FreeMod R n => φ (v j)) h1
    _ = φ (finSum m (fun i => (x i • f.toFun (Pi.single i (1 : R))) j)) :=
          congrArg φ (listSum_apply (List.finRange m)
            (fun i => x i • f.toFun (Pi.single i (1 : R))) j)
    _ = finSum m (fun i => φ ((x i • f.toFun (Pi.single i (1 : R))) j)) :=
          mapListSum φ (fun i => (x i • f.toFun (Pi.single i (1 : R))) j) (List.finRange m)
    _ = finSum m (fun i => φ (x i * (f.toFun (Pi.single i (1 : R))) j)) :=
          listSum_congr (List.finRange m) _ _ (fun i => congrArg φ
            (Eq.trans (Pi.smul_apply (x i) (f.toFun (Pi.single i (1 : R))) j)
              (smul_eq_mul (x i) ((f.toFun (Pi.single i (1 : R))) j))))
    _ = finSum m (fun i => (φ (x i) * φ ((f.toFun (Pi.single i (1 : R))) j))) :=
          listSum_congr (List.finRange m) _ _ (fun i => map_mul φ (x i) _)
    _ = finSum m (fun i => (baseChangeOf φ x) i * φ ((f.toFun (Pi.single i (1 : R))) j)) :=
          Eq.refl _

/-! ## The pairing of a `K`-dual with an `L`-vector -/

-- Reference: Hörmann, arXiv:2106.03803, Def 2.5 (`eval_∫` pairs `ω ∈ H_dR(M)∨`
-- with `∫_M(σ) ∈ H_dR(M) ⊗_K L`: `ω(∫_M σ) = ∑ j, φ(ω eⱼ) * (∫_M σ)ⱼ`);
-- Axler, LADR 4th ed., Ch. 2–3 (expansion in the standard basis).
/-- The pairing of a `K`-dual vector `ω : FreeModDual K n` with an `L`-vector
`y : FreeMod L n` along `φ : K →+* L`: `ω(y) = ∑ j, φ(ω eⱼ) * yⱼ`. -/
def pairL {K L : Type u} [Field K] [Field L] (φ : K →+* L) {n : ℕ}
    (ω : FreeModDual K n) (y : FreeMod L n) : L :=
  finSum n (fun j => φ (dualVal ω (Pi.single j (1 : K))) * y j)

-- Reference: Hörmann, arXiv:2106.03803, Def 2.5 (the pairing is linear in the
-- second argument); Axler, LADR 4th ed., Ch. 3; list lemmas.
/-- The pairing is additive in the second argument. -/
theorem pairLAddRight {K L : Type u} [Field K] [Field L] (φ : K →+* L) {n : ℕ}
    (ω : FreeModDual K n) (y z : FreeMod L n) :
    pairL φ ω (y + z) = pairL φ ω y + pairL φ ω z := by
  unfold pairL
  calc finSum n (fun j => φ (dualVal ω (Pi.single j (1 : K))) * (y + z) j)
      = finSum n (fun j => φ (dualVal ω (Pi.single j (1 : K))) * (y j + z j)) :=
          listSum_congr (List.finRange n) _ _ (fun j =>
            congrArg (fun t => _ * t) (Pi.add_apply y z j))
    _ = finSum n (fun j => (φ (dualVal ω (Pi.single j (1 : K))) * y j
          + φ (dualVal ω (Pi.single j (1 : K))) * z j)) :=
          listSum_congr (List.finRange n) _ _ (fun j => mul_add _ _ _)
    _ = finSum n (fun j => φ (dualVal ω (Pi.single j (1 : K))) * y j)
        + finSum n (fun j => φ (dualVal ω (Pi.single j (1 : K))) * z j) :=
          listSum_map_add (List.finRange n) _ _

-- Reference: Hörmann, arXiv:2106.03803, Def 2.5; Axler, LADR 4th ed., Ch. 3;
-- list lemmas (`listSum_congr`, `listSum_map_mul_left`, `mul_left_comm`).
/-- The pairing is `L`-linear in the second argument. -/
theorem pairLSmulRight {K L : Type u} [Field K] [Field L] (φ : K →+* L) {n : ℕ}
    (ω : FreeModDual K n) (c : L) (y : FreeMod L n) :
    pairL φ ω (c • y) = c * pairL φ ω y := by
  unfold pairL
  calc finSum n (fun j => φ (dualVal ω (Pi.single j (1 : K))) * (c • y) j)
      = finSum n (fun j => φ (dualVal ω (Pi.single j (1 : K))) * (c * y j)) :=
          listSum_congr (List.finRange n) _ _ (fun j =>
            congrArg (fun t => _ * t) (Eq.trans (Pi.smul_apply c y j) (smul_eq_mul c (y j))))
    _ = finSum n (fun j => c * (φ (dualVal ω (Pi.single j (1 : K))) * y j)) :=
          listSum_congr (List.finRange n) _ _ (fun j => mul_left_comm _ c _)
    _ = c * finSum n (fun j => φ (dualVal ω (Pi.single j (1 : K))) * y j) :=
          listSum_map_mul_left (List.finRange n) c _

-- Reference: Axler, LADR 4th ed., Ch. 3; list lemmas (`listSum_congr`,
-- `listSum_zero`, `Pi.zero_apply`, `mul_zero`).
/-- The pairing with the zero vector is zero. -/
theorem pairLZeroRight {K L : Type u} [Field K] [Field L] (φ : K →+* L) {n : ℕ}
    (ω : FreeModDual K n) : pairL φ ω 0 = 0 := by
  unfold pairL
  calc finSum n (fun j => φ (dualVal ω (Pi.single j (1 : K))) * (0 : FreeMod L n) j)
      = finSum n (fun j => φ (dualVal ω (Pi.single j (1 : K))) * (0 : L)) :=
          listSum_congr (List.finRange n) _ _ (fun j =>
            congrArg (fun t => _ * t) (Pi.zero_apply j))
    _ = finSum n (fun _ => (0 : L)) :=
          listSum_congr (List.finRange n) _ _ (fun j => mul_zero _)
    _ = 0 := listSum_zero (List.finRange n)

-- Reference: Axler, LADR 4th ed., Ch. 1 (linearity extends to finite sums);
-- proved by hand by `List` induction (`pairLListSum`).
/-- The pairing commutes with list sums in the second argument. -/
theorem pairLListSum {K L : Type u} [Field K] [Field L] (φ : K →+* L) {n : ℕ}
    (ω : FreeModDual K n) (k : ℕ) (g : Fin k → FreeMod L n) (l : List (Fin k)) :
    pairL φ ω ((l.map g).sum) = (l.map (fun i => pairL φ ω (g i))).sum := by
  induction l with
  | nil =>
      exact Eq.trans (congrArg (pairL φ ω) (listMapNilSum g))
        (Eq.trans (pairLZeroRight φ ω) (listMapNilSum (fun i => pairL φ ω (g i))).symm)
  | cons a l ih =>
      exact Eq.trans (congrArg (pairL φ ω) (listMapConsSum g a l))
        (Eq.trans (pairLAddRight φ ω (g a) ((l.map g).sum))
          (Eq.trans (congrArg (fun w => pairL φ ω (g a) + w) ih)
            (listMapConsSum (fun i => pairL φ ω (g i)) a l).symm))

-- Reference: Axler, LADR 4th ed., Ch. 1 (linearity extends to finite sums).
/-- The pairing commutes with finite sums in the second argument. -/
theorem pairLSumRight {K L : Type u} [Field K] [Field L] (φ : K →+* L) {n : ℕ}
    (ω : FreeModDual K n) (k : ℕ) (g : Fin k → FreeMod L n) :
    pairL φ ω (finSum k g) = finSum k (fun i => pairL φ ω (g i)) :=
  pairLListSum φ ω k g (List.finRange k)

-- Reference: Hörmann, arXiv:2106.03803, Def 2.5 (the pairing is linear in the
-- dual argument); Axler, LADR 4th ed., Ch. 3; list lemmas; mathlib (`map_add`,
-- `add_mul`).
/-- The pairing is additive in the dual argument. -/
theorem pairLAddLeft {K L : Type u} [Field K] [Field L] (φ : K →+* L) {n : ℕ}
    (ω₁ ω₂ : FreeModDual K n) (y : FreeMod L n) :
    pairL φ (ω₁ + ω₂) y = pairL φ ω₁ y + pairL φ ω₂ y := by
  unfold pairL
  calc finSum n (fun j => φ (dualVal (ω₁ + ω₂) (Pi.single j (1 : K))) * y j)
      = finSum n (fun j => φ (dualVal ω₁ (Pi.single j (1 : K))
          + dualVal ω₂ (Pi.single j (1 : K))) * y j) :=
          listSum_congr (List.finRange n) _ _ (fun j =>
            congrArg (fun t => φ t * y j) (dualValAdd ω₁ ω₂ _))
    _ = finSum n (fun j => (φ (dualVal ω₁ (Pi.single j (1 : K)))
          + φ (dualVal ω₂ (Pi.single j (1 : K)))) * y j) :=
          listSum_congr (List.finRange n) _ _ (fun j =>
            congrArg (fun t => t * y j) (map_add φ _ _))
    _ = finSum n (fun j => (φ (dualVal ω₁ (Pi.single j (1 : K))) * y j
          + φ (dualVal ω₂ (Pi.single j (1 : K))) * y j)) :=
          listSum_congr (List.finRange n) _ _ (fun j => add_mul _ _ _)
    _ = finSum n (fun j => φ (dualVal ω₁ (Pi.single j (1 : K))) * y j)
        + finSum n (fun j => φ (dualVal ω₂ (Pi.single j (1 : K))) * y j) :=
          listSum_map_add (List.finRange n) _ _

-- Reference: Hörmann, arXiv:2106.03803, Def 2.5; Axler, LADR 4th ed., Ch. 3;
-- list lemmas; mathlib (`map_mul`, `mul_assoc`).
/-- The pairing is `K`-linear in the dual argument. -/
theorem pairLSmulLeft {K L : Type u} [Field K] [Field L] (φ : K →+* L) {n : ℕ}
    (c : K) (ω : FreeModDual K n) (y : FreeMod L n) :
    pairL φ (c • ω) y = φ c * pairL φ ω y := by
  unfold pairL
  calc finSum n (fun j => φ (dualVal (c • ω) (Pi.single j (1 : K))) * y j)
      = finSum n (fun j => φ (c * dualVal ω (Pi.single j (1 : K))) * y j) :=
          listSum_congr (List.finRange n) _ _ (fun j =>
            congrArg (fun t => φ t * y j) (dualValSmul c ω _))
    _ = finSum n (fun j => (φ c * φ (dualVal ω (Pi.single j (1 : K)))) * y j) :=
          listSum_congr (List.finRange n) _ _ (fun j =>
            congrArg (fun t => t * y j) (map_mul φ c _))
    _ = finSum n (fun j => φ c * (φ (dualVal ω (Pi.single j (1 : K))) * y j)) :=
          listSum_congr (List.finRange n) _ _ (fun j => mul_assoc _ _ _)
    _ = φ c * finSum n (fun j => φ (dualVal ω (Pi.single j (1 : K))) * y j) :=
          listSum_map_mul_left (List.finRange n) (φ c) _

-- Reference: Axler, LADR 4th ed., Ch. 3; list lemmas (`listSum_congr`,
-- `listSum_zero`); mathlib (`map_zero`, `zero_mul`).
/-- The pairing with the zero dual vector is zero. -/
theorem pairLZeroLeft {K L : Type u} [Field K] [Field L] (φ : K →+* L) {n : ℕ}
    (y : FreeMod L n) : pairL φ (0 : FreeModDual K n) y = 0 := by
  unfold pairL
  calc finSum n (fun j => φ (dualVal (0 : FreeModDual K n) (Pi.single j (1 : K))) * y j)
      = finSum n (fun j => φ (0 : K) * y j) :=
          listSum_congr (List.finRange n) _ _ (fun j =>
            congrArg (fun t => φ t * y j) (dualValZero _))
    _ = finSum n (fun j => (0 : L) * y j) :=
          listSum_congr (List.finRange n) _ _ (fun j =>
            congrArg (fun t => t * y j) (map_zero φ))
    _ = finSum n (fun _ => (0 : L)) :=
          listSum_congr (List.finRange n) _ _ (fun j => zero_mul _)
    _ = 0 := listSum_zero (List.finRange n)

-- Reference: Hörmann, arXiv:2106.03803, Def 2.5 (`ω(∫_M σ)` pairs the `K`-dual
-- `ω` with the base-changed vector: `ω(φ y) = φ(ω y)`); Axler, LADR 4th ed.,
-- Ch. 2–3; list lemmas and `mapListSum`; mathlib (`map_mul`).
/-- The pairing of a dual vector with a base-changed vector:
`ω(φ y) = φ (ω y)`. -/
theorem pairLBase {K L : Type u} [Field K] [Field L] (φ : K →+* L) {n : ℕ}
    (ω : FreeModDual K n) (y : FreeMod K n) :
    pairL φ ω (baseChangeOf φ y) = φ (dualVal ω y) := by
  unfold pairL baseChangeOf
  calc finSum n (fun j => φ (dualVal ω (Pi.single j (1 : K))) * φ (y j))
      = finSum n (fun j => φ (dualVal ω (Pi.single j (1 : K)) * y j)) :=
          listSum_congr (List.finRange n) _ _ (fun j => (map_mul φ _ _).symm)
    _ = φ (finSum n (fun j => dualVal ω (Pi.single j (1 : K)) * y j)) :=
          (mapListSum φ (fun j => dualVal ω (Pi.single j (1 : K)) * y j) (List.finRange n)).symm
    _ = φ (finSum n (fun j => y j * dualVal ω (Pi.single j (1 : K)))) :=
          congrArg φ (listSum_congr (List.finRange n) _ _ (fun j => mul_comm _ _))
    _ = φ (dualVal ω y) := congrArg φ (dualValEqSum ω y).symm

-- Reference: definitional peel of `pairL` — primitive definitional lemma.
/-- Unfolding of the pairing. -/
theorem pairLEq {K L : Type u} [Field K] [Field L] (φ : K →+* L) {n : ℕ}
    (ω : FreeModDual K n) (y : FreeMod L n) :
    pairL φ ω y = finSum n (fun j => φ (dualVal ω (Pi.single j (1 : K))) * y j) := rfl

-- Reference: line 764 (pairLBaseHom: `rw [baseChangeHomOfDecomp φ f x]`).
/-- Peel: unfold the base-changed hom via its decomposition. -/
theorem pairLBaseHomDecomp {K L : Type u} [Field K] [Field L] (φ : K →+* L) {m n : ℕ}
    (f : FreeModHom K m n) (ω : FreeModDual K n) (x : FreeMod L m) :
    pairL φ ω ((baseChangeHomOf φ f).toFun x)
      = pairL φ ω (finSum m (fun i => x i • baseChangeOf φ (f.toFun (Pi.single i (1 : K))))) :=
  congrArg (pairL φ ω) (baseChangeHomOfDecomp φ f x)

-- Reference: Hörmann, arXiv:2106.03803, Def 2.3 (relation (2) uses `α∨(ω)`, and
-- the pairing satisfies `ω(φ α x) = α∨(ω)(φ x)` — the load-bearing identity for
-- eval_∫); Axler, LADR 4th ed., Ch. 2–3; list lemmas; mathlib (`mul_comm`).
/-- The key pairing identity: pairing `ω` with the base change of `f x`
equals pairing the dual `f∨(ω)` with `x`. -/
theorem pairLBaseHom {K L : Type u} [Field K] [Field L] (φ : K →+* L) {m n : ℕ}
    (f : FreeModHom K m n) (ω : FreeModDual K n) (x : FreeMod L m) :
    pairL φ ω ((baseChangeHomOf φ f).toFun x) = pairL φ (dualMap f ω) x := by
  calc pairL φ ω ((baseChangeHomOf φ f).toFun x)
      = pairL φ ω (finSum m (fun i => x i • baseChangeOf φ (f.toFun (Pi.single i (1 : K))))) :=
          pairLBaseHomDecomp φ f ω x
    _ = finSum m (fun i => pairL φ ω (x i • baseChangeOf φ (f.toFun (Pi.single i (1 : K))))) :=
          pairLSumRight φ ω m (fun i => x i • baseChangeOf φ (f.toFun (Pi.single i (1 : K))))
    _ = finSum m (fun i => (x i * pairL φ ω (baseChangeOf φ (f.toFun (Pi.single i (1 : K)))))) :=
          listSum_congr (List.finRange m) _ _ (fun i => pairLSmulRight φ ω (x i) _)
    _ = finSum m (fun i => (x i * φ (dualVal ω (f.toFun (Pi.single i (1 : K)))))) :=
          listSum_congr (List.finRange m) _ _ (fun i =>
            congrArg (fun t => x i * t) (pairLBase φ ω (f.toFun (Pi.single i (1 : K)))))
    _ = finSum m (fun i => (φ (dualVal (dualMap f ω) (Pi.single i (1 : K))) * x i)) :=
          listSum_congr (List.finRange m) _ _ (fun i =>
            Eq.trans (congrArg (fun t => x i * t)
              (congrArg φ (dualValDualMap f ω (Pi.single i (1 : K))))).symm (mul_comm _ _))
    _ = pairL φ (dualMap f ω) x := (pairLEq φ (dualMap f ω) x).symm

/-! ## The fiber functor and the quadruple -/

-- Reference: Axler, LADR 4th ed., Ch. 3 (injective = monic, surjective = epic
-- for linear maps between finite-dimensional spaces); Mac Lane, CWM, 2nd ed.,
-- Ch. VIII (exactness of a functor between abelian categories is equivalent to
-- preserving monomorphisms and epimorphisms).
/-- A morphism of basis-carrying free modules is monic iff its underlying
map is injective. -/
def IsMonoFreeModHom {R : Type u} [Field R] {m n : ℕ} (f : FreeModHom R m n) : Prop :=
  ∀ x y : FreeMod R m, f.toFun x = f.toFun y → x = y

-- Reference: Axler, LADR 4th ed., Ch. 3; Mac Lane, CWM, 2nd ed., Ch. VIII.
/-- A morphism of basis-carrying free modules is epic iff its underlying
map is surjective. -/
def IsEpiFreeModHom {R : Type u} [Field R] {m n : ℕ} (f : FreeModHom R m n) : Prop :=
  ∀ z : FreeMod R n, ∃ x : FreeMod R m, f.toFun x = z

-- Reference: Hörmann, arXiv:2106.03803, Def 2.1 (verified against the arXiv
-- HTML, v2): a fiber functor defined over `R` is a `B`-linear (Hörmann:
-- ℚ-linear), exact, faithful functor into f.d.-`R`-Vect; here into P.1's
-- basis-carrying spaces `FreeMod R (dim M)` — the dimension is data, and the
-- ℚ-linear/exact/faithful properties are carried as `Prop` fields (exactness
-- via the standard characterization in abelian categories: preserving
-- monomorphisms and epimorphisms — Mac Lane, CWM, 2nd ed., Ch. VIII).
/-- A fiber functor (Hörmann, Def 2.1) into the basis-carrying finite free
`R`-modules: on objects a dimension `dim M : ℕ` (the space is
`FreeMod R (dim M)`), on morphisms an explicit `FreeModHom`, with the functor
laws and the `B`-linear/exact/faithful properties as `Prop` fields. -/
structure FiberFunctor (A : Type u) [Category A] [Preadditive A]
    (B : Type u) [Field B] [∀ X Y : A, Module B (X ⟶ Y)]
    (R : Type u) [Field R] [Algebra B R] : Type u where
  dim : A → ℕ
  map : ∀ {M N : A}, (M ⟶ N) → FreeModHom R (dim M) (dim N)
  map_id : ∀ M : A, map (𝟙 M) = freeModHomId (dim M)
  map_comp : ∀ {M N P : A} (f : M ⟶ N) (g : N ⟶ P),
    map (f ≫ g) = freeModHomComp (map g) (map f)
  map_add : ∀ {M N : A} (f g : M ⟶ N), map (f + g) = map f + map g
  map_smul : ∀ {M N : A} (c : B) (f : M ⟶ N), map (c • f) = algebraMap B R c • map f
  faithful : ∀ {M N : A} (f g : M ⟶ N), map f = map g → f = g
  exact_mono : ∀ {M N : A} (f : M ⟶ N), Mono f → IsMonoFreeModHom (map f)
  exact_epi : ∀ {M N : A} (f : M ⟶ N), Epi f → IsEpiFreeModHom (map f)

-- Reference: Hörmann, arXiv:2106.03803, 2.2 (verified against the arXiv HTML,
-- v2): a quadruple `(𝒜, H_B, H_dR, ∫)` of a ℚ-linear abelian category with two
-- fiber functors over `B` (Hörmann's ℚ) and `K` (a subfield of `ℂ`), and a
-- natural isomorphism `∫ : H_B ⊗_B L ≅ H_dR ⊗_K L` (Hörmann: `L = ℂ`).  Since
-- the fiber functors land in basis-carrying spaces, base change to `L` keeps
-- the same dimension, and `∫_M` is the explicit matrix `int M : FreeModHom L
-- (hB.dim M) (hD.dim M)`; naturality is `intNat` and the inverse witnesses
-- `intInv` make `∫` an isomorphism.
/-- The formal-periods quadruple (Hörmann, arXiv:2106.03803, 2.2): an abelian
`B`-linear category `𝒜`, fiber functors `H_B` over `B` and `H_dR` over `K`, and
the comparison natural isomorphism `∫ : H_B ⊗_B L ≅ H_dR ⊗_K L` in bases
(`L` is Hörmann's `ℂ`). -/
structure PeriodQuadruple (A : Type u) [Category A] [Preadditive A] [AbelianCat A]
    (B : Type u) [Field B] [∀ X Y : A, Module B (X ⟶ Y)] [LinearCat A B]
    (K : Type u) [Field K] [Algebra B K]
    (L : Type u) [Field L] [Algebra K L] where
  hB : FiberFunctor A B B
  hD : FiberFunctor A B K
  int : ∀ M : A, FreeModHom L (hB.dim M) (hD.dim M)
  intNat : ∀ {M N : A} (α : M ⟶ N),
    freeModHomComp (int N) (baseChangeHomOf (algBL B K L) (hB.map α))
      = freeModHomComp (baseChangeHomOf (algebraMap K L) (hD.map α)) (int M)
  intInv : ∀ M : A, FreeModHom L (hD.dim M) (hB.dim M)
  intInvLeft : ∀ M : A,
    freeModHomComp (intInv M) (int M) = freeModHomId (hB.dim M)
  intInvRight : ∀ M : A,
    freeModHomComp (int M) (intInv M) = freeModHomId (hD.dim M)

/-! ## The raw symbols, the witness chains, and the relation -/

-- Reference: Hörmann, arXiv:2106.03803, Def 2.3 (the direct sum
-- `⨁_M H_B(M) ⊗_B H_dR(M)∨` is the free `B`-module on the abstract symbols
-- `(σ ⊗ ω)_M`); built by hand as an inductive (the `Finsupp.single` route is
-- choice-tainted at the pin — P.0.4 pin-run census), exactly as `TensorSym` in
-- `BoringMath.FormalPeriods.FreeTensor`.
/-- The raw terms of the free `B`-module on the symbols `(σ ⊗ ω)_M`:
`nil` is the empty sum, `sym M σ ω` is the abstract symbol, `add` is formal
addition and `smul` formal `B`-scalar multiplication. -/
inductive PeriodSym (Q : PeriodQuadruple A B K L) : Type u
  | nil : PeriodSym Q
  | sym (M : A) (σ : FreeMod B (Q.hB.dim M)) (ω : FreeModDual K (Q.hD.dim M)) :
      PeriodSym Q
  | add : PeriodSym Q → PeriodSym Q → PeriodSym Q
  | smul (c : B) : PeriodSym Q → PeriodSym Q

-- Reference: Hörmann, arXiv:2106.03803, Def 2.3 (the abstract symbol
-- `(σ ⊗ ω)_M`).
/-- The abstract symbol `(σ ⊗ ω)_M` as a raw formal sum. -/
abbrev periodSym (Q : PeriodQuadruple A B K L) (M : A) (σ : FreeMod B (Q.hB.dim M))
    (ω : FreeModDual K (Q.hD.dim M)) : PeriodSym Q := PeriodSym.sym M σ ω

-- Reference: Hörmann, arXiv:2106.03803, Def 2.3 (P(𝒜) is the quotient of the
-- direct sum by the relations (2); a relation holds iff generated by an
-- explicit chain — the witness-carrying inductive upgrade of program notes
-- §170); the constructors mirror `TensorChain` in
-- `BoringMath.FormalPeriods.FreeTensor`: the free-`B`-module laws, the
-- bilinearity relations (i)–(iv) of Hörmann's Key Lemma 3.2 (with an arbitrary
-- formal sum `x` as prefix), and the morphism relations (2) of Def 2.3.
/-- A witness chain for the equality of two formal sums: data (not a `Prop`),
so that "two formal sums are equal" carries its proof-relevant witness.
Constructors: the equivalence/congruence laws of the free `B`-module on the
symbols; the bilinearity relations (i)–(iv) over `B`; and the morphism
relations `(σ ⊗ α∨(ω))_M ∼ (α(σ) ⊗ ω)_N` (Hörmann, Def 2.3, relation (2)). -/
inductive PeriodChain (Q : PeriodQuadruple A B K L) :
    PeriodSym Q → PeriodSym Q → Type u
  | refl (x : PeriodSym Q) : PeriodChain Q x x
  | symm {x y : PeriodSym Q} (c : PeriodChain Q x y) : PeriodChain Q y x
  | trans {x y z : PeriodSym Q} (c₁ : PeriodChain Q x y) (c₂ : PeriodChain Q y z) :
      PeriodChain Q x z
  | addLeft {x y z : PeriodSym Q} (c : PeriodChain Q x y) :
      PeriodChain Q (PeriodSym.add z x) (PeriodSym.add z y)
  | addRight {x y z : PeriodSym Q} (c : PeriodChain Q x y) :
      PeriodChain Q (PeriodSym.add x z) (PeriodSym.add y z)
  | smulC (c : B) {x y : PeriodSym Q} (h : PeriodChain Q x y) :
      PeriodChain Q (PeriodSym.smul c x) (PeriodSym.smul c y)
  | nilLeft (x : PeriodSym Q) : PeriodChain Q (PeriodSym.add PeriodSym.nil x) x
  | nilRight (x : PeriodSym Q) : PeriodChain Q (PeriodSym.add x PeriodSym.nil) x
  | addAssoc (x y z : PeriodSym Q) :
      PeriodChain Q (PeriodSym.add (PeriodSym.add x y) z) (PeriodSym.add x (PeriodSym.add y z))
  | addComm (x y : PeriodSym Q) : PeriodChain Q (PeriodSym.add x y) (PeriodSym.add y x)
  | smulNil (c : B) : PeriodChain Q (PeriodSym.smul c PeriodSym.nil) PeriodSym.nil
  | smulAdd (c : B) (x y : PeriodSym Q) :
      PeriodChain Q (PeriodSym.smul c (PeriodSym.add x y))
        (PeriodSym.add (PeriodSym.smul c x) (PeriodSym.smul c y))
  | addSmul (a b : B) (x : PeriodSym Q) :
      PeriodChain Q (PeriodSym.smul (a + b) x)
        (PeriodSym.add (PeriodSym.smul a x) (PeriodSym.smul b x))
  | oneSmul (x : PeriodSym Q) : PeriodChain Q (PeriodSym.smul 1 x) x
  | zeroSmul (x : PeriodSym Q) : PeriodChain Q (PeriodSym.smul 0 x) PeriodSym.nil
  | smulSmul (a b : B) (x : PeriodSym Q) :
      PeriodChain Q (PeriodSym.smul a (PeriodSym.smul b x)) (PeriodSym.smul (a * b) x)
  | zeroSymRight (x : PeriodSym Q) (M : A) (σ : FreeMod B (Q.hB.dim M)) :
      PeriodChain Q (PeriodSym.add x (PeriodSym.sym M σ 0)) x
  | zeroSymLeft (x : PeriodSym Q) (M : A) (ω : FreeModDual K (Q.hD.dim M)) :
      PeriodChain Q (PeriodSym.add x (PeriodSym.sym M 0 ω)) x
  | addSymLeft (x : PeriodSym Q) (M : A) (σ₁ σ₂ : FreeMod B (Q.hB.dim M))
      (ω : FreeModDual K (Q.hD.dim M)) :
      PeriodChain Q
        (PeriodSym.add x (PeriodSym.add (PeriodSym.sym M σ₁ ω) (PeriodSym.sym M σ₂ ω)))
        (PeriodSym.add x (PeriodSym.sym M (σ₁ + σ₂) ω))
  | addSymRight (x : PeriodSym Q) (M : A) (σ : FreeMod B (Q.hB.dim M))
      (ω₁ ω₂ : FreeModDual K (Q.hD.dim M)) :
      PeriodChain Q
        (PeriodSym.add x (PeriodSym.add (PeriodSym.sym M σ ω₁) (PeriodSym.sym M σ ω₂)))
        (PeriodSym.add x (PeriodSym.sym M σ (ω₁ + ω₂)))
  | smulSym (x : PeriodSym Q) (M : A) (σ : FreeMod B (Q.hB.dim M))
      (ω : FreeModDual K (Q.hD.dim M)) (c : B) :
      PeriodChain Q (PeriodSym.add x (PeriodSym.sym M σ (c • ω)))
        (PeriodSym.add x (PeriodSym.sym M (c • σ) ω))
  | smulSymLeft (x : PeriodSym Q) (M : A) (σ : FreeMod B (Q.hB.dim M))
      (ω : FreeModDual K (Q.hD.dim M)) (c : B) :
      PeriodChain Q (PeriodSym.add x (PeriodSym.smul c (PeriodSym.sym M σ ω)))
        (PeriodSym.add x (PeriodSym.sym M (c • σ) ω))
  | morphRel (x : PeriodSym Q) {M N : A} (α : M ⟶ N) (σ : FreeMod B (Q.hB.dim M))
      (ω : FreeModDual K (Q.hD.dim N)) :
      PeriodChain Q
        (PeriodSym.add x (PeriodSym.sym M σ (dualMap (Q.hD.map α) ω)))
        (PeriodSym.add x (PeriodSym.sym N ((Q.hB.map α).toFun σ) ω))

-- Reference: Hörmann, arXiv:2106.03803, Def 2.3 (the quotient relation on formal
-- sums: related iff a witness chain exists — the chain is data, so the
-- relation is proof-relevant); Lean 4 core, Init/Prelude.lean (`Quot`).
/-- The witness-carrying relation on formal sums: `x` and `y` are related iff
a witness `PeriodChain` exists. -/
def periodRel (Q : PeriodQuadruple A B K L) (x y : PeriodSym Q) : Prop :=
  Nonempty (PeriodChain Q x y)

/-! ## The quotient: P(𝒜) and its operations -/

-- Reference: Dummit–Foote, §10.4 (the quotient's well-defined operations);
-- Lean 4 core, Init/Prelude.lean (`Quot.sound`).
/-- The relation is compatible with formal addition on the left. -/
theorem periodRelAddLeft (Q : PeriodQuadruple A B K L) (z x y : PeriodSym Q)
    (h : periodRel Q x y) : periodRel Q (PeriodSym.add z x) (PeriodSym.add z y) := by
  obtain ⟨ch⟩ := h
  exact ⟨PeriodChain.addLeft ch⟩

-- Reference: Dummit–Foote, §10.4; Lean 4 core, Init/Prelude.lean (`Quot.sound`).
/-- The relation is compatible with formal addition on the right. -/
theorem periodRelAddRight (Q : PeriodQuadruple A B K L) (x y z : PeriodSym Q)
    (h : periodRel Q x y) : periodRel Q (PeriodSym.add x z) (PeriodSym.add y z) := by
  obtain ⟨ch⟩ := h
  exact ⟨PeriodChain.addRight ch⟩

-- Reference: Dummit–Foote, §10.4; Lean 4 core, Init/Prelude.lean (`Quot.sound`).
/-- The relation is compatible with formal scalar multiplication. -/
theorem periodRelSmul (Q : PeriodQuadruple A B K L) (c : B) (x y : PeriodSym Q)
    (h : periodRel Q x y) : periodRel Q (PeriodSym.smul c x) (PeriodSym.smul c y) := by
  obtain ⟨ch⟩ := h
  exact ⟨PeriodChain.smulC c ch⟩

-- Reference: Hörmann, arXiv:2106.03803, Def 2.3 (P(𝒜) is the quotient of the
-- direct sum by the relations); Lean 4 core, Init/Prelude.lean (`Quot`).
/-- The space of formal periods `P(𝒜)`: the quotient of the free `B`-module
on the symbols `(σ ⊗ ω)_M` (presenting the finitely-supported direct sum
`⨁_M H_B(M) ⊗_B H_dR(M)∨`) by the witness-carrying relation generated by the
bilinearity laws and the morphism relations (2). -/
abbrev P (Q : PeriodQuadruple A B K L) : Type u := Quot (periodRel Q)

-- Reference: Dummit–Foote, §10.4 (addition on the quotient); mathlib,
-- Mathlib/Data/Quot.lean (`Quot.map₂`).
/-- Addition on `P(𝒜)`, descended from formal addition. -/
instance periodAddInst (Q : PeriodQuadruple A B K L) : Add (P Q) :=
  ⟨Quot.map₂ PeriodSym.add (periodRelAddLeft Q) (periodRelAddRight Q)⟩

-- Reference: Dummit–Foote, §10.4 (scalar multiplication on the quotient);
-- Lean 4 core, Init/Prelude.lean (`Quot.lift`).
/-- Scalar multiplication on `P(𝒜)` by `c : B`, descended from formal scalar
multiplication. -/
def periodSmulOp (Q : PeriodQuadruple A B K L) (c : B) : P Q → P Q :=
  Quot.lift (fun x => Quot.mk (periodRel Q) (PeriodSym.smul c x))
    (fun a b h => Quot.sound (periodRelSmul Q c a b h))

-- Reference: Dummit–Foote, §10.4.
/-- Scalar multiplication on `P(𝒜)` by `B`. -/
instance periodSMulInst (Q : PeriodQuadruple A B K L) : SMul B (P Q) :=
  ⟨periodSmulOp Q⟩

-- Reference: Hörmann, arXiv:2106.03803, Def 2.3, relation (i) (the empty sum
-- is zero).
/-- Zero on `P(𝒜)`: the class of the empty formal sum. -/
instance periodZeroInst (Q : PeriodQuadruple A B K L) : Zero (P Q) :=
  ⟨Quot.mk (periodRel Q) PeriodSym.nil⟩

-- Reference: mathlib, Mathlib/Data/Quot.lean (`Quot.map₂_mk`, proved by `rfl`);
-- primitive definitional lemma for the addition of classes.
/-- Addition of two classes is the class of the formal sum. -/
theorem periodAddMk (Q : PeriodQuadruple A B K L) (x y : PeriodSym Q) :
    (Quot.mk (periodRel Q) x + Quot.mk (periodRel Q) y : P Q)
      = Quot.mk (periodRel Q) (PeriodSym.add x y) :=
  Quot.map₂_mk PeriodSym.add (periodRelAddLeft Q) (periodRelAddRight Q) x y

-- Reference: mathlib, Mathlib/Data/Quot.lean (`Quot.lift_mk`, proved by `rfl`);
-- primitive definitional lemma for the scalar action on a class.
/-- Scalar multiplication of a class is the class of the formal scalar
multiple. -/
theorem periodSmulMk (Q : PeriodQuadruple A B K L) (c : B) (x : PeriodSym Q) :
    (c • Quot.mk (periodRel Q) x : P Q)
      = Quot.mk (periodRel Q) (PeriodSym.smul c x) :=
  Quot.lift_mk (fun x => Quot.mk (periodRel Q) (PeriodSym.smul c x))
    (fun a b h => Quot.sound (periodRelSmul Q c a b h)) x

-- Reference: Lean 4 core, Init/Prelude.lean (definitional unfolding of the
-- `Zero` instance); primitive definitional lemma.
/-- The `0` of `P(𝒜)` is the class of the empty formal sum. -/
theorem periodZeroMk (Q : PeriodQuadruple A B K L) :
    (0 : P Q) = Quot.mk (periodRel Q) PeriodSym.nil := Eq.refl _

-- Reference: Hörmann, arXiv:2106.03803, Def 2.3 ("We define `P(M)` as the image
-- of `H_B(M) ⊗_ℚ H_dR(M)∨` in `P(𝒜)`").
/-- A formal sum all of whose symbols are tagged by `M`. -/
def isSymSumAt (Q : PeriodQuadruple A B K L) (M : A) : PeriodSym Q → Prop
  | PeriodSym.nil => True
  | PeriodSym.sym N _ _ => N = M
  | PeriodSym.add x y => isSymSumAt Q M x ∧ isSymSumAt Q M y
  | PeriodSym.smul _ x => isSymSumAt Q M x

-- Reference: Hörmann, arXiv:2106.03803, Def 2.3 (P(M) is the image of
-- `H_B(M) ⊗_B H_dR(M)∨` in `P(𝒜)`).
/-- The formal periods `P(M)` of an object `M`: the image of the `M`-summand
`H_B(M) ⊗_B H_dR(M)∨` in `P(𝒜)`. -/
def PM (Q : PeriodQuadruple A B K L) (M : A) : Type u :=
  {q : P Q // ∃ x : PeriodSym Q, isSymSumAt Q M x ∧ Quot.mk (periodRel Q) x = q}

/-! ## The evaluation map eval_∫ -/

-- Reference: Hörmann, arXiv:2106.03803, Def 2.5 (verified against the arXiv
-- HTML, v2): `eval_∫` sends `(σ ⊗ ω)_M` to `∫σ ω := ω(∫_M(σ))` — the pairing of
-- `ω ∈ H_dR(M)∨` with the base-changed comparison `∫_M(σ) ∈ H_dR(M) ⊗_K L`,
-- computed in the standard bases.
/-- The value of `eval_∫` on a symbol `(σ ⊗ ω)_M`: the pairing of `ω` with
`∫_M(σ)` (base changed to `L`), i.e. Hörmann's `ω(∫_M(σ))`. -/
def evalSym (Q : PeriodQuadruple A B K L) (M : A) (σ : FreeMod B (Q.hB.dim M))
    (ω : FreeModDual K (Q.hD.dim M)) : L :=
  pairL (algebraMap K L) ω ((Q.int M).toFun (baseChangeOf (algBL B K L) σ))

-- Reference: Lean 4 core (definitional unfolding of `evalSym`); primitive
-- definitional lemma.
/-- Unfolding of `evalSym`. -/
theorem evalSymEq (Q : PeriodQuadruple A B K L) (M : A) (σ : FreeMod B (Q.hB.dim M))
    (ω : FreeModDual K (Q.hD.dim M)) :
    evalSym Q M σ ω
      = pairL (algebraMap K L) ω ((Q.int M).toFun (baseChangeOf (algBL B K L) σ)) :=
  Eq.refl _

-- Reference: line 1073 (evalSymAddLeft, `rw [evalSymEq ...]` chain).
/-- Peel: `evalSym` on `σ₁ + σ₂` unfolds to the pairing of the sum of the
base-changed images under `∫_M`. -/
theorem evalSymAddLeftUnfold (Q : PeriodQuadruple A B K L) (M : A)
    (σ₁ σ₂ : FreeMod B (Q.hB.dim M)) (ω : FreeModDual K (Q.hD.dim M)) :
    evalSym Q M (σ₁ + σ₂) ω
      = pairL (algebraMap K L) ω
          ((Q.int M).toFun (baseChangeOf (algBL B K L) σ₁)
            + (Q.int M).toFun (baseChangeOf (algBL B K L) σ₂)) :=
  Eq.trans (evalSymEq Q M (σ₁ + σ₂) ω)
    (Eq.trans (congrArg (fun v => pairL (algebraMap K L) ω ((Q.int M).toFun v))
        (baseChangeOfAdd (algBL B K L) σ₁ σ₂))
      (congrArg (fun v => pairL (algebraMap K L) ω v)
        ((Q.int M).map_add' (baseChangeOf (algBL B K L) σ₁) (baseChangeOf (algBL B K L) σ₂))))

-- Reference: Hörmann, arXiv:2106.03803, Def 2.5 (`eval_∫` is linear); the proof
-- chains base-change additivity, linearity of `∫_M`, and `pairLAddRight`.
/-- `evalSym` is additive in the Betti argument `σ`. -/
theorem evalSymAddLeft (Q : PeriodQuadruple A B K L) (M : A)
    (σ₁ σ₂ : FreeMod B (Q.hB.dim M)) (ω : FreeModDual K (Q.hD.dim M)) :
    evalSym Q M (σ₁ + σ₂) ω = evalSym Q M σ₁ ω + evalSym Q M σ₂ ω :=
  Eq.trans (evalSymAddLeftUnfold Q M σ₁ σ₂ ω)
    (Eq.trans (pairLAddRight (algebraMap K L) ω ((Q.int M).toFun (baseChangeOf (algBL B K L) σ₁))
        ((Q.int M).toFun (baseChangeOf (algBL B K L) σ₂)))
      (Eq.trans (congrArg (fun w => w + evalSym Q M σ₂ ω) (evalSymEq Q M σ₁ ω))
        (congrArg (fun w => pairL (algebraMap K L) ω
            ((Q.int M).toFun (baseChangeOf (algBL B K L) σ₁)) + w) (evalSymEq Q M σ₂ ω))).symm)

-- Reference: line 1086 (evalSymSmulLeft, `rw [evalSymEq ...]` chain).
/-- Peel: `evalSym` on `c • σ` unfolds to the pairing of the scaled base-changed
image under `∫_M`. -/
theorem evalSymSmulLeftUnfold (Q : PeriodQuadruple A B K L) (M : A) (c : B)
    (σ : FreeMod B (Q.hB.dim M)) (ω : FreeModDual K (Q.hD.dim M)) :
    evalSym Q M (c • σ) ω
      = pairL (algebraMap K L) ω
          ((algBL B K L) c • (Q.int M).toFun (baseChangeOf (algBL B K L) σ)) :=
  Eq.trans (evalSymEq Q M (c • σ) ω)
    (Eq.trans (congrArg (fun v => pairL (algebraMap K L) ω ((Q.int M).toFun v))
        (baseChangeOfSmul (algBL B K L) c σ))
      (congrArg (fun v => pairL (algebraMap K L) ω v)
        ((Q.int M).map_smul' ((algBL B K L) c) (baseChangeOf (algBL B K L) σ))))

-- Reference: Hörmann, arXiv:2106.03803, Def 2.5; the proof chains base-change
-- linearity, linearity of `∫_M`, and `pairLSmulRight`.
/-- `evalSym` is `B`-linear in the Betti argument `σ`. -/
theorem evalSymSmulLeft (Q : PeriodQuadruple A B K L) (M : A) (c : B)
    (σ : FreeMod B (Q.hB.dim M)) (ω : FreeModDual K (Q.hD.dim M)) :
    evalSym Q M (c • σ) ω = (algBL B K L) c * evalSym Q M σ ω :=
  Eq.trans (evalSymSmulLeftUnfold Q M c σ ω)
    (Eq.trans (pairLSmulRight (algebraMap K L) ω ((algBL B K L) c)
        ((Q.int M).toFun (baseChangeOf (algBL B K L) σ)))
      (congrArg (fun w => (algBL B K L) c * w) (evalSymEq Q M σ ω)).symm)

-- Reference: Hörmann, arXiv:2106.03803, Def 2.5; `pairLAddLeft`.
/-- `evalSym` is additive in the dual argument `ω`. -/
theorem evalSymAddRight (Q : PeriodQuadruple A B K L) (M : A)
    (σ : FreeMod B (Q.hB.dim M)) (ω₁ ω₂ : FreeModDual K (Q.hD.dim M)) :
    evalSym Q M σ (ω₁ + ω₂) = evalSym Q M σ ω₁ + evalSym Q M σ ω₂ :=
  Eq.trans (evalSymEq Q M σ (ω₁ + ω₂))
    (Eq.trans (pairLAddLeft (algebraMap K L) ω₁ ω₂
        ((Q.int M).toFun (baseChangeOf (algBL B K L) σ)))
      (Eq.trans (congrArg (fun w => w + evalSym Q M σ ω₂) (evalSymEq Q M σ ω₁))
        (congrArg (fun w => pairL (algebraMap K L) ω₁
            ((Q.int M).toFun (baseChangeOf (algBL B K L) σ)) + w) (evalSymEq Q M σ ω₂))).symm)

-- Reference: Hörmann, arXiv:2106.03803, Def 2.5; `pairLSmulLeft` (the `B`-action
-- on `H_dR(M)∨` is via `algebraMap B K`, and `algBL` is the composite
-- `B → K → L`, definitionally).
/-- `evalSym` is `B`-linear in the dual argument `ω`. -/
theorem evalSymSmulRight (Q : PeriodQuadruple A B K L) (M : A) (c : B)
    (σ : FreeMod B (Q.hB.dim M)) (ω : FreeModDual K (Q.hD.dim M)) :
    evalSym Q M σ (c • ω) = (algBL B K L) c * evalSym Q M σ ω :=
  Eq.trans (evalSymEq Q M σ (c • ω))
    (Eq.trans (pairLSmulLeft (algebraMap K L) (algebraMap B K c) ω
        ((Q.int M).toFun (baseChangeOf (algBL B K L) σ)))
      (congrArg (fun w => (algebraMap K L) (algebraMap B K c) * w) (evalSymEq Q M σ ω)).symm)

-- Reference: Hörmann, arXiv:2106.03803, Def 2.5 (bilinearity kills zero);
-- base change kills zero, `∫_M` kills zero, `pairLZeroRight`.
/-- `evalSym` vanishes at `σ = 0`. -/
theorem evalSymZeroLeft (Q : PeriodQuadruple A B K L) (M : A)
    (ω : FreeModDual K (Q.hD.dim M)) : evalSym Q M 0 ω = 0 :=
  Eq.trans (evalSymEq Q M 0 ω)
    (Eq.trans (congrArg (fun v => pairL (algebraMap K L) ω ((Q.int M).toFun v))
        (baseChangeOfZero (algBL B K L)))
      (Eq.trans (congrArg (fun v => pairL (algebraMap K L) ω v) (freeModHomMapZero (Q.int M)))
        (pairLZeroRight (algebraMap K L) ω)))

-- Reference: Hörmann, arXiv:2106.03803, Def 2.5 (bilinearity kills zero);
-- `pairLZeroLeft`.
/-- `evalSym` vanishes at `ω = 0`. -/
theorem evalSymZeroRight (Q : PeriodQuadruple A B K L) (M : A)
    (σ : FreeMod B (Q.hB.dim M)) : evalSym Q M σ 0 = 0 :=
  Eq.trans (evalSymEq Q M σ 0)
    (pairLZeroLeft (algebraMap K L) ((Q.int M).toFun (baseChangeOf (algBL B K L) σ)))

-- Reference: Hörmann, arXiv:2106.03803, Def 2.3 relation (2) + 2.2 (naturality
-- of `∫`): the morphism case of eval_∫'s well-definedness is exactly
-- `evalSym M σ (α∨ ω) = evalSym N (α σ) ω`, which follows from naturality of
-- `∫` (`intNat`) via the key pairing identity `pairLBaseHom` and the base-change
-- commutation `baseChangeHomOfApply`.
/-- The morphism-relation case: `ω(∫_M σ)` with `ω` replaced by `α∨(ω)` equals
`(α σ)` paired with `ω` at `N` — naturality of `∫`. -/
theorem evalSymMorph (Q : PeriodQuadruple A B K L) {M N : A} (α : M ⟶ N)
    (σ : FreeMod B (Q.hB.dim M)) (ω : FreeModDual K (Q.hD.dim N)) :
    evalSym Q M σ (dualMap (Q.hD.map α) ω)
      = evalSym Q N ((Q.hB.map α).toFun σ) ω := by
  have hint : (Q.int N).toFun
        ((baseChangeHomOf (algBL B K L) (Q.hB.map α)).toFun
          (baseChangeOf (algBL B K L) σ))
      = (baseChangeHomOf (algebraMap K L) (Q.hD.map α)).toFun
          ((Q.int M).toFun (baseChangeOf (algBL B K L) σ)) :=
    congrArg (fun F : FreeModHom L (Q.hB.dim M) (Q.hD.dim N) =>
      F.toFun (baseChangeOf (algBL B K L) σ)) (Q.intNat α)
  calc evalSym Q M σ (dualMap (Q.hD.map α) ω)
      = pairL (algebraMap K L) (dualMap (Q.hD.map α) ω)
          ((Q.int M).toFun (baseChangeOf (algBL B K L) σ)) :=
          evalSymEq Q M σ (dualMap (Q.hD.map α) ω)
    _ = pairL (algebraMap K L) ω ((baseChangeHomOf (algebraMap K L) (Q.hD.map α)).toFun
          ((Q.int M).toFun (baseChangeOf (algBL B K L) σ))) :=
          (pairLBaseHom (algebraMap K L) (Q.hD.map α) ω
            ((Q.int M).toFun (baseChangeOf (algBL B K L) σ))).symm
    _ = pairL (algebraMap K L) ω ((Q.int N).toFun
          ((baseChangeHomOf (algBL B K L) (Q.hB.map α)).toFun
            (baseChangeOf (algBL B K L) σ))) :=
          congrArg (fun v => pairL (algebraMap K L) ω v) hint.symm
    _ = pairL (algebraMap K L) ω ((Q.int N).toFun
          (baseChangeOf (algBL B K L) ((Q.hB.map α).toFun σ))) :=
          congrArg (fun v => pairL (algebraMap K L) ω ((Q.int N).toFun v))
            (baseChangeHomOfApply (algBL B K L) (Q.hB.map α) σ).symm
    _ = evalSym Q N ((Q.hB.map α).toFun σ) ω :=
          (evalSymEq Q N ((Q.hB.map α).toFun σ) ω).symm

-- Reference: Hörmann, arXiv:2106.03803, Def 2.5 (eval_∫ is defined on symbols
-- by `(σ⊗ω)_M ↦ ω(∫_M(σ))` and extended linearly); Dummit–Foote, §10.4 (the
-- lift to the free module on symbols, by recursion on formal sums).
/-- The raw evaluation on formal sums: the empty sum maps to `0`, a symbol
`(σ ⊗ ω)_M` maps to `ω(∫_M(σ))`, addition and `B`-scalars map to the
operations of `L` (via `algBL`). -/
def evalRaw (Q : PeriodQuadruple A B K L) : PeriodSym Q → L
  | PeriodSym.nil => 0
  | PeriodSym.sym M σ ω => evalSym Q M σ ω
  | PeriodSym.add x y => evalRaw Q x + evalRaw Q y
  | PeriodSym.smul c x => (algBL B K L) c * evalRaw Q x

-- Reference: Lean 4 core (definitional unfolding of `evalRaw`); primitive
-- definitional lemma.
/-- The empty formal sum evaluates to `0`. -/
theorem evalRawNil (Q : PeriodQuadruple A B K L) : evalRaw Q PeriodSym.nil = 0 := Eq.refl _

-- Reference: Lean 4 core (definitional unfolding of `evalRaw`); primitive
-- definitional lemma.
/-- A symbol `(σ ⊗ ω)_M` evaluates to `ω(∫_M(σ))`. -/
theorem evalRawSym (Q : PeriodQuadruple A B K L) (M : A) (σ : FreeMod B (Q.hB.dim M))
    (ω : FreeModDual K (Q.hD.dim M)) :
    evalRaw Q (PeriodSym.sym M σ ω) = evalSym Q M σ ω := Eq.refl _

-- Reference: Lean 4 core (definitional unfolding of `evalRaw`); primitive
-- definitional lemma.
/-- Formal sums evaluate to sums of values. -/
theorem evalRawAdd (Q : PeriodQuadruple A B K L) (x y : PeriodSym Q) :
    evalRaw Q (PeriodSym.add x y) = evalRaw Q x + evalRaw Q y := Eq.refl _

-- Reference: Lean 4 core (definitional unfolding of `evalRaw`); primitive
-- definitional lemma.
/-- Formal scalar multiples evaluate to scalar multiples. -/
theorem evalRawSmul (Q : PeriodQuadruple A B K L) (c : B) (x : PeriodSym Q) :
    evalRaw Q (PeriodSym.smul c x) = (algBL B K L) c * evalRaw Q x := Eq.refl _

-- Reference: line 1221 (eval_well_defined, addLeft case).
/-- Peel: `evalRaw` respects `PeriodChain.addLeft`. -/
theorem evalWellDefinedAddLeft (Q : PeriodQuadruple A B K L) (z x y : PeriodSym Q)
    (ih : evalRaw Q x = evalRaw Q y) :
    evalRaw Q (PeriodSym.add z x) = evalRaw Q (PeriodSym.add z y) :=
  Eq.trans (evalRawAdd Q z x)
    (Eq.trans (congrArg (fun w => evalRaw Q z + w) ih) (evalRawAdd Q z y).symm)

-- Reference: line 1225 (eval_well_defined, addRight case).
/-- Peel: `evalRaw` respects `PeriodChain.addRight`. -/
theorem evalWellDefinedAddRight (Q : PeriodQuadruple A B K L) (x y z : PeriodSym Q)
    (ih : evalRaw Q x = evalRaw Q y) :
    evalRaw Q (PeriodSym.add x z) = evalRaw Q (PeriodSym.add y z) :=
  Eq.trans (evalRawAdd Q x z)
    (Eq.trans (congrArg (fun w => w + evalRaw Q z) ih) (evalRawAdd Q y z).symm)

-- Reference: line 1229 (eval_well_defined, smulC case).
/-- Peel: `evalRaw` respects `PeriodChain.smulC`. -/
theorem evalWellDefinedSmulC (Q : PeriodQuadruple A B K L) (c : B) (x y : PeriodSym Q)
    (ih : evalRaw Q x = evalRaw Q y) :
    evalRaw Q (PeriodSym.smul c x) = evalRaw Q (PeriodSym.smul c y) :=
  Eq.trans (evalRawSmul Q c x)
    (Eq.trans (congrArg (fun w => (algBL B K L) c * w) ih) (evalRawSmul Q c y).symm)

-- Reference: line 1233 (eval_well_defined, nilLeft case).
/-- Peel: `evalRaw` respects `PeriodChain.nilLeft`. -/
theorem evalWellDefinedNilLeft (Q : PeriodQuadruple A B K L) (x : PeriodSym Q) :
    evalRaw Q (PeriodSym.add PeriodSym.nil x) = evalRaw Q x :=
  Eq.trans (evalRawAdd Q PeriodSym.nil x)
    (Eq.trans (congrArg (fun w => w + evalRaw Q x) (evalRawNil Q)) (zero_add (evalRaw Q x)))

-- Reference: line 1236 (eval_well_defined, nilRight case).
/-- Peel: `evalRaw` respects `PeriodChain.nilRight`. -/
theorem evalWellDefinedNilRight (Q : PeriodQuadruple A B K L) (x : PeriodSym Q) :
    evalRaw Q (PeriodSym.add x PeriodSym.nil) = evalRaw Q x :=
  Eq.trans (evalRawAdd Q x PeriodSym.nil)
    (Eq.trans (congrArg (fun w => evalRaw Q x + w) (evalRawNil Q)) (add_zero (evalRaw Q x)))

-- Reference: line 1239 (eval_well_defined, addAssoc case).
/-- Peel: `evalRaw` respects `PeriodChain.addAssoc`. -/
theorem evalWellDefinedAddAssoc (Q : PeriodQuadruple A B K L) (x y z : PeriodSym Q) :
    evalRaw Q (PeriodSym.add (PeriodSym.add x y) z)
      = evalRaw Q (PeriodSym.add x (PeriodSym.add y z)) :=
  Eq.trans (evalRawAdd Q (PeriodSym.add x y) z)
    (Eq.trans (congrArg (fun w => w + evalRaw Q z) (evalRawAdd Q x y))
      (Eq.trans (add_assoc (evalRaw Q x) (evalRaw Q y) (evalRaw Q z))
        (Eq.trans (congrArg (fun w => evalRaw Q x + w) (evalRawAdd Q y z).symm)
          (evalRawAdd Q x (PeriodSym.add y z)).symm)))

-- Reference: line 1244 (eval_well_defined, addComm case).
/-- Peel: `evalRaw` respects `PeriodChain.addComm`. -/
theorem evalWellDefinedAddComm (Q : PeriodQuadruple A B K L) (x y : PeriodSym Q) :
    evalRaw Q (PeriodSym.add x y) = evalRaw Q (PeriodSym.add y x) :=
  Eq.trans (evalRawAdd Q x y)
    (Eq.trans (add_comm (evalRaw Q x) (evalRaw Q y)) (evalRawAdd Q y x).symm)

-- Reference: line 1247 (eval_well_defined, smulNil case).
/-- Peel: `evalRaw` respects `PeriodChain.smulNil`. -/
theorem evalWellDefinedSmulNil (Q : PeriodQuadruple A B K L) (c : B) :
    evalRaw Q (PeriodSym.smul c PeriodSym.nil) = evalRaw Q PeriodSym.nil :=
  Eq.trans (evalRawSmul Q c PeriodSym.nil)
    (Eq.trans (congrArg (fun w => (algBL B K L) c * w) (evalRawNil Q))
      (Eq.trans (mul_zero ((algBL B K L) c)) (evalRawNil Q).symm))

-- Reference: line 1250 (eval_well_defined, smulAdd case).
/-- Peel: `evalRaw` respects `PeriodChain.smulAdd`. -/
theorem evalWellDefinedSmulAdd (Q : PeriodQuadruple A B K L) (c : B) (x y : PeriodSym Q) :
    evalRaw Q (PeriodSym.smul c (PeriodSym.add x y))
      = evalRaw Q (PeriodSym.add (PeriodSym.smul c x) (PeriodSym.smul c y)) :=
  Eq.trans (evalRawSmul Q c (PeriodSym.add x y))
    (Eq.trans (congrArg (fun w => (algBL B K L) c * w) (evalRawAdd Q x y))
      (Eq.trans (mul_add ((algBL B K L) c) (evalRaw Q x) (evalRaw Q y))
        (Eq.trans (congrArg (fun w => (algBL B K L) c * evalRaw Q x + w) (evalRawSmul Q c y).symm)
          (Eq.trans (congrArg (fun w => w + evalRaw Q (PeriodSym.smul c y))
              (evalRawSmul Q c x).symm)
            (evalRawAdd Q (PeriodSym.smul c x) (PeriodSym.smul c y)).symm))))

-- Reference: line 1255 (eval_well_defined, addSmul case).
/-- Peel: `evalRaw` respects `PeriodChain.addSmul`. -/
theorem evalWellDefinedAddSmul (Q : PeriodQuadruple A B K L) (a b : B) (x : PeriodSym Q) :
    evalRaw Q (PeriodSym.smul (a + b) x)
      = evalRaw Q (PeriodSym.add (PeriodSym.smul a x) (PeriodSym.smul b x)) :=
  Eq.trans (evalRawSmul Q (a + b) x)
    (Eq.trans (congrArg (fun w => w * evalRaw Q x) (map_add (algBL B K L) a b))
      (Eq.trans (add_mul ((algBL B K L) a) ((algBL B K L) b) (evalRaw Q x))
        (Eq.trans (congrArg (fun w => w + (algBL B K L) b * evalRaw Q x) (evalRawSmul Q a x).symm)
          (Eq.trans (congrArg (fun w => evalRaw Q (PeriodSym.smul a x) + w)
              (evalRawSmul Q b x).symm)
            (evalRawAdd Q (PeriodSym.smul a x) (PeriodSym.smul b x)).symm))))

-- Reference: line 1259 (eval_well_defined, oneSmul case).
/-- Peel: `evalRaw` respects `PeriodChain.oneSmul`. -/
theorem evalWellDefinedOneSmul (Q : PeriodQuadruple A B K L) (x : PeriodSym Q) :
    evalRaw Q (PeriodSym.smul 1 x) = evalRaw Q x :=
  Eq.trans (evalRawSmul Q 1 x)
    (Eq.trans (congrArg (fun w => w * evalRaw Q x) (map_one (algBL B K L)))
      (one_mul (evalRaw Q x)))

-- Reference: line 1262 (eval_well_defined, zeroSmul case).
/-- Peel: `evalRaw` respects `PeriodChain.zeroSmul`. -/
theorem evalWellDefinedZeroSmul (Q : PeriodQuadruple A B K L) (x : PeriodSym Q) :
    evalRaw Q (PeriodSym.smul 0 x) = evalRaw Q PeriodSym.nil :=
  Eq.trans (evalRawSmul Q 0 x)
    (Eq.trans (congrArg (fun w => w * evalRaw Q x) (map_zero (algBL B K L)))
      (Eq.trans (zero_mul (evalRaw Q x)) (evalRawNil Q).symm))

-- Reference: line 1265 (eval_well_defined, smulSmul case).
/-- Peel: `evalRaw` respects `PeriodChain.smulSmul`. -/
theorem evalWellDefinedSmulSmul (Q : PeriodQuadruple A B K L) (a b : B) (x : PeriodSym Q) :
    evalRaw Q (PeriodSym.smul a (PeriodSym.smul b x))
      = evalRaw Q (PeriodSym.smul (a * b) x) :=
  Eq.trans (evalRawSmul Q a (PeriodSym.smul b x))
    (Eq.trans (congrArg (fun w => (algBL B K L) a * w) (evalRawSmul Q b x))
      (Eq.trans (mul_assoc ((algBL B K L) a) ((algBL B K L) b) (evalRaw Q x)).symm
        (Eq.trans (congrArg (fun w => w * evalRaw Q x) (map_mul (algBL B K L) a b).symm)
          (evalRawSmul Q (a * b) x).symm)))

-- Reference: line 1269 (eval_well_defined, zeroSymRight case).
/-- Peel: `evalRaw` respects `PeriodChain.zeroSymRight`. -/
theorem evalWellDefinedZeroSymRight (Q : PeriodQuadruple A B K L) (x : PeriodSym Q)
    (M : A) (σ : FreeMod B (Q.hB.dim M)) :
    evalRaw Q (PeriodSym.add x (PeriodSym.sym M σ 0)) = evalRaw Q x :=
  Eq.trans (evalRawAdd Q x (PeriodSym.sym M σ 0))
    (Eq.trans (congrArg (fun w => evalRaw Q x + w) (evalRawSym Q M σ 0))
      (Eq.trans (congrArg (fun w => evalRaw Q x + w) (evalSymZeroRight Q M σ))
        (add_zero (evalRaw Q x))))

-- Reference: line 1273 (eval_well_defined, zeroSymLeft case).
/-- Peel: `evalRaw` respects `PeriodChain.zeroSymLeft`. -/
theorem evalWellDefinedZeroSymLeft (Q : PeriodQuadruple A B K L) (x : PeriodSym Q)
    (M : A) (ω : FreeModDual K (Q.hD.dim M)) :
    evalRaw Q (PeriodSym.add x (PeriodSym.sym M 0 ω)) = evalRaw Q x :=
  Eq.trans (evalRawAdd Q x (PeriodSym.sym M 0 ω))
    (Eq.trans (congrArg (fun w => evalRaw Q x + w) (evalRawSym Q M 0 ω))
      (Eq.trans (congrArg (fun w => evalRaw Q x + w) (evalSymZeroLeft Q M ω))
        (add_zero (evalRaw Q x))))

-- Reference: line 1277 (eval_well_defined, addSymLeft case).
/-- Peel: `evalRaw` respects `PeriodChain.addSymLeft`. -/
theorem evalWellDefinedAddSymLeft (Q : PeriodQuadruple A B K L) (x : PeriodSym Q)
    (M : A) (σ₁ σ₂ : FreeMod B (Q.hB.dim M)) (ω : FreeModDual K (Q.hD.dim M)) :
    evalRaw Q (PeriodSym.add x (PeriodSym.add (PeriodSym.sym M σ₁ ω) (PeriodSym.sym M σ₂ ω)))
      = evalRaw Q (PeriodSym.add x (PeriodSym.sym M (σ₁ + σ₂) ω)) :=
  Eq.trans (evalRawAdd Q x (PeriodSym.add (PeriodSym.sym M σ₁ ω) (PeriodSym.sym M σ₂ ω)))
    (Eq.trans (congrArg (fun w => evalRaw Q x + w)
        (evalRawAdd Q (PeriodSym.sym M σ₁ ω) (PeriodSym.sym M σ₂ ω)))
      (Eq.trans (congrArg (fun w => evalRaw Q x + w)
          (Eq.trans (congrArg (fun w => w + evalRaw Q (PeriodSym.sym M σ₂ ω))
              (evalRawSym Q M σ₁ ω))
            (congrArg (fun w => evalSym Q M σ₁ ω + w) (evalRawSym Q M σ₂ ω))))
        (Eq.trans (congrArg (fun w => evalRaw Q x + w) (evalSymAddLeft Q M σ₁ σ₂ ω)).symm
          (Eq.trans (congrArg (fun w => evalRaw Q x + w) (evalRawSym Q M (σ₁ + σ₂) ω)).symm
            (evalRawAdd Q x (PeriodSym.sym M (σ₁ + σ₂) ω)).symm))))

-- Reference: line 1284 (eval_well_defined, addSymRight case).
/-- Peel: `evalRaw` respects `PeriodChain.addSymRight`. -/
theorem evalWellDefinedAddSymRight (Q : PeriodQuadruple A B K L) (x : PeriodSym Q)
    (M : A) (σ : FreeMod B (Q.hB.dim M)) (ω₁ ω₂ : FreeModDual K (Q.hD.dim M)) :
    evalRaw Q (PeriodSym.add x (PeriodSym.add (PeriodSym.sym M σ ω₁) (PeriodSym.sym M σ ω₂)))
      = evalRaw Q (PeriodSym.add x (PeriodSym.sym M σ (ω₁ + ω₂))) :=
  Eq.trans (evalRawAdd Q x (PeriodSym.add (PeriodSym.sym M σ ω₁) (PeriodSym.sym M σ ω₂)))
    (Eq.trans (congrArg (fun w => evalRaw Q x + w)
        (evalRawAdd Q (PeriodSym.sym M σ ω₁) (PeriodSym.sym M σ ω₂)))
      (Eq.trans (congrArg (fun w => evalRaw Q x + w)
          (Eq.trans (congrArg (fun w => w + evalRaw Q (PeriodSym.sym M σ ω₂))
              (evalRawSym Q M σ ω₁))
            (congrArg (fun w => evalSym Q M σ ω₁ + w) (evalRawSym Q M σ ω₂))))
        (Eq.trans (congrArg (fun w => evalRaw Q x + w) (evalSymAddRight Q M σ ω₁ ω₂)).symm
          (Eq.trans (congrArg (fun w => evalRaw Q x + w) (evalRawSym Q M σ (ω₁ + ω₂))).symm
            (evalRawAdd Q x (PeriodSym.sym M σ (ω₁ + ω₂))).symm))))

-- Reference: line 1291 (eval_well_defined, smulSym case).
/-- Peel: `evalRaw` respects `PeriodChain.smulSym`. -/
theorem evalWellDefinedSmulSym (Q : PeriodQuadruple A B K L) (x : PeriodSym Q)
    (M : A) (σ : FreeMod B (Q.hB.dim M)) (ω : FreeModDual K (Q.hD.dim M)) (c : B) :
    evalRaw Q (PeriodSym.add x (PeriodSym.sym M σ (c • ω)))
      = evalRaw Q (PeriodSym.add x (PeriodSym.sym M (c • σ) ω)) :=
  Eq.trans (evalRawAdd Q x (PeriodSym.sym M σ (c • ω)))
    (Eq.trans (congrArg (fun w => evalRaw Q x + w) (evalRawSym Q M σ (c • ω)))
      (Eq.trans (congrArg (fun w => evalRaw Q x + w)
          (Eq.trans (evalSymSmulRight Q M c σ ω) (evalSymSmulLeft Q M c σ ω).symm))
        (Eq.trans (congrArg (fun w => evalRaw Q x + w) (evalRawSym Q M (c • σ) ω)).symm
          (evalRawAdd Q x (PeriodSym.sym M (c • σ) ω)).symm)))

-- Reference: line 1297 (eval_well_defined, smulSymLeft case).
/-- Peel: `evalRaw` respects `PeriodChain.smulSymLeft`. -/
theorem evalWellDefinedSmulSymLeft (Q : PeriodQuadruple A B K L) (x : PeriodSym Q)
    (M : A) (σ : FreeMod B (Q.hB.dim M)) (ω : FreeModDual K (Q.hD.dim M)) (c : B) :
    evalRaw Q (PeriodSym.add x (PeriodSym.smul c (PeriodSym.sym M σ ω)))
      = evalRaw Q (PeriodSym.add x (PeriodSym.sym M (c • σ) ω)) :=
  Eq.trans (evalRawAdd Q x (PeriodSym.smul c (PeriodSym.sym M σ ω)))
    (Eq.trans (congrArg (fun w => evalRaw Q x + w) (evalRawSmul Q c (PeriodSym.sym M σ ω)))
      (Eq.trans (congrArg (fun w => evalRaw Q x + w)
          (congrArg (fun w => (algBL B K L) c * w) (evalRawSym Q M σ ω)))
        (Eq.trans (congrArg (fun w => evalRaw Q x + w) (evalSymSmulLeft Q M c σ ω).symm)
          (Eq.trans (congrArg (fun w => evalRaw Q x + w) (evalRawSym Q M (c • σ) ω)).symm
            (evalRawAdd Q x (PeriodSym.sym M (c • σ) ω)).symm))))

-- Reference: line 1303 (eval_well_defined, morphRel case).
/-- Peel: `evalRaw` respects `PeriodChain.morphRel`. -/
theorem evalWellDefinedMorphRel (Q : PeriodQuadruple A B K L) (x : PeriodSym Q)
    {M N : A} (α : M ⟶ N) (σ : FreeMod B (Q.hB.dim M)) (ω : FreeModDual K (Q.hD.dim N)) :
    evalRaw Q (PeriodSym.add x (PeriodSym.sym M σ (dualMap (Q.hD.map α) ω)))
      = evalRaw Q (PeriodSym.add x (PeriodSym.sym N ((Q.hB.map α).toFun σ) ω)) :=
  Eq.trans (evalRawAdd Q x (PeriodSym.sym M σ (dualMap (Q.hD.map α) ω)))
    (Eq.trans (congrArg (fun w => evalRaw Q x + w)
        (evalRawSym Q M σ (dualMap (Q.hD.map α) ω)))
      (Eq.trans (congrArg (fun w => evalRaw Q x + w) (evalSymMorph Q α σ ω))
        (Eq.trans (congrArg (fun w => evalRaw Q x + w)
            (evalRawSym Q N ((Q.hB.map α).toFun σ) ω)).symm
          (evalRawAdd Q x (PeriodSym.sym N ((Q.hB.map α).toFun σ) ω)).symm)))

-- Reference: Hörmann, arXiv:2106.03803, Def 2.3 + Def 2.5 (eval_∫ is
-- well-defined on the quotient P(𝒜) — the main theorem of ticket P.4): the
-- raw evaluation respects every generator of the witness-carrying relation;
-- the morphism-relation case is `evalSymMorph` (naturality of `∫`), the
-- bilinearity cases are the `evalSym` linearity lemmas, and the free-module
-- cases are the module laws of `L`.  Proved by induction on the witness
-- `PeriodChain`, exactly as `tensorSymLiftRel` in
-- `BoringMath.FormalPeriods.FreeTensor`.
/-- **eval_∫ is well-defined on the quotient**: the raw evaluation respects the
witness-carrying relation, so it descends to `P(𝒜)`. -/
theorem eval_well_defined (Q : PeriodQuadruple A B K L) (x y : PeriodSym Q)
    (h : periodRel Q x y) : evalRaw Q x = evalRaw Q y := by
  obtain ⟨ch⟩ := h
  induction ch
  case refl x => exact Eq.refl _
  case symm x y ch ih => exact Eq.symm ih
  case trans x y z c₁ c₂ ih₁ ih₂ => exact Eq.trans ih₁ ih₂
  case addLeft x y z ch ih => exact evalWellDefinedAddLeft Q z x y ih
  case addRight x y z ch ih => exact evalWellDefinedAddRight Q x y z ih
  case smulC c x y hch ih => exact evalWellDefinedSmulC Q c x y ih
  case nilLeft x => exact evalWellDefinedNilLeft Q x
  case nilRight x => exact evalWellDefinedNilRight Q x
  case addAssoc x y z => exact evalWellDefinedAddAssoc Q x y z
  case addComm x y => exact evalWellDefinedAddComm Q x y
  case smulNil c => exact evalWellDefinedSmulNil Q c
  case smulAdd c x y => exact evalWellDefinedSmulAdd Q c x y
  case addSmul a b x => exact evalWellDefinedAddSmul Q a b x
  case oneSmul x => exact evalWellDefinedOneSmul Q x
  case zeroSmul x => exact evalWellDefinedZeroSmul Q x
  case smulSmul a b x => exact evalWellDefinedSmulSmul Q a b x
  case zeroSymRight x M σ => exact evalWellDefinedZeroSymRight Q x M σ
  case zeroSymLeft x M ω => exact evalWellDefinedZeroSymLeft Q x M ω
  case addSymLeft x M σ₁ σ₂ ω => exact evalWellDefinedAddSymLeft Q x M σ₁ σ₂ ω
  case addSymRight x M σ ω₁ ω₂ => exact evalWellDefinedAddSymRight Q x M σ ω₁ ω₂
  case smulSym x M σ ω c => exact evalWellDefinedSmulSym Q x M σ ω c
  case smulSymLeft x M σ ω c => exact evalWellDefinedSmulSymLeft Q x M σ ω c
  case morphRel x M N α σ ω => exact evalWellDefinedMorphRel Q x α σ ω

-- Reference: Hörmann, arXiv:2106.03803, Def 2.5 (verified against the arXiv
-- HTML, v2): `eval_∫ : P(𝒜) → ℂ` (here `L`) is the `K`-linear map
-- `(σ⊗ω)_M ↦ ∫σ ω := ω(∫_M(σ))`; Dummit–Foote, §10.4 (the lift descends to
-- the quotient); Lean 4 core, Init/Prelude.lean (`Quot.lift`).  Well-definedness
-- is `eval_well_defined`, the main theorem of ticket P.4.
/-- The evaluation map `eval_∫ : P(𝒜) → L`, descended from the raw evaluation
by `Quot.lift` (well-defined by `eval_well_defined`). -/
def eval (Q : PeriodQuadruple A B K L) : P Q → L :=
  Quot.lift (evalRaw Q) (fun x y h => eval_well_defined Q x y h)

-- Reference: mathlib, Mathlib/Data/Quot.lean (`Quot.lift_mk`, proved by `rfl`);
-- primitive definitional lemma.
/-- The lift of the raw evaluation on a class is the raw evaluation. -/
theorem evalMk (Q : PeriodQuadruple A B K L) (x : PeriodSym Q) :
    eval Q (Quot.mk (periodRel Q) x) = evalRaw Q x :=
  Quot.lift_mk (evalRaw Q) (fun x y h => eval_well_defined Q x y h) x

-- Reference: Hörmann, arXiv:2106.03803, Def 2.5 (the formula
-- `eval_∫ (σ⊗ω)_M = ω(∫_M(σ))`).
/-- The beta rule of `eval_∫`: `eval_∫ (σ⊗ω)_M = ω(∫_M(σ))`. -/
theorem evalSymMk (Q : PeriodQuadruple A B K L) (M : A) (σ : FreeMod B (Q.hB.dim M))
    (ω : FreeModDual K (Q.hD.dim M)) :
    eval Q (Quot.mk (periodRel Q) (PeriodSym.sym M σ ω)) = evalSym Q M σ ω :=
  Eq.trans (evalMk Q (PeriodSym.sym M σ ω)) (evalRawSym Q M σ ω)

/-! ## Smoke test -/

-- Reference: smoke test for the P.4 acceptance criterion (usable at concrete
-- fields; unlinted like the `ℚ` examples in `BoringMath.FormalPeriods.FreeTensor`,
-- since `Rat.instField` is choice-tainted at the pin).
/-- Smoke test: the key pairing identity `ω(φ f x) = (f∨ ω)(x)` at `K = L = ℚ`. -/
example {m n : ℕ} (f : FreeModHom ℚ m n) (ω : FreeModDual ℚ n) (x : FreeMod ℚ m) :
    pairL (RingHom.id ℚ) ω ((baseChangeHomOf (RingHom.id ℚ) f).toFun x)
      = pairL (RingHom.id ℚ) (dualMap f ω) x :=
  pairLBaseHom (RingHom.id ℚ) f ω x

/-! ## Axiom lint -/

#lint_axioms BoringMath.FormalPeriods.finSum
#lint_axioms BoringMath.FormalPeriods.listSum_congr
#lint_axioms BoringMath.FormalPeriods.listSum_map_add
#lint_axioms BoringMath.FormalPeriods.listSum_map_mul_left
#lint_axioms BoringMath.FormalPeriods.listSum_apply
#lint_axioms BoringMath.FormalPeriods.listSum_zero
#lint_axioms BoringMath.FormalPeriods.listSum_ite_zero
#lint_axioms BoringMath.FormalPeriods.listSum_ite_mem
#lint_axioms BoringMath.FormalPeriods.finSum_ite
#lint_axioms BoringMath.FormalPeriods.mapListSum
#lint_axioms BoringMath.FormalPeriods.LinearCat
#lint_axioms BoringMath.FormalPeriods.AbelianCat
#lint_axioms BoringMath.FormalPeriods.freeModHomZeroInst
#lint_axioms BoringMath.FormalPeriods.freeModHomAddInst
#lint_axioms BoringMath.FormalPeriods.freeModHomSMulKInst
#lint_axioms BoringMath.FormalPeriods.freeModHomSMulBInst
#lint_axioms BoringMath.FormalPeriods.freeModHomMapZero
#lint_axioms BoringMath.FormalPeriods.freeModEqSumSingle
#lint_axioms BoringMath.FormalPeriods.freeModHomMapListSum
#lint_axioms BoringMath.FormalPeriods.freeModHomMapSum
#lint_axioms BoringMath.FormalPeriods.precompDual
#lint_axioms BoringMath.FormalPeriods.dualMap
#lint_axioms BoringMath.FormalPeriods.dualVal
#lint_axioms BoringMath.FormalPeriods.dualValDualMap
#lint_axioms BoringMath.FormalPeriods.dualValAdd
#lint_axioms BoringMath.FormalPeriods.dualValSmul
#lint_axioms BoringMath.FormalPeriods.dualValZero
#lint_axioms BoringMath.FormalPeriods.dualValEqSum
#lint_axioms BoringMath.FormalPeriods.algBL
#lint_axioms BoringMath.FormalPeriods.baseChangeOf
#lint_axioms BoringMath.FormalPeriods.baseChangeOfAdd
#lint_axioms BoringMath.FormalPeriods.baseChangeOfSmul
#lint_axioms BoringMath.FormalPeriods.baseChangeOfZero
#lint_axioms BoringMath.FormalPeriods.baseChangeHomOfFun
#lint_axioms BoringMath.FormalPeriods.baseChangeHomOfFunAdd
#lint_axioms BoringMath.FormalPeriods.baseChangeHomOfFunSmul
#lint_axioms BoringMath.FormalPeriods.baseChangeHomOf
#lint_axioms BoringMath.FormalPeriods.baseChangeHomOfDecomp
#lint_axioms BoringMath.FormalPeriods.baseChangeHomOfApply
#lint_axioms BoringMath.FormalPeriods.pairL
#lint_axioms BoringMath.FormalPeriods.pairLAddRight
#lint_axioms BoringMath.FormalPeriods.pairLSmulRight
#lint_axioms BoringMath.FormalPeriods.pairLZeroRight
#lint_axioms BoringMath.FormalPeriods.pairLListSum
#lint_axioms BoringMath.FormalPeriods.pairLSumRight
#lint_axioms BoringMath.FormalPeriods.pairLAddLeft
#lint_axioms BoringMath.FormalPeriods.pairLSmulLeft
#lint_axioms BoringMath.FormalPeriods.pairLZeroLeft
#lint_axioms BoringMath.FormalPeriods.pairLBase
#lint_axioms BoringMath.FormalPeriods.pairLBaseHom
#lint_axioms BoringMath.FormalPeriods.IsMonoFreeModHom
#lint_axioms BoringMath.FormalPeriods.IsEpiFreeModHom
#lint_axioms BoringMath.FormalPeriods.FiberFunctor
#lint_axioms BoringMath.FormalPeriods.PeriodQuadruple
#lint_axioms BoringMath.FormalPeriods.PeriodSym
#lint_axioms BoringMath.FormalPeriods.periodSym
#lint_axioms BoringMath.FormalPeriods.PeriodChain
#lint_axioms BoringMath.FormalPeriods.periodRel
#lint_axioms BoringMath.FormalPeriods.periodRelAddLeft
#lint_axioms BoringMath.FormalPeriods.periodRelAddRight
#lint_axioms BoringMath.FormalPeriods.periodRelSmul
#lint_axioms BoringMath.FormalPeriods.P
#lint_axioms BoringMath.FormalPeriods.periodAddInst
#lint_axioms BoringMath.FormalPeriods.periodSmulOp
#lint_axioms BoringMath.FormalPeriods.periodSMulInst
#lint_axioms BoringMath.FormalPeriods.periodZeroInst
#lint_axioms BoringMath.FormalPeriods.periodAddMk
#lint_axioms BoringMath.FormalPeriods.periodSmulMk
#lint_axioms BoringMath.FormalPeriods.periodZeroMk
#lint_axioms BoringMath.FormalPeriods.isSymSumAt
#lint_axioms BoringMath.FormalPeriods.PM
#lint_axioms BoringMath.FormalPeriods.evalSym
#lint_axioms BoringMath.FormalPeriods.evalSymEq
#lint_axioms BoringMath.FormalPeriods.evalSymAddLeft
#lint_axioms BoringMath.FormalPeriods.evalSymSmulLeft
#lint_axioms BoringMath.FormalPeriods.evalSymAddRight
#lint_axioms BoringMath.FormalPeriods.evalSymSmulRight
#lint_axioms BoringMath.FormalPeriods.evalSymZeroLeft
#lint_axioms BoringMath.FormalPeriods.evalSymZeroRight
#lint_axioms BoringMath.FormalPeriods.evalSymMorph
#lint_axioms BoringMath.FormalPeriods.evalRaw
#lint_axioms BoringMath.FormalPeriods.evalRawNil
#lint_axioms BoringMath.FormalPeriods.evalRawSym
#lint_axioms BoringMath.FormalPeriods.evalRawAdd
#lint_axioms BoringMath.FormalPeriods.evalRawSmul
#lint_axioms BoringMath.FormalPeriods.eval_well_defined
#lint_axioms BoringMath.FormalPeriods.eval
#lint_axioms BoringMath.FormalPeriods.evalMk
#lint_axioms BoringMath.FormalPeriods.evalSymMk

end BoringMath.FormalPeriods








