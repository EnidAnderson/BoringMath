/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Module.Prod
import BoringMath.FormalPeriods.ExplicitLimits.Basic
import BoringMath.FormalPeriods.ExplicitLimits.Products

/-!
# Equalizers, pullbacks of monos, and images

Equalizers as kernels of `f - g` (Mac Lane, CWM 2nd ed., Ch. V §2), pullbacks
of monos as intersections (Hörmann, arXiv:2106.03803, Key Lemma 3.2), and
images (`N' := p(L')`), each as explicit data with its universal property.
-/

universe u

namespace BoringMath

variable {K : Type u} [Field K]
variable {V W : Type u} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
variable {A B C : Type u} [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
  [AddCommGroup C] [Module K C]
variable {X : Type u} [Add X] [Zero X] [SMul K X]

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

end BoringMath
