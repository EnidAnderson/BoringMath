/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Module.Prod
import BoringMath.FormalPeriods.ExplicitLimits.Basic
import BoringMath.FormalPeriods.ExplicitLimits.Quotient

/-!
# Pushouts

Pushouts of explicit linear maps (Hörmann, arXiv:2106.03803, Prop 3.6): the
pushout object as the quotient of `U × T` by the diagonal image, the two
inclusions `poInl`/`poInr`, and the universal property `poLift`.
-/

universe u

namespace BoringMath

variable {K : Type u} [Field K]
variable {V W : Type u} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

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

end BoringMath
