/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringMath.FormalPeriods.ExplicitLimits.Colimit

/-!
# The filtered colimit: cocones and the universal lift

`ColimCocone`, the lift of the formal sums `colimSymLift`, and the induced
`colimLift` with its universal property and uniqueness (Mac Lane, CWM 2nd
ed., Ch. III §3).
-/

universe u

namespace BoringMath

variable {K : Type u} [Field K]
variable {V W : Type u} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

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
          (Quotient.lift_mk (colimSymLift J D c)
            (fun a b h => colimSymLiftRel J D c a b h) b)).symm))

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
  Eq.subst (motive := fun t => k t = colimSymLift J D c (ColimSym.sym i x))
    (colimLeg_apply J D i x) (hk i x)

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

end BoringMath
