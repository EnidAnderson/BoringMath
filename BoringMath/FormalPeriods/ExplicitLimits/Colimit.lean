/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Data.Quot
import BoringMath.FormalPeriods.FreeMod
import BoringMath.FormalPeriods.ExplicitLimits.Basic

/-!
# The explicit filtered colimit: data, relation, operations, legs

A small filtered category and a diagram of basis-carrying spaces as explicit
data; the formal sums `ColimSym`, the witness chains `ColimChain`, the symbol
relation and the colimit `FilteredColim` as a quotient, its operations, and
the legs `colimLeg` (Hörmann, arXiv:2106.03803, Theorem 4.1).
-/

universe u

namespace BoringMath

variable {K : Type u} [Field K]
variable {V W : Type u} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

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

end BoringMath
