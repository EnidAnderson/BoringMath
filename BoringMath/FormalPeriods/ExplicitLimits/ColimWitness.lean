/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringMath.FormalPeriods.ExplicitLimits.ColimLift

/-!
# The dies-in-colimit witness (finite chains)

The proof-relevant witness chains: `a + (-1)•a ∼ nil`, the preservation of
addition and scalar multiplication by the legs up to the relation, the
evaluation of formal sums to symbol pairs, and transitivity of `colimSymRel`
(Mac Lane, CWM 2nd ed., Ch. IX §1).
-/

universe u

namespace BoringMath

variable {K : Type u} [Field K]
variable {V W : Type u} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

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

end BoringMath
