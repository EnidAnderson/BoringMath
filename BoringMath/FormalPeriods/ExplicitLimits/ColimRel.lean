/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringMath.FormalPeriods.ExplicitLimits.ColimWitness

/-!
# Compatibility of the symbol relation with the operations

The symbol relation `colimSymRel` is compatible with addition, scalar
multiplication, and the empty sum — the elementwise description of filtered
colimits (Mac Lane, CWM 2nd ed., Ch. IX §1, p. 211).
-/

universe u

namespace BoringMath

variable {K : Type u} [Field K]
variable {V W : Type u} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

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



end BoringMath
