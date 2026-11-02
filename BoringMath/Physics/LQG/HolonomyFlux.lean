/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringMath.Physics.LQG.SpinNetwork
import Mathlib.Algebra.BigOperators.Group.List.Lemmas

/-!
# The holonomy algebra on a finite graph — PHYS.LQG.0 (#352, items 7–9)

The algebraic core of LQG's kinematics: on a finite graph, a (lattice)
connection is an assignment of a group element to each edge, and the
**holonomy along a signed path** is the ordered product of the edge group
elements (inverted on reversed edges). The composition law
`pathHolonomy_append` — holonomy along a concatenated path is the product of
the holonomies — is proved outright. Cylinder functions (functions of the
connection depending on finitely many edges) form a commutative algebra, and
pullback along an edge map is an algebra homomorphism, both proved.

## References
* A. Ashtekar, J. Lewandowski, "Background independent quantum gravity: A
  status report", Class. Quantum Grav. 21 (2004) R53, gr-qc/0404018, §II —
  holonomies and cylinder functions. REVIEW(citation): pin the section.
* C. Rovelli, *Quantum Gravity*, CUP 2004, ch. 5 — holonomy-flux algebra.
  REVIEW(citation): pin the chapter section.
* Program register: BoringMath #352 (PHYS.LQG.0), items 7–9.
-/

namespace BoringMath

variable {ι ι' G R : Type*} [Group G] [CommRing R] [DecidableEq ι]

-- Reference: [Ashtekar–Lewandowski 2004] §II — a signed edge: an edge with an
-- orientation sign (`true` = along the edge, `false` = against).
/-- A **signed edge**: an edge index paired with an orientation. -/
abbrev SignedEdge (ι : Type*) := ι × Bool

-- Reference: [Rovelli 2004] ch. 5 — on a finite graph a connection is just an
-- assignment of a group element per edge (the lattice connection); no
-- choice-backed data.
/-- The **holonomy of a single edge** under the connection `c`. -/
def holonomyOf {ι G : Type*} [Group G] (c : ι → G) (e : ι) : G := c e

-- Reference: projection law (STYLE §5): peeled into its own named lemma.
/-- **Projection law**: the edge holonomy is the assigned group element. -/
theorem holonomyOf_eq {ι G : Type*} [Group G] (c : ι → G) (e : ι) :
    holonomyOf c e = c e := rfl

-- Reference: [Ashtekar–Lewandowski 2004] §II — the holonomy along a signed
-- path is the ordered product of edge holonomies (inverted when reversed).
/-- The **holonomy along a signed path**: the ordered product of the edge
group elements, inverted on edges traversed against their orientation. -/
def pathHolonomy {ι G : Type*} [Group G] (c : ι → G) : List (SignedEdge ι) → G
  | [] => 1
  | (e, b) :: p => (if b then holonomyOf c e else (holonomyOf c e)⁻¹) * pathHolonomy c p

-- Reference: [Ashtekar–Lewandowski 2004] §II — the empty path has trivial
-- holonomy.
/-- **The empty path has trivial holonomy**. -/
theorem pathHolonomy_nil {ι G : Type*} [Group G] (c : ι → G) :
    pathHolonomy c [] = 1 := rfl

-- Reference: [Ashtekar–Lewandowski 2004] §II — a single signed edge.
/-- **A single-edge path** has the edge's holonomy (inverted if reversed). -/
theorem pathHolonomy_singleton {ι G : Type*} [Group G] (c : ι → G) (e : ι) (b : Bool) :
    pathHolonomy c [(e, b)] = if b then holonomyOf c e else (holonomyOf c e)⁻¹ :=
  mul_one _

-- Reference: [Ashtekar–Lewandowski 2004] §II — the composition law: holonomy
-- along a concatenated path is the product of the holonomies (path-ordered).
/-- **The holonomy composition law**: holonomy along `p ++ q` is the product
of the holonomies along `p` and `q`. -/
theorem pathHolonomy_append {ι G : Type*} [Group G] (c : ι → G)
    (p q : List (SignedEdge ι)) :
    pathHolonomy c (p ++ q) = pathHolonomy c p * pathHolonomy c q := by
  induction p with
  | nil => exact (one_mul (pathHolonomy c q)).symm
  | cons a p ih =>
      exact Eq.trans
        (congrArg (fun z => (if a.2 then holonomyOf c a.1 else (holonomyOf c a.1)⁻¹) * z) ih)
        (mul_assoc _ _ _).symm

-- Reference: [Ashtekar–Lewandowski 2004] §II — cylinder functions are the
-- functions of the connection that depend on finitely many edges.
/-- A function `f` of the connection **depends on the edge set `s`** when
connections agreeing on `s` have equal values. -/
def dependsOn {ι G R : Type*} [DecidableEq ι] (s : Finset ι) (f : (ι → G) → R) : Prop :=
  ∀ c c' : ι → G, (∀ e ∈ s, c e = c' e) → f c = f c'

-- Reference: [Ashtekar–Lewandowski 2004] §II — on a finite graph every
-- function is cylindrical (depends on all edges, i.e. the whole connection).
/-- **On a finite graph every function depends on all edges**. -/
theorem dependsOn_univ {ι G R : Type*} [DecidableEq ι] [Fintype ι] (f : (ι → G) → R) :
    dependsOn (Finset.univ : Finset ι) f :=
  fun _c _c' h => congrArg f (funext fun e => h e (Finset.mem_univ e))

-- Reference: [Ashtekar–Lewandowski 2004] §II — enlarging the edge set weakens
-- the dependence condition.
/-- **Dependence is monotone**: if `f` depends on `t` and `t ⊆ s`, then `f`
depends on `s`. -/
theorem dependsOn_mono {ι G R : Type*} [DecidableEq ι] {s t : Finset ι}
    (h : t ⊆ s) {f : (ι → G) → R} (hd : dependsOn t f) : dependsOn s f :=
  fun c c' hc => hd c c' (fun e he => hc e (h he))

-- Reference: [Ashtekar–Lewandowski 2004] §II — the pullback of a cylinder
-- function along an edge map `φ` is the function on the smaller graph.
/-- The **pullback** of a function of connections along an edge map `φ`. -/
def pullback {ι ι' G R : Type*} (φ : ι' → ι) (f : (ι' → G) → R) : (ι → G) → R :=
  fun c => f fun e' => c (φ e')

-- Reference: projection laws for the pointwise algebra on cylinder functions
-- (STYLE §5): peeled into named lemmas.
/-- **Projection law**: pointwise multiplication of cylinder functions. -/
theorem cylinder_mul_apply {ι G R : Type*} [CommRing R] (f g : (ι → G) → R) (c : ι → G) :
    (f * g) c = f c * g c := Pi.mul_apply f g c

/-- **Projection law**: the constant-one cylinder function. -/
theorem cylinder_one_apply {ι G R : Type*} [CommRing R] (c : ι → G) :
    (1 : (ι → G) → R) c = 1 := Pi.one_apply c

-- Reference: [Ashtekar–Lewandowski 2004] §II — pullback is an algebra
-- homomorphism: it preserves multiplication and one.
/-- **Pullback preserves multiplication**. -/
theorem pullback_mul {ι ι' G R : Type*} [CommRing R] (φ : ι' → ι) (f g : (ι' → G) → R) :
    pullback φ (f * g) = pullback φ f * pullback φ g :=
  funext fun c => cylinder_mul_apply (pullback φ f) (pullback φ g) c

-- Reference: [Ashtekar–Lewandowski 2004] §II — pullback preserves one.
/-- **Pullback preserves one**. -/
theorem pullback_one {ι ι' G R : Type*} [CommRing R] (φ : ι' → ι) :
    pullback φ (1 : (ι' → G) → R) = 1 :=
  funext fun c => cylinder_one_apply c

-- Reference: [Ashtekar–Lewandowski 2004] §II — pullback composes contravariantly.
/-- **Pullback is contravariant**: pulling back along `φ` then `ψ` is pulling
back along `φ ∘ ψ`. -/
theorem pullback_comp {ι ι' ι'' G R : Type*} [CommRing R] (φ : ι' → ι) (ψ : ι → ι'')
    (f : (ι' → G) → R) :
    pullback ψ (pullback φ f) = pullback (fun e' => ψ (φ e')) f := rfl

-- Reference: [Ashtekar–Lewandowski 2004] §II — cylinder functions on `s` form
-- a commutative algebra: the subtype of functions depending on `s`, with the
-- pointwise operations.
/-- **Cylinder functions on the edge set `s`**: functions of the connection
depending only on the edges in `s` (a subtype of `(ι → G) → R`). -/
def CylinderFun (ι G R : Type*) [DecidableEq ι] [CommRing R] (s : Finset ι) :=
  {f : (ι → G) → R // dependsOn s f}

-- Reference: [Ashtekar–Lewandowski 2004] §II — closure of `dependsOn` under
-- the pointwise operations; each op is transported along `Subtype.val`.
/-- The zero cylinder function depends on `s`. -/
instance cylinderFunZero {ι G R : Type*} [DecidableEq ι] [CommRing R] (s : Finset ι) :
    Zero (CylinderFun ι G R s) :=
  ⟨⟨0, fun c c' _ =>
    (Pi.zero_apply (M := fun _ : (ι → G) => R) c).trans
      (Pi.zero_apply (M := fun _ : (ι → G) => R) c').symm⟩⟩

-- Reference: [Ashtekar–Lewandowski 2004] §II — same closure for the unit.
/-- The one cylinder function depends on `s`. -/
instance cylinderFunOne {ι G R : Type*} [DecidableEq ι] [CommRing R] (s : Finset ι) :
    One (CylinderFun ι G R s) :=
  ⟨⟨1, fun c c' _ => (cylinder_one_apply c).trans (cylinder_one_apply c').symm⟩⟩

-- Reference: [Ashtekar–Lewandowski 2004] §II — same closure for addition.
/-- The sum of two cylinder functions on `s` depends on `s`. -/
instance cylinderFunAdd {ι G R : Type*} [DecidableEq ι] [CommRing R] (s : Finset ι) :
    Add (CylinderFun ι G R s) :=
  ⟨fun f g => ⟨f.1 + g.1, fun c c' h =>
    Eq.trans (Pi.add_apply f.1 g.1 c)
      (Eq.trans (congrArg₂ (· + ·) (f.2 c c' h) (g.2 c c' h))
        (Pi.add_apply f.1 g.1 c').symm)⟩⟩

-- Reference: [Ashtekar–Lewandowski 2004] §II — same closure for multiplication.
/-- The product of two cylinder functions on `s` depends on `s`. -/
instance cylinderFunMul {ι G R : Type*} [DecidableEq ι] [CommRing R] (s : Finset ι) :
    Mul (CylinderFun ι G R s) :=
  ⟨fun f g => ⟨f.1 * g.1, fun c c' h =>
    Eq.trans (Pi.mul_apply f.1 g.1 c)
      (Eq.trans (congrArg₂ (· * ·) (f.2 c c' h) (g.2 c c' h))
        (Pi.mul_apply f.1 g.1 c').symm)⟩⟩

-- Reference: [Ashtekar–Lewandowski 2004] §II — same closure for negation.
/-- The negation of a cylinder function on `s` depends on `s`. -/
instance cylinderFunNeg {ι G R : Type*} [DecidableEq ι] [CommRing R] (s : Finset ι) :
    Neg (CylinderFun ι G R s) :=
  ⟨fun f => ⟨-f.1, fun c c' h =>
    Eq.trans (Pi.neg_apply f.1 c)
      (Eq.trans (congrArg Neg.neg (f.2 c c' h)) (Pi.neg_apply f.1 c').symm)⟩⟩

-- Reference: [Ashtekar–Lewandowski 2004] §II — same closure for subtraction.
/-- The difference of two cylinder functions on `s` depends on `s`. -/
instance cylinderFunSub {ι G R : Type*} [DecidableEq ι] [CommRing R] (s : Finset ι) :
    Sub (CylinderFun ι G R s) :=
  ⟨fun f g => ⟨f.1 - g.1, fun c c' h =>
    Eq.trans (Pi.sub_apply f.1 g.1 c)
      (Eq.trans (congrArg₂ (· - ·) (f.2 c c' h) (g.2 c c' h))
        (Pi.sub_apply f.1 g.1 c').symm)⟩⟩

-- Reference: [Ashtekar–Lewandowski 2004] §II — same closure for `ℕ`-multiples.
/-- The `ℕ`-multiple of a cylinder function on `s` depends on `s`. -/
instance cylinderFunNSMul {ι G R : Type*} [DecidableEq ι] [CommRing R] (s : Finset ι) :
    SMul ℕ (CylinderFun ι G R s) :=
  ⟨fun n f => ⟨n • f.1, fun c c' h => congrArg (n • ·) (f.2 c c' h)⟩⟩

-- Reference: [Ashtekar–Lewandowski 2004] §II — same closure for `ℤ`-multiples.
/-- The `ℤ`-multiple of a cylinder function on `s` depends on `s`. -/
instance cylinderFunZSMul {ι G R : Type*} [DecidableEq ι] [CommRing R] (s : Finset ι) :
    SMul ℤ (CylinderFun ι G R s) :=
  ⟨fun n f => ⟨n • f.1, fun c c' h => congrArg (n • ·) (f.2 c c' h)⟩⟩

-- Reference: [Ashtekar–Lewandowski 2004] §II — same closure for powers.
/-- The power of a cylinder function on `s` depends on `s`. -/
instance cylinderFunPow {ι G R : Type*} [DecidableEq ι] [CommRing R] (s : Finset ι) :
    Pow (CylinderFun ι G R s) ℕ :=
  ⟨fun f n => ⟨f.1 ^ n, fun c c' h => congrArg (· ^ n) (f.2 c c' h)⟩⟩

-- Reference: [Ashtekar–Lewandowski 2004] §II — same closure for the natural cast.
/-- The natural cast of a cylinder function on `s` depends on `s`. -/
instance cylinderFunNatCast {ι G R : Type*} [DecidableEq ι] [CommRing R] (s : Finset ι) :
    NatCast (CylinderFun ι G R s) :=
  ⟨fun n => ⟨((n : ℕ) : (ι → G) → R), fun c c' _ =>
    (Pi.natCast_apply (π := fun _ : (ι → G) => R) n c).trans
      (Pi.natCast_apply (π := fun _ : (ι → G) => R) n c').symm⟩⟩

-- Reference: [Ashtekar–Lewandowski 2004] §II — same closure for the integer cast.
/-- The integer cast of a cylinder function on `s` depends on `s`. -/
instance cylinderFunIntCast {ι G R : Type*} [DecidableEq ι] [CommRing R] (s : Finset ι) :
    IntCast (CylinderFun ι G R s) :=
  ⟨fun n => ⟨((n : ℤ) : (ι → G) → R), fun c c' _ =>
    (Pi.intCast_apply (π := fun _ : (ι → G) => R) n c).trans
      (Pi.intCast_apply (π := fun _ : (ι → G) => R) n c').symm⟩⟩

-- Reference: [Ashtekar–Lewandowski 2004] §II — the transported pointwise
-- operations make the cylinder functions a commutative ring.
/-- **Cylinder functions on `s` form a commutative ring** (pointwise
operations, transported along the subtype inclusion). -/
instance cylinderFunCommRing {ι G R : Type*} [DecidableEq ι] [CommRing R] (s : Finset ι) :
    CommRing (CylinderFun ι G R s) :=
  Function.Injective.commRing Subtype.val Subtype.val_injective rfl rfl
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)

-- Reference: [Ashtekar–Lewandowski 2004] §II — the pullback of a cylinder
-- function on `t` depends on the image `t.image φ`.
/-- **Pullback preserves cylindrical dependence**: if `f` depends on `t`, then
`pullback φ f` depends on `t.image φ` (proved). -/
theorem dependsOn_pullback {ι ι' G R : Type*} [DecidableEq ι] [DecidableEq ι'] [CommRing R]
    {t : Finset ι'} {f : (ι' → G) → R} (hd : dependsOn t f) (φ : ι' → ι) :
    dependsOn (t.image φ) (pullback φ f) :=
  fun c c' h => hd (fun e' => c (φ e')) (fun e' => c' (φ e'))
    (fun e he => h (φ e) (Finset.mem_image.mpr ⟨e, he, rfl⟩))

-- Reference: [Ashtekar–Lewandowski 2004] §II — pullback is a ring homomorphism
-- between the cylinder algebras.
/-- **Pullback is a ring homomorphism** of cylinder algebras
`CylinderFun ι' G R t →+* CylinderFun ι G R (t.image φ)` (proved). -/
def pullbackRingHom {ι ι' G R : Type*} [DecidableEq ι] [DecidableEq ι'] [CommRing R]
    (φ : ι' → ι) (t : Finset ι') :
    CylinderFun ι' G R t →+* CylinderFun ι G R (t.image φ) where
  toFun f := ⟨pullback φ f.1, dependsOn_pullback f.2 φ⟩
  map_one' := Subtype.ext (pullback_one φ)
  map_zero' := Subtype.ext (funext fun c =>
    Pi.zero_apply (M := fun _ : (ι → G) => R) c)
  map_mul' x y := Subtype.ext (pullback_mul φ x.1 y.1)
  map_add' x y := Subtype.ext (funext fun c =>
    (Pi.add_apply (pullback φ x.1) (pullback φ y.1) c).symm)

end BoringMath
