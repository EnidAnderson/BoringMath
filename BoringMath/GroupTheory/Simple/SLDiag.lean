/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringMath.GroupTheory.Simple.SLTransvection
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# Diagonals are products of transvections — step (2) of `SL_isPerfect` (#394)

For `i ≠ j` and `0 ≠ u`, the Weyl element `w_ij(u) = T_ij(u) T_ji(-u⁻¹) T_ij(u)`
and `h_ij(u) = w_ij(u) w_ij(-1) = diag2n(i,j,u)`. Hence every `diag2n` is a
product of transvections, so in rank `≥ 3` (where transvections are commutators,
`SLTransvection.lean`) every `diag2n` lies in the commutator subgroup.

The torus identity `hOf_eq_diag2n` is proved through the action on the standard
basis: `w_ij(u)` sends `e_i ↦ -u⁻¹ e_j`, `e_j ↦ u e_i` and fixes the other
`e_l` (`wOf_smul_single_fst/snd/other`), so `h_ij(u)` acts diagonally with `u`
on `e_i`, `u⁻¹` on `e_j` — exactly `diag2n` (`diag2n_smul_single`).

## References
* [Carter] ch. 5; [Steinberg], *Lectures on Chevalley Groups* (the h_ij/w_ij
  identities).
* mathlib pin v4.35.0-rc3: `SpecialLinearGroup.diag2n`, `diag2n_coe`,
  `transvection`, `transvection_smul_single_fst/snd`, `Matrix.diagonal_mulVec_single`,
  `Pi.single_smul'`, `diagonal_transvection_induction'`.
-/

namespace BoringMath

open Matrix
open scoped commutatorElement

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {F : Type*} [Field F]

-- Reference: mathlib pin v4.35.0-rc3, `add_assoc`, `add_comm`, `add_neg_cancel`,
-- `add_zero`.
/-- Cancellation in the middle: `a + (b + -a) = b`. -/
theorem add_add_neg_cancel_right {V : Type*} [AddCommGroup V] (a b : V) : a + (b + -a) = b :=
  (add_assoc a b (-a)).symm.trans
    ((congrArg (fun w => w + -a) (add_comm a b)).trans
      ((add_assoc b a (-a)).trans
        ((congrArg (fun w => b + w) (add_neg_cancel a)).trans (add_zero b))))

-- Reference: [Steinberg] (the Weyl element as a product of transvections).
/-- The Weyl element `w_ij(u)` as a product of three transvections. -/
def wOf {i j : ι} (hij : i ≠ j) (u : F) (_hu : u ≠ 0) : SpecialLinearGroup ι F :=
  SpecialLinearGroup.transvection hij u *
    SpecialLinearGroup.transvection (Ne.symm hij) (-u⁻¹) *
      SpecialLinearGroup.transvection hij u

-- Reference: [Steinberg] (h_ij(u) = w_ij(u) w_ij(-1) = diag(u, u⁻¹) in the (i,j) block).
/-- The torus element `h_ij(u) = w_ij(u) w_ij(-1)`. -/
def hOf {i j : ι} (hij : i ≠ j) (u : F) (hu : u ≠ 0) : SpecialLinearGroup ι F :=
  wOf hij u hu * wOf hij (-1) (neg_ne_zero.mpr one_ne_zero)

/-! ## Action of the Weyl element on the standard basis -/

-- Reference: mathlib pin v4.35.0-rc3, `mul_smul` (the `DistribMulAction` instance
-- on `ι → F`); [Steinberg].
/-- The triple product defining `wOf` acts step by step. -/
theorem wOf_smul {i j : ι} (hij : i ≠ j) (u : F) (hu : u ≠ 0) (v : ι → F) :
    wOf hij u hu • v
      = SpecialLinearGroup.transvection hij u •
        (SpecialLinearGroup.transvection (Ne.symm hij) (-u⁻¹) •
          (SpecialLinearGroup.transvection hij u • v)) :=
  (mul_smul (SpecialLinearGroup.transvection hij u *
      SpecialLinearGroup.transvection (Ne.symm hij) (-u⁻¹))
    (SpecialLinearGroup.transvection hij u) v).trans
    (mul_smul (SpecialLinearGroup.transvection hij u)
      (SpecialLinearGroup.transvection (Ne.symm hij) (-u⁻¹))
      (SpecialLinearGroup.transvection hij u • v))

-- Reference: mathlib pin v4.35.0-rc3, `transvection_smul_single_fst/snd`,
-- `smul_add`, `smul_comm`, `smul_smul`, `inv_mul_cancel₀`; [Steinberg]
-- (`w_ij(u)` sends `e_i ↦ -u⁻¹ e_j`).
/-- The Weyl element `w_ij(u)` sends `e_i` to `-u⁻¹ • e_j`. -/
theorem wOf_smul_single_fst {i j : ι} (hij : i ≠ j) (u : F) (hu : u ≠ 0) :
    wOf hij u hu • (Pi.single i (1 : F) : ι → F)
      = (-u⁻¹) • (Pi.single j (1 : F) : ι → F) := by
  have hneg : (-u⁻¹) * u = (-1 : F) :=
    (neg_mul u⁻¹ u).trans (congrArg (fun x : F => -x) (inv_mul_cancel₀ hu))
  have h3 := SpecialLinearGroup.transvection_smul_single_fst hij u
  have h2 := SpecialLinearGroup.transvection_smul_single_snd (Ne.symm hij) (-u⁻¹)
  have h1 := SpecialLinearGroup.transvection_smul_single_snd hij u
  have hcancel : (Pi.single i (1 : F) : ι → F) +
        ((-u⁻¹) • (Pi.single j (1 : F) : ι → F) + (-(Pi.single i (1 : F) : ι → F)))
      = (-u⁻¹) • (Pi.single j (1 : F) : ι → F) :=
    add_add_neg_cancel_right _ _
  calc wOf hij u hu • (Pi.single i (1 : F) : ι → F)
      = SpecialLinearGroup.transvection hij u •
          (SpecialLinearGroup.transvection (Ne.symm hij) (-u⁻¹) •
            (SpecialLinearGroup.transvection hij u • (Pi.single i (1 : F) : ι → F))) :=
        wOf_smul hij u hu _
    _ = SpecialLinearGroup.transvection hij u •
          (SpecialLinearGroup.transvection (Ne.symm hij) (-u⁻¹) •
            (Pi.single i (1 : F) : ι → F)) :=
        congrArg (fun v => SpecialLinearGroup.transvection hij u •
          (SpecialLinearGroup.transvection (Ne.symm hij) (-u⁻¹) • v)) h3
    _ = SpecialLinearGroup.transvection hij u •
          ((Pi.single i (1 : F) : ι → F) + (-u⁻¹) • (Pi.single j (1 : F) : ι → F)) :=
        congrArg (fun v => SpecialLinearGroup.transvection hij u • v) h2
    _ = (SpecialLinearGroup.transvection hij u • (Pi.single i (1 : F) : ι → F))
          + SpecialLinearGroup.transvection hij u •
            ((-u⁻¹) • (Pi.single j (1 : F) : ι → F)) := smul_add _ _ _
    _ = (Pi.single i (1 : F) : ι → F) + SpecialLinearGroup.transvection hij u •
            ((-u⁻¹) • (Pi.single j (1 : F) : ι → F)) :=
        congrArg (fun v => v + SpecialLinearGroup.transvection hij u •
          ((-u⁻¹) • (Pi.single j (1 : F) : ι → F))) h3
    _ = (Pi.single i (1 : F) : ι → F) +
          (-u⁻¹) • (SpecialLinearGroup.transvection hij u • (Pi.single j (1 : F) : ι → F)) :=
        congrArg (fun v => (Pi.single i (1 : F) : ι → F) + v) (smul_comm _ (-u⁻¹) _)
    _ = (Pi.single i (1 : F) : ι → F) +
          (-u⁻¹) • ((Pi.single j (1 : F) : ι → F) + u • (Pi.single i (1 : F) : ι → F)) :=
        congrArg (fun v => (Pi.single i (1 : F) : ι → F) + (-u⁻¹) • v) h1
    _ = (Pi.single i (1 : F) : ι → F) +
          ((-u⁻¹) • (Pi.single j (1 : F) : ι → F)
            + (-u⁻¹) • (u • (Pi.single i (1 : F) : ι → F))) :=
        congrArg (fun v => (Pi.single i (1 : F) : ι → F) + v)
          (smul_add (-u⁻¹) (Pi.single j (1 : F) : ι → F) (u • (Pi.single i (1 : F) : ι → F)))
    _ = (Pi.single i (1 : F) : ι → F) +
          ((-u⁻¹) • (Pi.single j (1 : F) : ι → F)
            + ((-u⁻¹) * u) • (Pi.single i (1 : F) : ι → F)) :=
        congrArg (fun v => (Pi.single i (1 : F) : ι → F) +
          ((-u⁻¹) • (Pi.single j (1 : F) : ι → F) + v)) (smul_smul (-u⁻¹) u _)
    _ = (Pi.single i (1 : F) : ι → F) +
          ((-u⁻¹) • (Pi.single j (1 : F) : ι → F)
            + (-1) • (Pi.single i (1 : F) : ι → F)) :=
        congrArg (fun v => (Pi.single i (1 : F) : ι → F) +
          ((-u⁻¹) • (Pi.single j (1 : F) : ι → F) + v))
          (congrArg (fun x : F => x • (Pi.single i (1 : F) : ι → F)) hneg)
    _ = (Pi.single i (1 : F) : ι → F) +
          ((-u⁻¹) • (Pi.single j (1 : F) : ι → F) + (-(Pi.single i (1 : F) : ι → F))) :=
        congrArg (fun v => (Pi.single i (1 : F) : ι → F) +
          ((-u⁻¹) • (Pi.single j (1 : F) : ι → F) + v)) (neg_one_smul F _)
    _ = (-u⁻¹) • (Pi.single j (1 : F) : ι → F) :=
        hcancel

-- Reference: as `wOf_smul_single_fst`, with `mul_inv_cancel₀`; [Steinberg]
-- (`w_ij(u)` sends `e_j ↦ u e_i`).
/-- The Weyl element `w_ij(u)` sends `e_j` to `u • e_i`. -/
theorem wOf_smul_single_snd {i j : ι} (hij : i ≠ j) (u : F) (hu : u ≠ 0) :
    wOf hij u hu • (Pi.single j (1 : F) : ι → F)
      = u • (Pi.single i (1 : F) : ι → F) := by
  have hneg : u * (-u⁻¹) = (-1 : F) :=
    (mul_neg u u⁻¹).trans (congrArg (fun x : F => -x) (mul_inv_cancel₀ hu))
  have h3 := SpecialLinearGroup.transvection_smul_single_snd hij u
  have h2fst := SpecialLinearGroup.transvection_smul_single_fst (Ne.symm hij) (-u⁻¹)
  have h2snd := SpecialLinearGroup.transvection_smul_single_snd (Ne.symm hij) (-u⁻¹)
  have h1fst := SpecialLinearGroup.transvection_smul_single_fst hij u
  have hcancel : (Pi.single j (1 : F) : ι → F) +
        (u • (Pi.single i (1 : F) : ι → F) + (-(Pi.single j (1 : F) : ι → F)))
      = u • (Pi.single i (1 : F) : ι → F) :=
    add_add_neg_cancel_right _ _
  calc wOf hij u hu • (Pi.single j (1 : F) : ι → F)
      = SpecialLinearGroup.transvection hij u •
          (SpecialLinearGroup.transvection (Ne.symm hij) (-u⁻¹) •
            (SpecialLinearGroup.transvection hij u • (Pi.single j (1 : F) : ι → F))) :=
        wOf_smul hij u hu _
    _ = SpecialLinearGroup.transvection hij u •
          (SpecialLinearGroup.transvection (Ne.symm hij) (-u⁻¹) •
            ((Pi.single j (1 : F) : ι → F) + u • (Pi.single i (1 : F) : ι → F))) :=
        congrArg (fun v => SpecialLinearGroup.transvection hij u •
          (SpecialLinearGroup.transvection (Ne.symm hij) (-u⁻¹) • v)) h3
    _ = SpecialLinearGroup.transvection hij u •
          (SpecialLinearGroup.transvection (Ne.symm hij) (-u⁻¹) • (Pi.single j (1 : F) : ι → F)
            + SpecialLinearGroup.transvection (Ne.symm hij) (-u⁻¹) •
              (u • (Pi.single i (1 : F) : ι → F))) :=
        congrArg (fun v => SpecialLinearGroup.transvection hij u • v)
          (smul_add (SpecialLinearGroup.transvection (Ne.symm hij) (-u⁻¹))
            (Pi.single j (1 : F) : ι → F) (u • (Pi.single i (1 : F) : ι → F)))
    _ = SpecialLinearGroup.transvection hij u •
          ((Pi.single j (1 : F) : ι → F)
            + SpecialLinearGroup.transvection (Ne.symm hij) (-u⁻¹) •
              (u • (Pi.single i (1 : F) : ι → F))) :=
        congrArg (fun v => SpecialLinearGroup.transvection hij u •
          (v + SpecialLinearGroup.transvection (Ne.symm hij) (-u⁻¹) •
            (u • (Pi.single i (1 : F) : ι → F)))) h2fst
    _ = SpecialLinearGroup.transvection hij u •
          ((Pi.single j (1 : F) : ι → F)
            + u • (SpecialLinearGroup.transvection (Ne.symm hij) (-u⁻¹) •
              (Pi.single i (1 : F) : ι → F))) :=
        congrArg (fun v => SpecialLinearGroup.transvection hij u •
          ((Pi.single j (1 : F) : ι → F) + v)) (smul_comm _ u _)
    _ = SpecialLinearGroup.transvection hij u •
          ((Pi.single j (1 : F) : ι → F)
            + u • ((Pi.single i (1 : F) : ι → F) + (-u⁻¹) • (Pi.single j (1 : F) : ι → F))) :=
        congrArg (fun v => SpecialLinearGroup.transvection hij u •
          ((Pi.single j (1 : F) : ι → F) + u • v)) h2snd
    _ = SpecialLinearGroup.transvection hij u •
          ((Pi.single j (1 : F) : ι → F)
            + (u • (Pi.single i (1 : F) : ι → F)
              + u • ((-u⁻¹) • (Pi.single j (1 : F) : ι → F)))) :=
        congrArg (fun v => SpecialLinearGroup.transvection hij u •
          ((Pi.single j (1 : F) : ι → F) + v))
          (smul_add u (Pi.single i (1 : F) : ι → F) ((-u⁻¹) • (Pi.single j (1 : F) : ι → F)))
    _ = SpecialLinearGroup.transvection hij u •
          ((Pi.single j (1 : F) : ι → F)
            + (u • (Pi.single i (1 : F) : ι → F)
              + (u * (-u⁻¹)) • (Pi.single j (1 : F) : ι → F))) :=
        congrArg (fun v => SpecialLinearGroup.transvection hij u •
          ((Pi.single j (1 : F) : ι → F) + (u • (Pi.single i (1 : F) : ι → F) + v)))
          (smul_smul u (-u⁻¹) _)
    _ = SpecialLinearGroup.transvection hij u •
          ((Pi.single j (1 : F) : ι → F)
            + (u • (Pi.single i (1 : F) : ι → F)
              + (-1) • (Pi.single j (1 : F) : ι → F))) :=
        congrArg (fun v => SpecialLinearGroup.transvection hij u •
          ((Pi.single j (1 : F) : ι → F) + (u • (Pi.single i (1 : F) : ι → F) + v)))
          (congrArg (fun x : F => x • (Pi.single j (1 : F) : ι → F)) hneg)
    _ = SpecialLinearGroup.transvection hij u •
          ((Pi.single j (1 : F) : ι → F)
            + (u • (Pi.single i (1 : F) : ι → F) + (-(Pi.single j (1 : F) : ι → F)))) :=
        congrArg (fun v => SpecialLinearGroup.transvection hij u •
          ((Pi.single j (1 : F) : ι → F) + (u • (Pi.single i (1 : F) : ι → F) + v)))
          (neg_one_smul F _)
    _ = SpecialLinearGroup.transvection hij u • (u • (Pi.single i (1 : F) : ι → F)) :=
        congrArg (fun v => SpecialLinearGroup.transvection hij u • v)
          hcancel
    _ = u • (SpecialLinearGroup.transvection hij u • (Pi.single i (1 : F) : ι → F)) :=
        smul_comm _ u _
    _ = u • (Pi.single i (1 : F) : ι → F) := congrArg (fun v => u • v) h1fst

-- Reference: `transvection_smul_single_other` (SLTransvection.lean, pin-based);
-- [Steinberg] (`w_ij(u)` fixes `e_l` for `l ∉ {i, j}`).
/-- The Weyl element `w_ij(u)` fixes the basis vector `e_l` for `l ∉ {i, j}`. -/
theorem wOf_smul_single_other {i j l : ι} (hij : i ≠ j) (u : F) (hu : u ≠ 0)
    (hli : l ≠ i) (hlj : l ≠ j) :
    wOf hij u hu • (Pi.single l (1 : F) : ι → F) = (Pi.single l (1 : F) : ι → F) := by
  have h3 := transvection_smul_single_other hij u hlj
  have h2 := transvection_smul_single_other (Ne.symm hij) (-u⁻¹) hli
  calc wOf hij u hu • (Pi.single l (1 : F) : ι → F)
      = SpecialLinearGroup.transvection hij u •
          (SpecialLinearGroup.transvection (Ne.symm hij) (-u⁻¹) •
            (SpecialLinearGroup.transvection hij u • (Pi.single l (1 : F) : ι → F))) :=
        wOf_smul hij u hu _
    _ = SpecialLinearGroup.transvection hij u •
          (SpecialLinearGroup.transvection (Ne.symm hij) (-u⁻¹) •
            (Pi.single l (1 : F) : ι → F)) :=
        congrArg (fun v => SpecialLinearGroup.transvection hij u •
          (SpecialLinearGroup.transvection (Ne.symm hij) (-u⁻¹) • v)) h3
    _ = SpecialLinearGroup.transvection hij u • (Pi.single l (1 : F) : ι → F) :=
        congrArg (fun v => SpecialLinearGroup.transvection hij u • v) h2
    _ = (Pi.single l (1 : F) : ι → F) := h3

-- Reference: mathlib pin v4.35.0-rc3, `SpecialLinearGroup.diag2n_coe`,
-- `Matrix.diagonal_mulVec_single`, `Pi.single_smul'`, `smul_eq_mul`, `mul_one`.
/-- The diagonal element `diag2n(i, j, a)` acts on `e_l` by the scalar
`if l = i then a else if l = j then a⁻¹ else 1`. -/
theorem diag2n_smul_single {i j l : ι} (hij : i ≠ j) (a : F) (ha : a ≠ 0) :
    SpecialLinearGroup.diag2n hij a ha • (Pi.single l (1 : F) : ι → F)
      = (if l = i then a else if l = j then a⁻¹ else 1) • (Pi.single l (1 : F) : ι → F) := by
  have h1 : (SpecialLinearGroup.diag2n hij a ha : Matrix ι ι F) *ᵥ (Pi.single l (1 : F) : ι → F)
      = Matrix.diagonal (fun k => if k = i then a else if k = j then a⁻¹ else 1) *ᵥ
          (Pi.single l (1 : F) : ι → F) :=
    congrArg (fun M : Matrix ι ι F => M *ᵥ (Pi.single l (1 : F) : ι → F))
      (SpecialLinearGroup.diag2n_coe hij a ha)
  have h2 : Matrix.diagonal (fun k => if k = i then a else if k = j then a⁻¹ else 1) *ᵥ
        (Pi.single l (1 : F) : ι → F)
      = Pi.single l ((if l = i then a else if l = j then a⁻¹ else 1) * 1) :=
    Matrix.diagonal_mulVec_single (fun k => if k = i then a else if k = j then a⁻¹ else 1) l
      (1 : F)
  have h3 : Pi.single l ((if l = i then a else if l = j then a⁻¹ else 1) * 1)
      = Pi.single l (if l = i then a else if l = j then a⁻¹ else 1) :=
    congrArg (fun x : F => Pi.single (M := fun _ => F) l x)
      (mul_one (if l = i then a else if l = j then a⁻¹ else 1))
  have h5 : (if l = i then a else if l = j then a⁻¹ else 1) • (1 : F)
      = (if l = i then a else if l = j then a⁻¹ else 1) :=
    (smul_eq_mul _ _).trans (mul_one _)
  have h4 : Pi.single l (if l = i then a else if l = j then a⁻¹ else 1)
      = (if l = i then a else if l = j then a⁻¹ else 1) • Pi.single l (1 : F) :=
    Eq.subst (motive := fun x : F => Pi.single (M := fun _ => F) l x
        = (if l = i then a else if l = j then a⁻¹ else 1) • Pi.single l (1 : F)) h5
      (Pi.single_smul' l (if l = i then a else if l = j then a⁻¹ else 1) (1 : F))
  have h6 : (SpecialLinearGroup.diag2n hij a ha : Matrix ι ι F) *ᵥ (Pi.single l (1 : F) : ι → F)
      = (if l = i then a else if l = j then a⁻¹ else 1) • (Pi.single l (1 : F) : ι → F) :=
    h1.trans (h2.trans (h3.trans h4))
  exact h6

-- Reference: [Steinberg]; computation via the action on basis vectors, exactly
-- as in `commutator_transvection_transvection` (SLTransvection.lean):
-- `w_ij(u)` sends `e_i ↦ -u⁻¹ e_j`, `e_j ↦ u e_i`, fixes other `e_l`
-- (`wOf_smul_single_fst/snd/other`); hence `h_ij(u)` sends `e_i ↦ u e_i`,
-- `e_j ↦ u⁻¹ e_j`, fixes others = `diag2n` (`diag2n_smul_single`).
/-- **The torus identity**: `h_ij(u) = diag2n(i, j, u)` (proved). -/
theorem hOf_eq_diag2n {i j : ι} (hij : i ≠ j) (u : F) (hu : u ≠ 0) :
    hOf hij u hu = SpecialLinearGroup.diag2n hij u hu := by
  apply SpecialLinearGroup.ext
  intro p q
  have hsmul : ∀ l : ι,
      ((hOf hij u hu : SpecialLinearGroup ι F) : Matrix ι ι F) *ᵥ (Pi.single l (1 : F) : ι → F)
      = ((SpecialLinearGroup.diag2n hij u hu : SpecialLinearGroup ι F) : Matrix ι ι F) *ᵥ
          (Pi.single l (1 : F) : ι → F) := by
    intro l
    have hneg1 : (-1 : F) ≠ 0 := neg_ne_zero.mpr one_ne_zero
    have hstep : hOf hij u hu • (Pi.single l (1 : F) : ι → F)
        = wOf hij u hu • (wOf hij (-1) hneg1 •
            (Pi.single l (1 : F) : ι → F)) :=
      mul_smul (wOf hij u hu) (wOf hij (-1) hneg1) (Pi.single l (1 : F) : ι → F)
    rcases eq_or_ne i l with rfl | hli
    · -- case `l = i`: `w_ij(-1)` sends `e_i ↦ e_j`, then `w_ij(u)` sends `e_j ↦ u e_i`
      have hw1 : wOf hij (-1) hneg1 • (Pi.single i (1 : F) : ι → F)
          = (Pi.single j (1 : F) : ι → F) := by
        have h := wOf_smul_single_fst hij (-1) hneg1
        have hneg : (-((-1 : F)⁻¹)) = (1 : F) :=
          (congrArg Neg.neg (inv_neg (a := (1 : F)))).trans
          ((congrArg Neg.neg (congrArg Neg.neg (inv_one (G := F)))).trans (neg_neg (1 : F)))
        exact h.trans (Eq.subst
          (motive := fun c : F => c • (Pi.single j (1 : F) : ι → F)
            = (Pi.single j (1 : F) : ι → F)) hneg.symm (one_smul F _))
      calc ((hOf hij u hu : SpecialLinearGroup ι F) : Matrix ι ι F) *ᵥ
            (Pi.single i (1 : F) : ι → F)
          = wOf hij u hu • (wOf hij (-1) hneg1 •
              (Pi.single i (1 : F) : ι → F)) := hstep
        _ = wOf hij u hu • (Pi.single j (1 : F) : ι → F) :=
            congrArg (fun v => wOf hij u hu • v) hw1
        _ = u • (Pi.single i (1 : F) : ι → F) := wOf_smul_single_snd hij u hu
        _ = (if i = i then u else if i = j then u⁻¹ else 1) • (Pi.single i (1 : F) : ι → F) :=
            Eq.subst (motive := fun c : F => u • (Pi.single i (1 : F) : ι → F)
              = c • (Pi.single i (1 : F) : ι → F)) (ite_eq_left rfl).symm rfl
        _ = ((SpecialLinearGroup.diag2n hij u hu : SpecialLinearGroup ι F) :
              Matrix ι ι F) *ᵥ (Pi.single i (1 : F) : ι → F) :=
            (diag2n_smul_single hij u hu).symm
    · rcases eq_or_ne j l with rfl | hlj
      · -- case `l = j`: `w_ij(-1)` sends `e_j ↦ -e_i`, then `w_ij(u)` sends `-e_i ↦ u⁻¹ e_j`
        have hw1 : wOf hij (-1) hneg1 • (Pi.single j (1 : F) : ι → F)
            = (-1 : F) • (Pi.single i (1 : F) : ι → F) :=
          wOf_smul_single_snd hij (-1) hneg1
        have hneg : (-1 : F) * (-u⁻¹) = u⁻¹ :=
          (mul_neg (-1 : F) u⁻¹).trans
            ((congrArg Neg.neg (neg_one_mul u⁻¹)).trans (neg_neg u⁻¹))
        calc ((hOf hij u hu : SpecialLinearGroup ι F) : Matrix ι ι F) *ᵥ
              (Pi.single j (1 : F) : ι → F)
            = wOf hij u hu • (wOf hij (-1) hneg1 •
                (Pi.single j (1 : F) : ι → F)) := hstep
          _ = wOf hij u hu • ((-1 : F) • (Pi.single i (1 : F) : ι → F)) :=
              congrArg (fun v => wOf hij u hu • v) hw1
          _ = (-1 : F) • (wOf hij u hu • (Pi.single i (1 : F) : ι → F)) :=
              smul_comm _ (-1 : F) _
          _ = (-1 : F) • ((-u⁻¹) • (Pi.single j (1 : F) : ι → F)) :=
              congrArg (fun v => (-1 : F) • v) (wOf_smul_single_fst hij u hu)
          _ = ((-1 : F) * (-u⁻¹)) • (Pi.single j (1 : F) : ι → F) :=
              smul_smul (-1 : F) (-u⁻¹) _
          _ = u⁻¹ • (Pi.single j (1 : F) : ι → F) :=
              congrArg (fun c : F => c • (Pi.single j (1 : F) : ι → F)) hneg
          _ = (if j = i then u else if j = j then u⁻¹ else 1) • (Pi.single j (1 : F) : ι → F) :=
              Eq.subst (motive := fun c : F => u⁻¹ • (Pi.single j (1 : F) : ι → F)
                = c • (Pi.single j (1 : F) : ι → F))
                ((ite_eq_right (Ne.symm hij)).trans (ite_eq_left rfl)).symm rfl
          _ = ((SpecialLinearGroup.diag2n hij u hu : SpecialLinearGroup ι F) :
                Matrix ι ι F) *ᵥ (Pi.single j (1 : F) : ι → F) :=
              (diag2n_smul_single hij u hu).symm
      · -- case `l ∉ {i, j}`: both Weyl factors fix `e_l`, and the diagonal acts by `1`
        have hw1 : wOf hij (-1) hneg1 • (Pi.single l (1 : F) : ι → F)
            = (Pi.single l (1 : F) : ι → F) :=
          wOf_smul_single_other hij (-1) hneg1 (Ne.symm hli) (Ne.symm hlj)
        have hw2 : wOf hij u hu • (Pi.single l (1 : F) : ι → F)
            = (Pi.single l (1 : F) : ι → F) :=
          wOf_smul_single_other hij u hu (Ne.symm hli) (Ne.symm hlj)
        calc ((hOf hij u hu : SpecialLinearGroup ι F) : Matrix ι ι F) *ᵥ
              (Pi.single l (1 : F) : ι → F)
            = wOf hij u hu • (wOf hij (-1) hneg1 •
                (Pi.single l (1 : F) : ι → F)) := hstep
          _ = wOf hij u hu • (Pi.single l (1 : F) : ι → F) :=
              congrArg (fun v => wOf hij u hu • v) hw1
          _ = (Pi.single l (1 : F) : ι → F) := hw2
          _ = (1 : F) • (Pi.single l (1 : F) : ι → F) := (one_smul F _).symm
          _ = (if l = i then u else if l = j then u⁻¹ else 1) • (Pi.single l (1 : F) : ι → F) :=
              Eq.subst (motive := fun c : F => (1 : F) • (Pi.single l (1 : F) : ι → F)
                = c • (Pi.single l (1 : F) : ι → F))
                ((ite_eq_right (Ne.symm hli)).trans (ite_eq_right (Ne.symm hlj))).symm rfl
          _ = ((SpecialLinearGroup.diag2n hij u hu : SpecialLinearGroup ι F) :
                Matrix ι ι F) *ᵥ (Pi.single l (1 : F) : ι → F) :=
              (diag2n_smul_single hij u hu).symm
  have hentry : ((hOf hij u hu : SpecialLinearGroup ι F) : Matrix ι ι F) p q
      = ((SpecialLinearGroup.diag2n hij u hu : SpecialLinearGroup ι F) : Matrix ι ι F) p q :=
    (congrFun (Matrix.mulVec_single_one _ q) p).symm.trans
      ((congrFun (hsmul q) p).trans (congrFun (Matrix.mulVec_single_one _ q) p))
  exact hentry

-- Reference: `hOf_eq_diag2n` + `transvection_mem_commutator_of_card_three`
-- (SLTransvection.lean) + `Subgroup.mul_mem`; [Carter] ch. 5.
/-- In rank `≥ 3`, every `diag2n` lies in the commutator subgroup: it is a
product of six transvections, each a commutator. -/
theorem diag2n_mem_commutator_of_card_three {i j : ι} (hij : i ≠ j) (a : F) (ha : a ≠ 0)
    (hι : 3 ≤ Fintype.card ι) :
    SpecialLinearGroup.diag2n hij a ha ∈ commutator (SpecialLinearGroup ι F) := by
  have hT : ∀ (p q : ι) (hpq : p ≠ q) (b : F),
      SpecialLinearGroup.transvection hpq b ∈ commutator (SpecialLinearGroup ι F) :=
    fun p q hpq b => transvection_mem_commutator_of_card_three hpq b hι
  -- `hOf_eq_diag2n` rewrites the goal to `hOf ∈ commutator`, and
  -- `hOf = wOf * wOf`, each `wOf` a triple product of transvections
  exact Eq.subst (motive := fun x => x ∈ commutator (SpecialLinearGroup ι F))
    (hOf_eq_diag2n hij a ha)
    (Subgroup.mul_mem _
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hT i j hij a)
        (hT j i (Ne.symm hij) (-a⁻¹))) (hT i j hij a))
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hT i j hij (-1))
        (hT j i (Ne.symm hij) (-(-1 : F)⁻¹))) (hT i j hij (-1))))

end BoringMath
