/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.GroupTheory.Commutator.Basic

/-!
# The transvection commutator identity — step (1) of `SL_isPerfect` (#230)

For pairwise distinct `i j k`, in `SL(ι, F)`:

  `⁅T_ik(a), T_kj(b)⁆ = T_ij(a * b)`.

Proved through the action on basis vectors (`transvection_smul_single_fst/snd`),
not by entry sums. Consequence: when `3 ≤ Fintype.card ι`, every transvection
`T_ij(c)` is a commutator (`⁅T_ik(c), T_kj(1)⁆`), hence lies in
`commutator (SL ι F)` — step (1) of the peeling plan of `SL_isPerfect`
(SLPerfect.lean).

## References
* [Carter] R. W. Carter, *Simple Groups of Lie Type*, Wiley 1972, ch. 5
  (transvections are commutators in rank ≥ 3); [Wilson] GTM 251, ch. 5.
* mathlib pin v4.35.0-rc3: `SpecialLinearGroup.transvection`,
  `transvection_smul_single_fst`, `transvection_smul_single_snd`,
  `transvection_inv`, `transvection_coe`, `Matrix.single_mulVec_eq`,
  `Matrix.mulVec_single_one`, `commutatorElement_def`,
  `Subgroup.commutator_mem_commutator`.
-/

namespace BoringMath

open Matrix
open scoped commutatorElement

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {F : Type*} [Field F]

/-! ## Action of a transvection on an unrelated basis vector -/

-- Reference: mathlib pin v4.35.0-rc3, `SpecialLinearGroup.transvection_coe`,
-- `Matrix.add_mulVec`, `Matrix.one_mulVec`, `Matrix.single_mulVec_eq`,
-- `Pi.single_apply`, `ite_eq_right`.
/-- A transvection `T_pq(b)` fixes the basis vector `e_l` for `l ≠ q`. -/
theorem transvection_smul_single_other {p q l : ι} (hpq : p ≠ q) (b : F) (hl : l ≠ q) :
    (SpecialLinearGroup.transvection hpq b) • (Pi.single l (1 : F) : ι → F)
      = (Pi.single l 1 : ι → F) := by
  have h1 : (SpecialLinearGroup.transvection hpq b : Matrix ι ι F) = 1 + single p q b :=
    SpecialLinearGroup.transvection_coe hpq b
  have h3 : (Pi.single l (1 : F) : ι → F) q = 0 :=
    (Pi.single_apply l (1 : F) q).trans (ite_eq_right hl.symm)
  have h2 : (single p q b : Matrix ι ι F) *ᵥ (Pi.single l (1 : F) : ι → F) = 0 :=
    Eq.subst
      (motive := fun u => (single p q b : Matrix ι ι F) *ᵥ (Pi.single l (1 : F) : ι → F) = u)
      ((congrArg (fun u => (b * u) • (Pi.single p 1 : ι → F)) h3).trans
        ((congrArg (fun u => u • (Pi.single p 1 : ι → F)) (mul_zero b)).trans
          (zero_smul F (Pi.single p 1 : ι → F))))
      (Matrix.single_mulVec_eq p q b (Pi.single l (1 : F) : ι → F))
  have h4 : ((SpecialLinearGroup.transvection hpq b : SpecialLinearGroup ι F) : Matrix ι ι F)
      *ᵥ (Pi.single l (1 : F) : ι → F) = (Pi.single l 1 : ι → F) :=
    Eq.subst
      (motive := fun M => (M : Matrix ι ι F) *ᵥ (Pi.single l (1 : F) : ι → F)
        = (Pi.single l 1 : ι → F))
      h1.symm
      ((Matrix.add_mulVec 1 (single p q b) (Pi.single l (1 : F) : ι → F)).trans
        ((congrArg (fun v => (1 : Matrix ι ι F) *ᵥ (Pi.single l (1 : F) : ι → F) + v) h2).trans
          ((congrArg (fun v => v + 0) (Matrix.one_mulVec (Pi.single l (1 : F) : ι → F))).trans
            (add_zero (Pi.single l (1 : F) : ι → F)))))
  exact Eq.subst
    (motive := fun v : ι → F => (SpecialLinearGroup.transvection hpq b : SpecialLinearGroup ι F)
      • v = v)
    rfl h4

-- Reference: `transvection_smul_single_snd` (pin) for `l = q` and
-- `transvection_smul_single_other` for `l ≠ q`; `ite_eq_left`/`ite_eq_right`.
/-- Uniform action of a transvection on a basis vector. -/
theorem transvection_smul_single {p q l : ι} (hpq : p ≠ q) (b : F) :
    (SpecialLinearGroup.transvection hpq b) • (Pi.single l (1 : F) : ι → F)
      = if l = q then Pi.single l 1 + b • (Pi.single p 1 : ι → F) else Pi.single l 1 := by
  rcases eq_or_ne q l with rfl | hl
  · exact (SpecialLinearGroup.transvection_smul_single_snd hpq b).trans (ite_eq_left rfl).symm
  · exact (transvection_smul_single_other hpq b hl.symm).trans (ite_eq_right hl.symm).symm

/-! ## The commutator identity -/

-- Reference: [Carter] ch. 5 / [Wilson] ch. 5; pin's `transvection_smul_single_fst`,
-- `transvection_smul_single_snd`, `transvection_inv`, `commutatorElement_def`,
-- `Matrix.mulVec_single_one`, `SpecialLinearGroup.ext`.
/-- **Transvection commutator identity**: for pairwise distinct `i j k`,
`⁅T_ik(a), T_kj(b)⁆ = T_ij(a * b)` in `SL(ι, F)` (proved via the action on basis
vectors). -/
theorem commutator_transvection_transvection {i j k : ι} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (a b : F) :
    ⁅SpecialLinearGroup.transvection hik a, SpecialLinearGroup.transvection hjk.symm b⁆
      = SpecialLinearGroup.transvection hij (a * b) := by
  apply SpecialLinearGroup.ext
  intro p q
  have hsmul : ∀ l : ι,
      ((⁅SpecialLinearGroup.transvection hik a, SpecialLinearGroup.transvection hjk.symm b⁆ :
          SpecialLinearGroup ι F) : Matrix ι ι F) *ᵥ (Pi.single l (1 : F) : ι → F)
      = ((SpecialLinearGroup.transvection hij (a * b) : SpecialLinearGroup ι F) :
          Matrix ι ι F) *ᵥ (Pi.single l (1 : F) : ι → F) := by
    intro l
    have hAinv : (SpecialLinearGroup.transvection hik a)⁻¹
        = SpecialLinearGroup.transvection hik (-a) := SpecialLinearGroup.transvection_inv hik a
    have hBinv : (SpecialLinearGroup.transvection hjk.symm b)⁻¹
        = SpecialLinearGroup.transvection hjk.symm (-b) :=
      SpecialLinearGroup.transvection_inv hjk.symm b
    have hstep : (⁅SpecialLinearGroup.transvection hik a,
        SpecialLinearGroup.transvection hjk.symm b⁆ : SpecialLinearGroup ι F) •
        (Pi.single l (1 : F) : ι → F)
        = (SpecialLinearGroup.transvection hik a) •
          ((SpecialLinearGroup.transvection hjk.symm b) •
            ((SpecialLinearGroup.transvection hik a)⁻¹ •
              ((SpecialLinearGroup.transvection hjk.symm b)⁻¹ •
                (Pi.single l (1 : F) : ι → F)))) :=
      (congrArg (fun x : SpecialLinearGroup ι F => x • (Pi.single l (1 : F) : ι → F))
        (commutatorElement_def (SpecialLinearGroup.transvection hik a)
          (SpecialLinearGroup.transvection hjk.symm b))).trans
        ((mul_smul _ _ _).trans ((mul_smul _ _ _).trans (mul_smul _ _ _)))
    -- NOTE: the four cases below are verified by hand; for `B = T_kj(b)`,
    -- `A = T_ik(a)`, `D = T_ij(a*b)`:
    --   l = j : B⁻¹e_j = e_j - b e_k; A⁻¹ gives e_j - b e_k + ab e_i;
    --           B gives e_j + ab e_i; A fixes it. RHS: T_ij(ab) e_j = e_j + ab e_i.
    --   l = k : B⁻¹ e_k = e_k; A⁻¹ e_k = e_k - a e_i; B gives e_k - a e_i; A gives e_k.
    --   l = i : all four fix e_i. RHS: T_ij(ab) fixes e_i.
    --   l other : all four fix e_l. RHS fixes e_l.
    rcases eq_or_ne j l with rfl | hlj
    · -- case l = j
      have s1 : (SpecialLinearGroup.transvection hjk.symm b)⁻¹ • (Pi.single j (1 : F) : ι → F)
          = (Pi.single j (1 : F) : ι → F) + (-b) • (Pi.single k (1 : F) : ι → F) :=
        (congrArg (fun x : SpecialLinearGroup ι F => x • (Pi.single j (1 : F) : ι → F))
          hBinv).trans (SpecialLinearGroup.transvection_smul_single_snd hjk.symm (-b))
      have s2 : (SpecialLinearGroup.transvection hik a)⁻¹ • (Pi.single j (1 : F) : ι → F)
          = (Pi.single j (1 : F) : ι → F) :=
        (congrArg (fun x : SpecialLinearGroup ι F => x • (Pi.single j (1 : F) : ι → F))
          hAinv).trans (transvection_smul_single_other hik (-a) hjk)
      have s3 : (SpecialLinearGroup.transvection hik a)⁻¹ • (Pi.single k (1 : F) : ι → F)
          = (Pi.single k (1 : F) : ι → F) + (-a) • (Pi.single i (1 : F) : ι → F) :=
        (congrArg (fun x : SpecialLinearGroup ι F => x • (Pi.single k (1 : F) : ι → F))
          hAinv).trans (SpecialLinearGroup.transvection_smul_single_snd hik (-a))
      have s4 : (SpecialLinearGroup.transvection hik a)⁻¹ •
          ((-b) • (Pi.single k (1 : F) : ι → F))
          = (-b) • (Pi.single k (1 : F) : ι → F)
            + (a * b) • (Pi.single i (1 : F) : ι → F) := by
        calc (SpecialLinearGroup.transvection hik a)⁻¹ •
            ((-b) • (Pi.single k (1 : F) : ι → F))
          = (-b) • ((SpecialLinearGroup.transvection hik a)⁻¹ • (Pi.single k (1 : F) : ι → F)) :=
            smul_comm _ (-b) _
        _ = (-b) • ((Pi.single k (1 : F) : ι → F) + (-a) • (Pi.single i (1 : F) : ι → F)) :=
            congrArg (fun v => (-b) • v) s3
        _ = (-b) • (Pi.single k (1 : F) : ι → F)
            + (-b) • ((-a) • (Pi.single i (1 : F) : ι → F)) := smul_add (-b) _ _
        _ = (-b) • (Pi.single k (1 : F) : ι → F)
            + ((-b) * (-a)) • (Pi.single i (1 : F) : ι → F) :=
            congrArg (fun v => (-b) • (Pi.single k (1 : F) : ι → F) + v)
              (smul_smul (-b) (-a) (Pi.single i (1 : F) : ι → F))
        _ = (-b) • (Pi.single k (1 : F) : ι → F) + (b * a) • (Pi.single i (1 : F) : ι → F) :=
            congrArg (fun v => (-b) • (Pi.single k (1 : F) : ι → F) + v)
              (congrArg (fun u => u • (Pi.single i (1 : F) : ι → F)) (neg_mul_neg b a))
        _ = (-b) • (Pi.single k (1 : F) : ι → F) + (a * b) • (Pi.single i (1 : F) : ι → F) :=
            congrArg (fun v => (-b) • (Pi.single k (1 : F) : ι → F) + v)
              (congrArg (fun u => u • (Pi.single i (1 : F) : ι → F)) (mul_comm b a))
      have t1 : (SpecialLinearGroup.transvection hik a)⁻¹ •
          ((SpecialLinearGroup.transvection hjk.symm b)⁻¹ • (Pi.single j (1 : F) : ι → F))
          = (Pi.single j (1 : F) : ι → F)
            + ((-b) • (Pi.single k (1 : F) : ι → F) + (a * b) • (Pi.single i (1 : F) : ι → F)) := by
        calc (SpecialLinearGroup.transvection hik a)⁻¹ •
            ((SpecialLinearGroup.transvection hjk.symm b)⁻¹ • (Pi.single j (1 : F) : ι → F))
          = (SpecialLinearGroup.transvection hik a)⁻¹ •
              ((Pi.single j (1 : F) : ι → F) + (-b) • (Pi.single k (1 : F) : ι → F)) :=
            congrArg (fun v => (SpecialLinearGroup.transvection hik a)⁻¹ • v) s1
        _ = (SpecialLinearGroup.transvection hik a)⁻¹ • (Pi.single j (1 : F) : ι → F)
            + (SpecialLinearGroup.transvection hik a)⁻¹ • ((-b) • (Pi.single k (1 : F) : ι → F)) :=
            smul_add _ _ _
        _ = (Pi.single j (1 : F) : ι → F)
            + ((-b) • (Pi.single k (1 : F) : ι → F) + (a * b) • (Pi.single i (1 : F) : ι → F)) :=
            (congrArg (fun v => v + (SpecialLinearGroup.transvection hik a)⁻¹ •
                ((-b) • (Pi.single k (1 : F) : ι → F))) s2).trans
              (congrArg (fun v => (Pi.single j (1 : F) : ι → F) + v) s4)
      have t2 : (SpecialLinearGroup.transvection hjk.symm b) •
          ((Pi.single j (1 : F) : ι → F)
            + ((-b) • (Pi.single k (1 : F) : ι → F) + (a * b) • (Pi.single i (1 : F) : ι → F)))
          = (Pi.single j (1 : F) : ι → F) + (a * b) • (Pi.single i (1 : F) : ι → F) := by
        have u1 : (SpecialLinearGroup.transvection hjk.symm b) • (Pi.single j (1 : F) : ι → F)
            = (Pi.single j (1 : F) : ι → F) + b • (Pi.single k (1 : F) : ι → F) :=
          SpecialLinearGroup.transvection_smul_single_snd hjk.symm b
        have u2 : (SpecialLinearGroup.transvection hjk.symm b) • (Pi.single k (1 : F) : ι → F)
            = (Pi.single k (1 : F) : ι → F) :=
          transvection_smul_single_other hjk.symm b hjk.symm
        have u3 : (SpecialLinearGroup.transvection hjk.symm b) • (Pi.single i (1 : F) : ι → F)
            = (Pi.single i (1 : F) : ι → F) :=
          transvection_smul_single_other hjk.symm b hij
        have u4 : (SpecialLinearGroup.transvection hjk.symm b) •
            ((-b) • (Pi.single k (1 : F) : ι → F)) = (-b) • (Pi.single k (1 : F) : ι → F) :=
          (smul_comm _ (-b) _).trans (congrArg (fun v => (-b) • v) u2)
        have u5 : (SpecialLinearGroup.transvection hjk.symm b) •
            ((a * b) • (Pi.single i (1 : F) : ι → F)) = (a * b) • (Pi.single i (1 : F) : ι → F) :=
          (smul_comm _ (a * b) _).trans (congrArg (fun v => (a * b) • v) u3)
        have u6 : (SpecialLinearGroup.transvection hjk.symm b) •
            ((-b) • (Pi.single k (1 : F) : ι → F) + (a * b) • (Pi.single i (1 : F) : ι → F))
            = (-b) • (Pi.single k (1 : F) : ι → F) + (a * b) • (Pi.single i (1 : F) : ι → F) :=
          (smul_add _ _ _).trans
            ((congrArg (fun v => (SpecialLinearGroup.transvection hjk.symm b) •
                ((-b) • (Pi.single k (1 : F) : ι → F)) + v) u5).trans
              (congrArg (fun v => v + (a * b) • (Pi.single i (1 : F) : ι → F)) u4))
        calc (SpecialLinearGroup.transvection hjk.symm b) •
            ((Pi.single j (1 : F) : ι → F)
              + ((-b) • (Pi.single k (1 : F) : ι → F) + (a * b) • (Pi.single i (1 : F) : ι → F)))
          = (SpecialLinearGroup.transvection hjk.symm b) • (Pi.single j (1 : F) : ι → F)
            + (SpecialLinearGroup.transvection hjk.symm b) •
              ((-b) • (Pi.single k (1 : F) : ι → F) + (a * b) • (Pi.single i (1 : F) : ι → F)) :=
            smul_add _ _ _
        _ = ((Pi.single j (1 : F) : ι → F) + b • (Pi.single k (1 : F) : ι → F))
            + ((-b) • (Pi.single k (1 : F) : ι → F) + (a * b) • (Pi.single i (1 : F) : ι → F)) :=
            (congrArg (fun v => v + (SpecialLinearGroup.transvection hjk.symm b) •
                ((-b) • (Pi.single k (1 : F) : ι → F) + (a * b) • (Pi.single i (1 : F) : ι → F)))
                u1).trans
              (congrArg (fun v => ((Pi.single j (1 : F) : ι → F)
                  + b • (Pi.single k (1 : F) : ι → F)) + v) u6)
        _ = (Pi.single j (1 : F) : ι → F) + (a * b) • (Pi.single i (1 : F) : ι → F) := by
          calc ((Pi.single j (1 : F) : ι → F) + b • (Pi.single k (1 : F) : ι → F))
              + ((-b) • (Pi.single k (1 : F) : ι → F) + (a * b) • (Pi.single i (1 : F) : ι → F))
            = (Pi.single j (1 : F) : ι → F)
              + ((b • (Pi.single k (1 : F) : ι → F) + (-b) • (Pi.single k (1 : F) : ι → F))
                + (a * b) • (Pi.single i (1 : F) : ι → F)) :=
              (add_assoc _ _ _).trans
                (congrArg (fun v => (Pi.single j (1 : F) : ι → F) + v) (add_assoc _ _ _).symm)
          _ = (Pi.single j (1 : F) : ι → F)
              + (((b + (-b)) • (Pi.single k (1 : F) : ι → F))
                + (a * b) • (Pi.single i (1 : F) : ι → F)) :=
              congrArg (fun v => (Pi.single j (1 : F) : ι → F)
                + (v + (a * b) • (Pi.single i (1 : F) : ι → F))) (add_smul b (-b) _).symm
          _ = (Pi.single j (1 : F) : ι → F)
              + (((0 : F) • (Pi.single k (1 : F) : ι → F))
                + (a * b) • (Pi.single i (1 : F) : ι → F)) :=
              congrArg (fun v => (Pi.single j (1 : F) : ι → F)
                + (v + (a * b) • (Pi.single i (1 : F) : ι → F)))
                (congrArg (fun u => u • (Pi.single k (1 : F) : ι → F)) (add_neg_cancel b))
          _ = (Pi.single j (1 : F) : ι → F)
              + (0 + (a * b) • (Pi.single i (1 : F) : ι → F)) :=
              congrArg (fun v => (Pi.single j (1 : F) : ι → F)
                + (v + (a * b) • (Pi.single i (1 : F) : ι → F)))
                (zero_smul F (Pi.single k (1 : F) : ι → F))
          _ = (Pi.single j (1 : F) : ι → F) + (a * b) • (Pi.single i (1 : F) : ι → F) :=
              congrArg (fun v => (Pi.single j (1 : F) : ι → F) + v) (zero_add _)
      have t3 : (SpecialLinearGroup.transvection hik a) •
          ((Pi.single j (1 : F) : ι → F) + (a * b) • (Pi.single i (1 : F) : ι → F))
          = (Pi.single j (1 : F) : ι → F) + (a * b) • (Pi.single i (1 : F) : ι → F) := by
        have v1 : (SpecialLinearGroup.transvection hik a) • (Pi.single j (1 : F) : ι → F)
            = (Pi.single j (1 : F) : ι → F) := transvection_smul_single_other hik a hjk
        have v2 : (SpecialLinearGroup.transvection hik a) • (Pi.single i (1 : F) : ι → F)
            = (Pi.single i (1 : F) : ι → F) := SpecialLinearGroup.transvection_smul_single_fst hik a
        calc (SpecialLinearGroup.transvection hik a) •
            ((Pi.single j (1 : F) : ι → F) + (a * b) • (Pi.single i (1 : F) : ι → F))
          = (SpecialLinearGroup.transvection hik a) • (Pi.single j (1 : F) : ι → F)
            + (SpecialLinearGroup.transvection hik a) • ((a * b) • (Pi.single i (1 : F) : ι → F)) :=
            smul_add _ _ _
        _ = (Pi.single j (1 : F) : ι → F)
            + (SpecialLinearGroup.transvection hik a) • ((a * b) • (Pi.single i (1 : F) : ι → F)) :=
            congrArg (fun v => v + (SpecialLinearGroup.transvection hik a) •
              ((a * b) • (Pi.single i (1 : F) : ι → F))) v1
        _ = (Pi.single j (1 : F) : ι → F)
            + (a * b) • ((SpecialLinearGroup.transvection hik a) • (Pi.single i (1 : F) : ι → F)) :=
            congrArg (fun v => (Pi.single j (1 : F) : ι → F) + v) (smul_comm _ (a * b) _)
        _ = (Pi.single j (1 : F) : ι → F) + (a * b) • (Pi.single i (1 : F) : ι → F) :=
            congrArg (fun v => (Pi.single j (1 : F) : ι → F) + v)
              (congrArg (fun v => (a * b) • v) v2)
      calc (⁅SpecialLinearGroup.transvection hik a, SpecialLinearGroup.transvection hjk.symm b⁆ :
            SpecialLinearGroup ι F) • (Pi.single j (1 : F) : ι → F)
        = (SpecialLinearGroup.transvection hik a) •
            ((SpecialLinearGroup.transvection hjk.symm b) •
              ((SpecialLinearGroup.transvection hik a)⁻¹ •
                ((SpecialLinearGroup.transvection hjk.symm b)⁻¹ •
                  (Pi.single j (1 : F) : ι → F)))) := hstep
      _ = (SpecialLinearGroup.transvection hik a) •
            ((SpecialLinearGroup.transvection hjk.symm b) •
              ((Pi.single j (1 : F) : ι → F)
                + ((-b) • (Pi.single k (1 : F) : ι → F)
                  + (a * b) • (Pi.single i (1 : F) : ι → F)))) :=
            congrArg (fun v => (SpecialLinearGroup.transvection hik a) •
              ((SpecialLinearGroup.transvection hjk.symm b) • v)) t1
      _ = (SpecialLinearGroup.transvection hik a) •
            ((Pi.single j (1 : F) : ι → F) + (a * b) • (Pi.single i (1 : F) : ι → F)) :=
            congrArg (fun v => (SpecialLinearGroup.transvection hik a) • v) t2
      _ = (Pi.single j (1 : F) : ι → F) + (a * b) • (Pi.single i (1 : F) : ι → F) := t3
      _ = (SpecialLinearGroup.transvection hij (a * b) : SpecialLinearGroup ι F) •
            (Pi.single j (1 : F) : ι → F) :=
            (SpecialLinearGroup.transvection_smul_single_snd hij (a * b)).symm
    · rcases eq_or_ne k l with rfl | hlk
      · -- case l = k
        have w1 : (SpecialLinearGroup.transvection hjk.symm b)⁻¹ • (Pi.single k (1 : F) : ι → F)
            = (Pi.single k (1 : F) : ι → F) :=
          (congrArg (fun x : SpecialLinearGroup ι F => x • (Pi.single k (1 : F) : ι → F))
            hBinv).trans (transvection_smul_single_other hjk.symm (-b) hjk.symm)
        have w2 : (SpecialLinearGroup.transvection hik a)⁻¹ • (Pi.single k (1 : F) : ι → F)
            = (Pi.single k (1 : F) : ι → F) + (-a) • (Pi.single i (1 : F) : ι → F) :=
          (congrArg (fun x : SpecialLinearGroup ι F => x • (Pi.single k (1 : F) : ι → F))
            hAinv).trans (SpecialLinearGroup.transvection_smul_single_snd hik (-a))
        have w3 : (SpecialLinearGroup.transvection hjk.symm b) • (Pi.single k (1 : F) : ι → F)
            = (Pi.single k (1 : F) : ι → F) :=
          transvection_smul_single_other hjk.symm b hjk.symm
        have w4 : (SpecialLinearGroup.transvection hjk.symm b) • (Pi.single i (1 : F) : ι → F)
            = (Pi.single i (1 : F) : ι → F) :=
          transvection_smul_single_other hjk.symm b hij
        have w5 : (SpecialLinearGroup.transvection hik a) • (Pi.single k (1 : F) : ι → F)
            = (Pi.single k (1 : F) : ι → F) + a • (Pi.single i (1 : F) : ι → F) :=
          SpecialLinearGroup.transvection_smul_single_snd hik a
        have w6 : (SpecialLinearGroup.transvection hik a) • (Pi.single i (1 : F) : ι → F)
            = (Pi.single i (1 : F) : ι → F) := SpecialLinearGroup.transvection_smul_single_fst hik a
        have x1 : (SpecialLinearGroup.transvection hik a)⁻¹ •
            ((SpecialLinearGroup.transvection hjk.symm b)⁻¹ • (Pi.single k (1 : F) : ι → F))
            = (Pi.single k (1 : F) : ι → F) + (-a) • (Pi.single i (1 : F) : ι → F) :=
          (congrArg (fun v => (SpecialLinearGroup.transvection hik a)⁻¹ • v) w1).trans w2
        have x2 : (SpecialLinearGroup.transvection hjk.symm b) •
            ((Pi.single k (1 : F) : ι → F) + (-a) • (Pi.single i (1 : F) : ι → F))
            = (Pi.single k (1 : F) : ι → F) + (-a) • (Pi.single i (1 : F) : ι → F) := by
          calc (SpecialLinearGroup.transvection hjk.symm b) •
              ((Pi.single k (1 : F) : ι → F) + (-a) • (Pi.single i (1 : F) : ι → F))
            = (SpecialLinearGroup.transvection hjk.symm b) • (Pi.single k (1 : F) : ι → F)
              + (SpecialLinearGroup.transvection hjk.symm b) •
                ((-a) • (Pi.single i (1 : F) : ι → F)) := smul_add _ _ _
          _ = (Pi.single k (1 : F) : ι → F)
              + (SpecialLinearGroup.transvection hjk.symm b) •
                ((-a) • (Pi.single i (1 : F) : ι → F)) :=
              congrArg (fun v => v + (SpecialLinearGroup.transvection hjk.symm b) •
                ((-a) • (Pi.single i (1 : F) : ι → F))) w3
          _ = (Pi.single k (1 : F) : ι → F)
              + (-a) • ((SpecialLinearGroup.transvection hjk.symm b) •
                (Pi.single i (1 : F) : ι → F)) :=
              congrArg (fun v => (Pi.single k (1 : F) : ι → F) + v) (smul_comm _ (-a) _)
          _ = (Pi.single k (1 : F) : ι → F) + (-a) • (Pi.single i (1 : F) : ι → F) :=
              congrArg (fun v => (Pi.single k (1 : F) : ι → F) + v)
                (congrArg (fun v => (-a) • v) w4)
        have x3 : (SpecialLinearGroup.transvection hik a) •
            ((Pi.single k (1 : F) : ι → F) + (-a) • (Pi.single i (1 : F) : ι → F))
            = (Pi.single k (1 : F) : ι → F) := by
          calc (SpecialLinearGroup.transvection hik a) •
              ((Pi.single k (1 : F) : ι → F) + (-a) • (Pi.single i (1 : F) : ι → F))
            = (SpecialLinearGroup.transvection hik a) • (Pi.single k (1 : F) : ι → F)
              + (SpecialLinearGroup.transvection hik a) • ((-a) • (Pi.single i (1 : F) : ι → F)) :=
              smul_add _ _ _
          _ = ((Pi.single k (1 : F) : ι → F) + a • (Pi.single i (1 : F) : ι → F))
              + (SpecialLinearGroup.transvection hik a) • ((-a) • (Pi.single i (1 : F) : ι → F)) :=
              congrArg (fun v => v + (SpecialLinearGroup.transvection hik a) •
                ((-a) • (Pi.single i (1 : F) : ι → F))) w5
          _ = ((Pi.single k (1 : F) : ι → F) + a • (Pi.single i (1 : F) : ι → F))
              + (-a) • ((SpecialLinearGroup.transvection hik a) • (Pi.single i (1 : F) : ι → F)) :=
              congrArg (fun v => ((Pi.single k (1 : F) : ι → F) + a • (Pi.single i (1 : F) : ι → F))
                + v) (smul_comm _ (-a) _)
          _ = ((Pi.single k (1 : F) : ι → F) + a • (Pi.single i (1 : F) : ι → F))
              + (-a) • (Pi.single i (1 : F) : ι → F) :=
              congrArg (fun v => ((Pi.single k (1 : F) : ι → F) + a • (Pi.single i (1 : F) : ι → F))
                + v) (congrArg (fun v => (-a) • v) w6)
          _ = (Pi.single k (1 : F) : ι → F) := by
            calc ((Pi.single k (1 : F) : ι → F) + a • (Pi.single i (1 : F) : ι → F))
                + (-a) • (Pi.single i (1 : F) : ι → F)
              = (Pi.single k (1 : F) : ι → F)
                + (a • (Pi.single i (1 : F) : ι → F) + (-a) • (Pi.single i (1 : F) : ι → F)) :=
                add_assoc _ _ _
            _ = (Pi.single k (1 : F) : ι → F) + ((a + (-a)) • (Pi.single i (1 : F) : ι → F)) :=
                congrArg (fun v => (Pi.single k (1 : F) : ι → F) + v) (add_smul a (-a) _).symm
            _ = (Pi.single k (1 : F) : ι → F) + ((0 : F) • (Pi.single i (1 : F) : ι → F)) :=
                congrArg (fun v => (Pi.single k (1 : F) : ι → F) + v)
                  (congrArg (fun u => u • (Pi.single i (1 : F) : ι → F)) (add_neg_cancel a))
            _ = (Pi.single k (1 : F) : ι → F) + 0 :=
                congrArg (fun v => (Pi.single k (1 : F) : ι → F) + v)
                  (zero_smul F (Pi.single i (1 : F) : ι → F))
            _ = (Pi.single k (1 : F) : ι → F) := add_zero _
        calc (⁅SpecialLinearGroup.transvection hik a, SpecialLinearGroup.transvection hjk.symm b⁆ :
              SpecialLinearGroup ι F) • (Pi.single k (1 : F) : ι → F)
          = (SpecialLinearGroup.transvection hik a) •
              ((SpecialLinearGroup.transvection hjk.symm b) •
                ((SpecialLinearGroup.transvection hik a)⁻¹ •
                  ((SpecialLinearGroup.transvection hjk.symm b)⁻¹ •
                    (Pi.single k (1 : F) : ι → F)))) := hstep
        _ = (SpecialLinearGroup.transvection hik a) •
              ((SpecialLinearGroup.transvection hjk.symm b) •
                ((Pi.single k (1 : F) : ι → F) + (-a) • (Pi.single i (1 : F) : ι → F))) :=
              congrArg (fun v => (SpecialLinearGroup.transvection hik a) •
                ((SpecialLinearGroup.transvection hjk.symm b) • v)) x1
        _ = (SpecialLinearGroup.transvection hik a) •
              ((Pi.single k (1 : F) : ι → F) + (-a) • (Pi.single i (1 : F) : ι → F)) :=
              congrArg (fun v => (SpecialLinearGroup.transvection hik a) • v) x2
        _ = (Pi.single k (1 : F) : ι → F) := x3
        _ = (SpecialLinearGroup.transvection hij (a * b) : SpecialLinearGroup ι F) •
              (Pi.single k (1 : F) : ι → F) :=
              (transvection_smul_single_other hij (a * b) hjk.symm).symm
      · rcases eq_or_ne i l with rfl | hli
        · -- case l = i: all four factors fix e_i
          have y1 : (SpecialLinearGroup.transvection hjk.symm b)⁻¹ •
              (Pi.single i (1 : F) : ι → F) = (Pi.single i (1 : F) : ι → F) :=
            (congrArg (fun x : SpecialLinearGroup ι F => x • (Pi.single i (1 : F) : ι → F))
              hBinv).trans (transvection_smul_single_other hjk.symm (-b) hij)
          have y2 : (SpecialLinearGroup.transvection hik a)⁻¹ • (Pi.single i (1 : F) : ι → F)
              = (Pi.single i (1 : F) : ι → F) :=
            (congrArg (fun x : SpecialLinearGroup ι F => x • (Pi.single i (1 : F) : ι → F))
              hAinv).trans (SpecialLinearGroup.transvection_smul_single_fst hik (-a))
          have y3 : (SpecialLinearGroup.transvection hjk.symm b) • (Pi.single i (1 : F) : ι → F)
              = (Pi.single i (1 : F) : ι → F) :=
            transvection_smul_single_other hjk.symm b hij
          have y4 : (SpecialLinearGroup.transvection hik a) • (Pi.single i (1 : F) : ι → F)
              = (Pi.single i (1 : F) : ι → F) :=
            SpecialLinearGroup.transvection_smul_single_fst hik a
          calc (⁅SpecialLinearGroup.transvection hik a,
              SpecialLinearGroup.transvection hjk.symm b⁆ : SpecialLinearGroup ι F) •
              (Pi.single i (1 : F) : ι → F)
            = (SpecialLinearGroup.transvection hik a) •
                ((SpecialLinearGroup.transvection hjk.symm b) •
                  ((SpecialLinearGroup.transvection hik a)⁻¹ •
                    ((SpecialLinearGroup.transvection hjk.symm b)⁻¹ •
                      (Pi.single i (1 : F) : ι → F)))) := hstep
          _ = (SpecialLinearGroup.transvection hik a) •
                ((SpecialLinearGroup.transvection hjk.symm b) •
                  ((SpecialLinearGroup.transvection hik a)⁻¹ • (Pi.single i (1 : F) : ι → F))) :=
              congrArg (fun v => (SpecialLinearGroup.transvection hik a) •
                ((SpecialLinearGroup.transvection hjk.symm b) •
                  ((SpecialLinearGroup.transvection hik a)⁻¹ • v))) y1
          _ = (SpecialLinearGroup.transvection hik a) •
                ((SpecialLinearGroup.transvection hjk.symm b) • (Pi.single i (1 : F) : ι → F)) :=
              congrArg (fun v => (SpecialLinearGroup.transvection hik a) •
                ((SpecialLinearGroup.transvection hjk.symm b) • v)) y2
          _ = (SpecialLinearGroup.transvection hik a) • (Pi.single i (1 : F) : ι → F) :=
              congrArg (fun v => (SpecialLinearGroup.transvection hik a) • v) y3
          _ = (Pi.single i (1 : F) : ι → F) := y4
          _ = (SpecialLinearGroup.transvection hij (a * b) : SpecialLinearGroup ι F) •
                (Pi.single i (1 : F) : ι → F) :=
              (SpecialLinearGroup.transvection_smul_single_fst hij (a * b)).symm
        · -- case l ∉ {i, j, k}: all four factors fix e_l
          have z1 : (SpecialLinearGroup.transvection hjk.symm b)⁻¹ •
              (Pi.single l (1 : F) : ι → F) = (Pi.single l (1 : F) : ι → F) :=
            (congrArg (fun x : SpecialLinearGroup ι F => x • (Pi.single l (1 : F) : ι → F))
              hBinv).trans (transvection_smul_single_other hjk.symm (-b) hlj.symm)
          have z2 : (SpecialLinearGroup.transvection hik a)⁻¹ • (Pi.single l (1 : F) : ι → F)
              = (Pi.single l (1 : F) : ι → F) :=
            (congrArg (fun x : SpecialLinearGroup ι F => x • (Pi.single l (1 : F) : ι → F))
              hAinv).trans (transvection_smul_single_other hik (-a) hlk.symm)
          have z3 : (SpecialLinearGroup.transvection hjk.symm b) • (Pi.single l (1 : F) : ι → F)
              = (Pi.single l (1 : F) : ι → F) :=
            transvection_smul_single_other hjk.symm b hlj.symm
          have z4 : (SpecialLinearGroup.transvection hik a) • (Pi.single l (1 : F) : ι → F)
              = (Pi.single l (1 : F) : ι → F) :=
            transvection_smul_single_other hik a hlk.symm
          calc (⁅SpecialLinearGroup.transvection hik a,
              SpecialLinearGroup.transvection hjk.symm b⁆ : SpecialLinearGroup ι F) •
              (Pi.single l (1 : F) : ι → F)
            = (SpecialLinearGroup.transvection hik a) •
                ((SpecialLinearGroup.transvection hjk.symm b) •
                  ((SpecialLinearGroup.transvection hik a)⁻¹ •
                    ((SpecialLinearGroup.transvection hjk.symm b)⁻¹ •
                      (Pi.single l (1 : F) : ι → F)))) := hstep
          _ = (SpecialLinearGroup.transvection hik a) •
                ((SpecialLinearGroup.transvection hjk.symm b) •
                  ((SpecialLinearGroup.transvection hik a)⁻¹ • (Pi.single l (1 : F) : ι → F))) :=
              congrArg (fun v => (SpecialLinearGroup.transvection hik a) •
                ((SpecialLinearGroup.transvection hjk.symm b) •
                  ((SpecialLinearGroup.transvection hik a)⁻¹ • v))) z1
          _ = (SpecialLinearGroup.transvection hik a) •
                ((SpecialLinearGroup.transvection hjk.symm b) • (Pi.single l (1 : F) : ι → F)) :=
              congrArg (fun v => (SpecialLinearGroup.transvection hik a) •
                ((SpecialLinearGroup.transvection hjk.symm b) • v)) z2
          _ = (SpecialLinearGroup.transvection hik a) • (Pi.single l (1 : F) : ι → F) :=
              congrArg (fun v => (SpecialLinearGroup.transvection hik a) • v) z3
          _ = (Pi.single l (1 : F) : ι → F) := z4
          _ = (SpecialLinearGroup.transvection hij (a * b) : SpecialLinearGroup ι F) •
                (Pi.single l (1 : F) : ι → F) :=
              (transvection_smul_single_other hij (a * b) hlj.symm).symm
  have hentry : ((⁅SpecialLinearGroup.transvection hik a,
      SpecialLinearGroup.transvection hjk.symm b⁆ : SpecialLinearGroup ι F) : Matrix ι ι F) p q
      = ((SpecialLinearGroup.transvection hij (a * b) : SpecialLinearGroup ι F) :
          Matrix ι ι F) p q :=
    (congrFun (Matrix.mulVec_single_one _ q) p).symm.trans
      ((congrFun (hsmul q) p).trans (congrFun (Matrix.mulVec_single_one _ q) p))
  exact hentry

/-! ## Transvections are commutators in rank ≥ 3 -/

-- Reference: `commutator_transvection_transvection` + `Subgroup.commutator_mem_commutator`;
-- [Carter] ch. 5.
/-- When `3 ≤ Fintype.card ι`, every transvection `T_ij(c)` of `SL(ι, F)` lies in
the commutator subgroup: `T_ij(c) = ⁅T_ik(c), T_kj(1)⁆` for any third index `k`. -/
theorem transvection_mem_commutator_of_card_three {i j : ι} (hij : i ≠ j) (c : F)
    (hι : 3 ≤ Fintype.card ι) :
    SpecialLinearGroup.transvection hij c ∈ commutator (SpecialLinearGroup ι F) := by
  -- a third index `k ∉ {i, j}` exists since `card ι ≥ 3 > 2 ≥ card {i, j}`
  have h2 : (2 : ℕ) < 3 := Nat.lt_succ_of_le (Nat.le_refl 2)
  have hcard2 : ({i, j} : Finset ι).card ≤ 2 :=
    (Finset.card_insert_le i {j}).trans_eq
      (congrArg (fun n : ℕ => n + 1) (Finset.card_singleton j))
  have hcard : ({i, j} : Finset ι).card < (Finset.univ : Finset ι).card :=
    hcard2.trans_lt ((h2.trans_le hι).trans_eq Finset.card_univ.symm)
  obtain ⟨k, _, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hki : k ≠ i := fun h => hk (Eq.subst (motive := fun x => x ∈ ({i, j} : Finset ι)) h.symm
    (Finset.mem_insert_self i {j}))
  have hkj : k ≠ j := fun h => hk (Eq.subst (motive := fun x => x ∈ ({i, j} : Finset ι)) h.symm
    (Finset.mem_insert_of_mem (Finset.mem_singleton_self j)))
  have hcomm : ⁅SpecialLinearGroup.transvection hki.symm c,
      SpecialLinearGroup.transvection hkj (1 : F)⁆ = SpecialLinearGroup.transvection hij c :=
    (commutator_transvection_transvection hij hki.symm hkj.symm c 1).trans
      (congrArg (fun x => SpecialLinearGroup.transvection hij x) (mul_one c))
  exact Eq.subst (motive := fun u => u ∈ commutator (SpecialLinearGroup ι F)) hcomm
    (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))

end BoringMath
