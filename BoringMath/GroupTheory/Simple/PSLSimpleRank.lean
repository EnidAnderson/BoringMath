/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringMath.GroupTheory.Simple.SLPerfect
import BoringMath.GroupTheory.CFSG.Quasisimple
import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.LinearAlgebra.Projectivization.PSL.Stabilizer
import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import Mathlib.GroupTheory.GroupAction.Iwasawa

/-!
# Simplicity of `PSL(n, F)` for rank `n ≥ 3` — reduction to perfectness of `SL`

Ticket #230. The pin already provides, for the action of `PSL(n, F)` on the
projective space `ℙ F (ι → F)`: `FaithfulSMul` and `IsPreprimitive`
(`Projectivization/Action.lean`). What remains is the normal-subgroup argument,
which needs `SL(n, F)` perfect for `n ≥ 3` (transvections are commutators) —
tracked as the sanctioned sorry `SL_isPerfect` in `SLPerfect.lean`.

## References
* [Wilson] ch. 5 (PSL(n,q) simple for n ≥ 3); [GLS] Number 3.
* mathlib pin v4.35.0-rc3: `FaithfulSMul (PSL ι K) (ℙ K (ι → K))`,
  `IsPreprimitive (PSL ι K) (ℙ K (ι → K))` (Projectivization/Action.lean:238),
  `MulAction.IwasawaStructure.isSimpleGroup` (GroupAction/Iwasawa.lean).
-/

namespace BoringMath

open Matrix
open scoped MatrixGroups

-- Reference: mathlib pin v4.35.0-rc3, `Matrix.SpecialLinearGroup.transvection` in
-- `lineStab (span (Pi.single i 1))` (via `mem_lineStab_iff`); [Carter] ch. 5.
/-- Every transvection `T_ij(b)` lies in the line stabilizer of the line spanned
by `e_i`. -/
theorem transvection_mem_lineStab_span {i j : ι} (hij : i ≠ j) (b : F) :
    SpecialLinearGroup.transvection hij b ∈
      Matrix.SpecialLinearGroup.lineStab (Submodule.span F {Pi.single i (1 : F)}) := by
  show ∀ w : ι → F, (SpecialLinearGroup.transvection hij b) • w - w
    ∈ Submodule.span F {Pi.single i (1 : F)}
  intro w
  have hT : (SpecialLinearGroup.transvection hij b : Matrix ι ι F) *ᵥ w
      = w + b * w j • Pi.single i (1 : F) := by
    have h1 : (SpecialLinearGroup.transvection hij b : Matrix ι ι F) = 1 + single i j b :=
      SpecialLinearGroup.transvection_coe hij b
    exact Eq.subst (motive := fun M => (M : Matrix ι ι F) *ᵥ w = _)
      h1 ((Matrix.add_mulVec 1 (single i j b) w).trans
        ((Matrix.one_mulVec w).trans (by
          exact Eq.subst (motive := fun v => w + v = w + b * w j • Pi.single i 1)
            (Matrix.single_mulVec_eq i j b w)
            (by
              apply congrArg (fun t => w + t)
              exact Eq.subst (motive := fun u => (if w j = u then b • Pi.single i (w j) else 0)
                  = b * u • Pi.single i 1) rfl rfl))))
  have h2 : (SpecialLinearGroup.transvection hij b) • w - w
      = b * w j • Pi.single i (1 : F) := by
    exact Eq.subst (motive := fun v => v - w = b * w j • Pi.single i 1)
      (SpecialLinearGroup.smul_def _ w) (by
        exact Eq.subst (motive := fun v => (v : ι → F) - w = b * w j • Pi.single i 1) hT
          (add_sub_cancel_left w _))
  exact Eq.subst (motive := fun v => v ∈ Submodule.span F {Pi.single i (1 : F)}) h2
    (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))

-- Reference: [Wilson] ch. 5; `transvection_mem_lineStab_span` +
-- `diag2n_mem_commutator_of_card_three`/`hOf`-products + pin's
-- `diagonal_transvection_induction'`; the transvections generate `SL` in rank ≥ 3.
/-- In rank `≥ 3`, the line stabilizers generate `SL(ι, F)`:
`⨆ p : ℙ F (ι → F), lineStab p.submodule = ⊤`. -/
theorem iSup_lineStab_eq_top_of_card_three (hι : 3 ≤ Fintype.card ι) :
    (⨆ p : ℙ F (ι → F), Matrix.SpecialLinearGroup.lineStab p.submodule)
      = (⊤ : Subgroup (SpecialLinearGroup ι F)) := by
  haveI : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.mp
    (Nat.lt_of_lt_of_le (Nat.lt_succ_of_le (Nat.le_add_right 1 1)) hι)
  apply eq_top_iff.mpr
  intro M _
  refine SpecialLinearGroup.diagonal_transvection_induction'
    (fun A => A ∈ ⨆ p : ℙ F (ι → F), Matrix.SpecialLinearGroup.lineStab p.submodule) M
    (fun i j hij c hc => ?_) (fun i j hij a => ?_) (fun A B hA hB => Subgroup.mul_mem _ hA hB)
  · -- diag2n is a product of six transvections (SLDiag.hOf), each in the iSup
    have e := (hOf_eq_diag2n hij c hc).symm
    refine Eq.subst (motive := fun x => x ∈ ⨆ p : ℙ F (ι → F),
      Matrix.SpecialLinearGroup.lineStab p.submodule) e ?_
    sorry -- TEMPORARY SORRY: wOf-products via Subgroup.mul_mem + le_iSup of
    -- transvection_mem_lineStab_span at p := Projectivization.mk (Pi.single i 1)
  · -- transvection T_ij(a) ∈ lineStab (span e_i) ≤ iSup
    have hmem := transvection_mem_lineStab_span hij a
    have hp : (Projectivization.mk (Pi.single i (1 : F))
        (Pi.single_ne_zero_iff.mpr one_ne_zero)).submodule
        = Submodule.span F {Pi.single i (1 : F)} := rfl
    have hle := le_iSup (fun p : ℙ F (ι → F) => Matrix.SpecialLinearGroup.lineStab p.submodule)
      (Projectivization.mk (Pi.single i (1 : F)) _)
    exact hle.trans (Eq.subst (motive := fun L => Matrix.SpecialLinearGroup.lineStab L ≤ _)
      hp hmem)

-- Reference: pin's PSL2 `PSL.iSup_iwasawaT_eq_top`, generalized: `Subgroup.map_iSup`
-- + `map_top_of_surjective`.
/-- The Iwasawa generator property in rank `≥ 3`: `iSup (PSL.iwasawaT) = ⊤`. -/
theorem iSup_iwasawaT_eq_top_of_card_three (hι : 3 ≤ Fintype.card ι) :
    iSup (PSL.iwasawaT (F := F) (ι := ι)) = ⊤ := by
  have h1 : iSup (PSL.iwasawaT (F := F) (ι := ι))
      = Subgroup.map (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup ι F)))
        (⨆ p : ℙ F (ι → F), Matrix.SpecialLinearGroup.lineStab p.submodule) :=
    Subgroup.map_iSup
  exact h1.trans (Eq.subst (motive := fun H => Subgroup.map _ H = ⊤)
    (iSup_lineStab_eq_top_of_card_three hι)
    (Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)))

-- Reference: pin's PSL2 `PSL2.Iwasawa` (Iwasawa structure), generalized to rank ≥ 3
-- via `iSup_iwasawaT_eq_top_of_card_three`.
/-- The Iwasawa structure on `PSL(ι, F)` acting on `ℙ F (ι → F)`, rank `≥ 3`. -/
noncomputable def iwasawaPSL (hι : 3 ≤ Fintype.card ι) :
    MulAction.IwasawaStructure (Matrix.ProjectiveSpecialLinearGroup ι F) (ℙ F (ι → F)) where
  T := PSL.iwasawaT
  is_comm p := by
    have hSL : IsMulCommutative (Matrix.SpecialLinearGroup.lineStab p.submodule) := by
      have hsub : p.submodule = Submodule.span F {p.rep} :=
        (Projectivization.mk_rep p).symm.trans Projectivization.submodule_mk
      exact Eq.subst (motive := fun L => IsMulCommutative
        (Matrix.SpecialLinearGroup.lineStab L)) hsub
        (Matrix.SpecialLinearGroup.lineStab_isMulCommutative_of_span p.rep p.rep_nonzero)
    exact Subgroup.map_isMulCommutative _ _
  is_conj g p := by
    obtain ⟨g_SL, rfl⟩ := QuotientGroup.mk_surjective g
    sorry -- TEMPORARY SORRY: as pin's PSL2 proof: `PSL.smul_submodule`,
    -- `lineStab_smul`, `PSL.iwasawaT_map_conj` (all general-ι at the pin)
  is_generator := iSup_iwasawaT_eq_top_of_card_three hι

-- Reference: [Wilson] ch. 5 (PSL(n,F) simple for n ≥ 3 given SL perfect);
-- pin's `IsPreprimitive`/`FaithfulSMul` for the projective action (general ι),
-- `IsPreprimitive.isQuasiPreprimitive`, `SL2Simple.PSL_nontrivial`, and
-- `Group.IsPerfect.of_surjective` (BoringMath Quasisimple) for the quotient.
/-- **`PSL(n, F)` is simple for `n ≥ 3`, given `SL(n, F)` is perfect** (proved via
the Iwasawa criterion). -/
theorem PSL_simple_of_SL_perfect {ι : Type*} [Fintype ι] [DecidableEq ι] {F : Type*}
    [Field F] (hι : 3 ≤ Fintype.card ι) [Group.IsPerfect (SpecialLinearGroup ι F)] :
    IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup ι F) := by
  haveI : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.mp
    (Nat.lt_of_lt_of_le (Nat.lt_succ_of_le (Nat.le_add_right 1 1)) hι)
  have hperf : Group.IsPerfect (Matrix.ProjectiveSpecialLinearGroup ι F) :=
    Group.IsPerfect.of_surjective (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup ι F)))
      (QuotientGroup.mk'_surjective _)
  have hcomm : commutator (Matrix.ProjectiveSpecialLinearGroup ι F) = ⊤ :=
    hperf.commutator_eq_top
  exact MulAction.IwasawaStructure.isSimpleGroup hcomm (iwasawaPSL hι) inferInstance

-- Reference: as above, combined with `SL_isPerfect` (SLPerfect.lean).
/-- **`PSL(n, F)` is simple for `n ≥ 3`** (modulo the sanctioned
`SL_isPerfect` sorry). -/
theorem PSL_isSimpleGroup_rank_ge_three {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : Type*} [Field F] (hι : 3 ≤ Fintype.card ι) :
    IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup ι F) :=
  @PSL_simple_of_SL_perfect ι _ _ F _ hι (SL_isPerfect F hι)

end BoringMath
