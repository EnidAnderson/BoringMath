/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# The linear groups `GL`, `SL`, `PGL` over finite fields (house naming)

AlgebraicGroups ticket #321 (seed). The pin `v4.35.0-rc3` has no linear
algebraic group theory as such, but it carries the matrix groups
`GL n R`, `SpecialLinearGroup n R`, `PGL(n, R)` with their cardinals over
finite fields and their centers; this module restates the load-bearing facts
in house naming for the Lie-type sector of the CFSG (#251–#253), where
`|GL(n,q)|`, `|SL(n,q)|`, and the centers (scalar matrices; `n`-th roots of
unity for `SL`) feed the order formulas and the simplicity arguments for
`PSL(n,q)`.

## References
* mathlib pin v4.35.0-rc3: `Matrix.card_GL_field`, `Matrix.card_SL_field`,
  `Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar`,
  `Matrix.SpecialLinearGroup.mem_center_iff`, `Matrix.PGL` (`mk`, `ker_mk`,
  `mk_surjective`).
* [Wilson] ch. 3 (orders of GL/SL over finite fields; centers).
* [Carter] GTM 251, ch. 7–8 (Chevalley groups; `PSL` as `SL`/center).
* Program register: BoringMath #251–#253, #321–#326.
-/

namespace BoringMath

open scoped MatrixGroups

variable {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽]

-- Reference: mathlib pin v4.35.0-rc3, `Matrix.card_GL_field`; [Wilson] ch. 3.
/-- **Order of `GL(n, q)`**: `∏_{i < n} (q^n − q^i)` (proved). -/
theorem card_GL_finiteField (n : ℕ) :
    Nat.card (Matrix.GeneralLinearGroup (Fin n) 𝔽) =
      ∏ i : Fin n, (Fintype.card 𝔽 ^ n - Fintype.card 𝔽 ^ (i : ℕ)) :=
  Matrix.card_GL_field n

-- Reference: mathlib pin v4.35.0-rc3, `Matrix.card_SL_field`; [Wilson] ch. 3.
/-- **Order of `SL(n, q)`**: `(∏_{i < n} (q^n − q^i)) / (q − 1)` (proved). -/
theorem card_SL_finiteField (n : ℕ) [NeZero n] :
    Nat.card (Matrix.SpecialLinearGroup (Fin n) 𝔽) =
      (∏ i : Fin n, (Fintype.card 𝔽 ^ n - Fintype.card 𝔽 ^ (i : ℕ))) /
        (Fintype.card 𝔽 - 1) :=
  Matrix.card_SL_field n

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]

-- Reference: mathlib pin v4.35.0-rc3,
-- `Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar`;
-- [Wilson] ch. 3 (center of GL = scalar matrices).
/-- The center of `GL(n, R)` consists of the scalar matrices (proved). -/
theorem mem_center_GL_iff (g : Matrix.GeneralLinearGroup n R) :
    g ∈ Subgroup.center (Matrix.GeneralLinearGroup n R) ↔
      g.val ∈ Set.range (Matrix.scalar n) :=
  Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar

-- Reference: mathlib pin v4.35.0-rc3, `Matrix.SpecialLinearGroup.mem_center_iff`;
-- [Carter] ch. 7 (center of SL = scalar matrices with scalar an n-th root of
-- unity).
/-- The center of `SL(n, R)` is the scalar matrices whose scalar is an
`n`-th root of unity (proved). -/
theorem mem_center_SL_iff {A : Matrix.SpecialLinearGroup n R} :
    A ∈ Subgroup.center (Matrix.SpecialLinearGroup n R) ↔
      ∃ r : R, r ^ (Fintype.card n) = 1 ∧ Matrix.scalar n r = A :=
  Matrix.SpecialLinearGroup.mem_center_iff

-- Reference: mathlib pin v4.35.0-rc3, `Matrix.ProjGenLinGroup.mk_surjective` and
-- `Matrix.ProjGenLinGroup.ker_mk`; [Carter] ch. 7 (`PGL = GL`/center).
/-- The projection `GL(n, R) →* PGL(n, R)` is surjective with kernel the
center (scalar matrices) (proved). -/
theorem pgl_mk_surjective :
    Function.Surjective (Matrix.ProjGenLinGroup.mk : Matrix.GeneralLinearGroup n R →* PGL(n, R)) :=
  Matrix.ProjGenLinGroup.mk_surjective

/-- The kernel of `GL(n, R) →* PGL(n, R)` is the center (proved). -/
theorem pgl_ker_mk :
    (Matrix.ProjGenLinGroup.mk : Matrix.GeneralLinearGroup n R →* PGL(n, R)).ker =
      Subgroup.center (Matrix.GeneralLinearGroup n R) :=
  Matrix.ProjGenLinGroup.ker_mk

end BoringMath
