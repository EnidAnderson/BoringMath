/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Nat.Find

/-!
# The mex (minimum excluded value) of a finite set of naturals

CombinatorialGames ticket #343 (seed). The pin `v4.35.0-rc3` has no Conway
game theory (`SetTheory/Game` is absent at this pin) and no `mex`; the
Sprague–Grundy theory of impartial games (#343–#346, consumers in
`BoringLab/Games`) is built from the mex of the Grundy values of the options.
This module defines `mex` on finsets and proves its two characterizing
properties.

## References
* [Conway] *On Numbers and Games*, 1976, ch. 3 (mex in the definition of
  surreal numbers / Grundy values).
* [Bouton] 1901 (Nim; the xor of heap sizes is the Grundy value) — the
  Sprague–Grundy theorem's first instance.
* mathlib pin v4.35.0-rc3: `Nat.find`, `Nat.find_spec`, `Nat.find_min`,
  `Finset.le_sup`, `Nat.lt_succ_of_le`, `Nat.lt_irrefl`.
* Program register: BoringMath #343–#346; BoringLab #276–#279.
-/

namespace BoringMath

-- Reference: [Conway] ch. 3 (the simplest number not in the set of options).
/-- The **mex** of a finite set of naturals: the least natural not in `s`.
Existence: `s.sup id + 1 ∉ s`. -/
def mex (s : Finset ℕ) : ℕ :=
  Nat.find (p := fun n => n ∉ s) ⟨s.sup id + 1, fun h =>
    Nat.lt_irrefl _ (Nat.lt_succ_of_le (Finset.le_sup (f := id) h))⟩

-- Reference: mathlib pin v4.35.0-rc3, `Nat.find_spec`.
/-- The mex is not a member of the set (proved). -/
theorem mex_not_mem (s : Finset ℕ) : mex s ∉ s :=
  Nat.find_spec (mex._proof_1 s)

-- Reference: mathlib pin v4.35.0-rc3, `Nat.find_min`.
/-- Every natural below the mex is a member of the set (proved). -/
theorem mem_of_lt_mex {s : Finset ℕ} {n : ℕ} (h : n < mex s) : n ∈ s :=
  not_not.mp (Nat.find_min (mex._proof_1 s) h)

-- Reference: [Conway] ch. 3; uniqueness of the least excluded value.
/-- The mex is uniquely characterized by the two properties above (proved). -/
theorem mex_eq_of_not_mem_and_forall {s : Finset ℕ} {m : ℕ}
    (h0 : m ∉ s) (h1 : ∀ n, n < m → n ∈ s) : mex s = m :=
  Nat.le_antisymm
    (Nat.find_min' ⟨s.sup id + 1, fun h =>
      Nat.lt_irrefl _ (Nat.lt_succ_of_le (Finset.le_sup (f := id) h))⟩ h0)
    (Nat.le_of_not_lt fun h => absurd (h1 _ h) (mex_not_mem s))

-- Reference: [Bouton] 1901; the nim-sum (xor) is the Grundy value of Nim.
/-- The **nim-sum** of two naturals (bitwise xor) — the operation behind the
Sprague–Grundy value of a disjoint sum of Nim heaps. -/
def nimSum (a b : ℕ) : ℕ := a ^^^ b

end BoringMath
