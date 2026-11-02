/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Data.Fin.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.Perm.Sign

/-!
# The symmetric group `S4` by explicit enumeration

Ticket #167 (G.1.2): `S4 = Equiv.Perm (Fin 4)` as an explicit table of 24
permutations, closed under multiplication and inversion by enumeration; the
five conjugacy classes as data (sizes 1, 6, 8, 6, 3); the sign by inversion
count, multiplicative on the table; the invariant ledger `A4` (the 12 even
permutations) and the Klein four group `V4`, both normal in `S4` by enumeration.

The `Fintype` instance for `Equiv.Perm (Fin 4)` at the pinned Mathlib is
noncomputable (`Equiv.instFintype` uses `Trunc.recOnSubsingleton` in
`Mathlib.Data.Fintype.Perm`), so the table is written explicitly as products of
the adjacent transpositions `s01`, `s12`, `s23`. Each enumeration fact is a
named lemma proved by `rfl` at the kernel (a computable `List.all`/`List.any`
scan over the literal table).

## References
* [Dummit-Foote] D. S. Dummit and R. M. Foote, *Abstract Algebra*, 3rd ed.,
  Wiley, 2004, Chapter 4 (permutation groups; conjugacy classes of `S_n` by
  cycle type; the normal subgroups `A4` and `V4` of `S4` in the exercises).
* [Rotman] J. Rotman, *An Introduction to the Theory of Groups*, 4th ed.,
  Wiley, 2017 (the symmetric group; the sign of a permutation by inversion
  count).
* [Knuth] D. E. Knuth, *The Art of Computer Programming*, Vol. 1, 3rd ed.,
  Section 2.3.1 (lists).
* [Boole] G. Boole, *The Laws of Thought*, 1854 (Boolean implication).
-/

namespace BoringMath.Symmetry

/-! ### The explicit table of 24 permutations -/

-- Reference: [Dummit-Foote], Ch. 4, Sec. 4.1 (transpositions). REVIEW(citation): pin section.
/-- The adjacent transposition `(0 1)` of `Fin 4`. -/
def s01 : Equiv.Perm (Fin 4) := Equiv.swap 0 1

-- Reference: [Dummit-Foote], Ch. 4, Sec. 4.1 (transpositions). REVIEW(citation): pin section.
/-- The adjacent transposition `(1 2)` of `Fin 4`. -/
def s12 : Equiv.Perm (Fin 4) := Equiv.swap 1 2

-- Reference: [Dummit-Foote], Ch. 4, Sec. 4.1 (transpositions). REVIEW(citation): pin section.
/-- The adjacent transposition `(2 3)` of `Fin 4`. -/
def s23 : Equiv.Perm (Fin 4) := Equiv.swap 2 3

-- Reference: [Dummit-Foote], Ch. 4, Sec. 4.3 (class sizes 1,6,8,6,3). REVIEW(citation).
/-- The explicit table of the 24 permutations of `Fin 4`: identity, the six
transpositions, the eight 3-cycles, the six 4-cycles, the three double
transpositions, each a product of `s01`, `s12`, `s23`. -/
def s4Table : List (Equiv.Perm (Fin 4)) :=
  [1, s01, s12, s23, s01 * s12 * s01, s12 * s23 * s12, s01 * s12 * s23 * s12 * s01,
    s01 * s12, s12 * s01, s12 * s23, s23 * s12, s01 * s12 * s01 * s23,
    s01 * s12 * s23 * s12, s01 * s23 * s12 * s01, s12 * s23 * s12 * s01,
    s01 * s12 * s23, s01 * s23 * s12, s12 * s01 * s23, s23 * s12 * s01,
    s01 * s12 * s01 * s23 * s12, s12 * s01 * s23 * s12 * s01, s01 * s23,
    s12 * s01 * s23 * s12, s01 * s12 * s01 * s23 * s12 * s01]

-- Reference: [Dummit-Foote], Ch. 4, Sec. 4.1 (permutation = its values). REVIEW(citation).
/-- A 4-tuple of values in `Fin 4`: the image row `(p 0, p 1, p 2, p 3)` of `p`. -/
abbrev S4Tuple := Fin 4 × Fin 4 × Fin 4 × Fin 4

-- Reference: [Dummit-Foote], Ch. 4, Sec. 4.1. REVIEW(citation): pin section.
/-- The image row `(p 0, p 1, p 2, p 3)` of a permutation of `Fin 4`. -/
def toTab (p : Equiv.Perm (Fin 4)) : S4Tuple := (p 0, p 1, p 2, p 3)

-- Reference: [Dummit-Foote], Ch. 4, Sec. 4.1 (`(p * q) x = p (q x)`). REVIEW(citation).
/-- The image row of a product `p * q`. -/
def mulTab (p q : Equiv.Perm (Fin 4)) : S4Tuple := toTab (p * q)

-- Reference: [Dummit-Foote], Ch. 4, Sec. 4.3 (conjugation `g * p * g⁻¹`). REVIEW(citation).
/-- The image row of the conjugate `g * p * g⁻¹`. -/
def conjTab (g p : Equiv.Perm (Fin 4)) : S4Tuple := toTab (g * p * g⁻¹)

-- Reference: [Dummit-Foote], Ch. 4, Sec. 4.1 (inverses). REVIEW(citation): pin section.
/-- The image row of the inverse `p⁻¹`. -/
def invTab (p : Equiv.Perm (Fin 4)) : S4Tuple := toTab p⁻¹

-- Reference: [Dummit-Foote], Ch. 4, Sec. 4.3 (the 24 elements of `S4`). REVIEW(citation).
/-- The image rows of the 24 table entries, in table order. -/
def s4Tab : List S4Tuple := s4Table.map toTab

-- Reference: [Knuth], Sec. 2.3.1 (membership by scanning a list). REVIEW(citation).
/-- Boolean membership in the image table. -/
def s4Mem (t : S4Tuple) : Bool := s4Tab.any (fun u => u == t)

-- Reference: [Knuth], Sec. 2.3.1 (list scanning). REVIEW(citation): pin section.
/-- Boolean `any` with `==` on a list detects membership. -/
theorem mem_of_any_beq {l : List S4Tuple} {t : S4Tuple} (h : l.any (fun u => u == t) = true) :
    t ∈ l := by
  obtain ⟨u, hu, hut⟩ := List.any_eq_true.mp h
  exact Eq.subst (beq_iff_eq.mp hut) hu

-- Reference: [Knuth], Sec. 2.3.1 (list scanning). REVIEW(citation): pin section.
/-- Membership gives a `true` `any`/`==` scan. -/
theorem any_beq_of_mem {l : List S4Tuple} {t : S4Tuple} (h : t ∈ l) :
    l.any (fun u => u == t) = true :=
  List.any_eq_true.mpr ⟨t, h, beq_iff_eq.mpr rfl⟩

-- Reference: [Boole], Ch. I (implication as `¬a ∨ b`). REVIEW(citation): pin chapter.
/-- Boolean implication: `(!a || b) = true` with `a = true` gives `b = true`. -/
theorem bool_impl {a b : Bool} (h : (!a || b) = true) (ha : a = true) : b = true := by
  rcases Bool.or_eq_true_iff.mp h with hn | hb
  · exfalso
    exact Bool.false_ne_true
      (Eq.subst (motive := fun x => x = true) (Eq.mp (Bool.not_eq_true' a) hn) ha)
  · exact hb

-- Reference: [Knuth], Sec. 2.3.1 (list scanning). REVIEW(citation): pin section.
/-- Boolean membership in the image table is list membership. -/
theorem s4Mem_iff (t : S4Tuple) : s4Mem t = true ↔ t ∈ s4Tab :=
  Iff.trans (List.any_eq_true (p := fun u => u == t) (l := s4Tab))
    (Iff.intro
      (fun h => match h with | ⟨_u, hu, hut⟩ => Eq.subst (beq_iff_eq.mp hut) hu)
      (fun h => ⟨t, h, beq_iff_eq.mpr rfl⟩))

-- Reference: [Dummit-Foote], Ch. 4, Sec. 4.1 (extensionality of `Equiv`). REVIEW(citation).
/-- `toTab` is injective: equal image rows give equal permutations. -/
theorem toTab_injective {p q : Equiv.Perm (Fin 4)} (h : toTab p = toTab q) : p = q := by
  have h0 : p 0 = q 0 := congrArg (fun t => t.1) h
  have h1 : p 1 = q 1 := congrArg (fun t => t.2.1) h
  have h2 : p 2 = q 2 := congrArg (fun t => t.2.2.1) h
  have h3 : p 3 = q 3 := congrArg (fun t => t.2.2.2) h
  refine Equiv.ext ?_
  exact Fin.forall_fin_succ.mpr ⟨h0,
    Fin.forall_fin_succ.mpr ⟨h1,
      Fin.forall_fin_succ.mpr ⟨h2,
        Fin.forall_fin_succ.mpr ⟨h3, fun k => Fin.elim0 k⟩⟩⟩⟩

-- Reference: [Dummit-Foote], Ch. 4, Sec. 4.1 (`|S4| = 4! = 24`). REVIEW(citation).
/-- The table has exactly 24 entries. -/
theorem s4_card : s4Table.length = 24 := rfl

-- Reference: [Dummit-Foote], Ch. 4, Sec. 4.1 (the group table is closed). REVIEW(citation).
-- Enumeration fact: the kernel checks all 24 x 24 = 576 products.
/-- **Closure census**: the image row of every product of two table entries is
in the image table. Proved by `rfl` enumeration. -/
theorem s4_closure_census :
    s4Table.all (fun p => s4Table.all (fun q => s4Mem (mulTab p q))) = true := rfl

-- Reference: [Dummit-Foote], Ch. 4, Sec. 4.1. REVIEW(citation): pin section.
/-- Membership transfer of the closure census. -/
theorem s4_mul_mem_tab (p q : Equiv.Perm (Fin 4)) (hp : p ∈ s4Table) (hq : q ∈ s4Table) :
    s4Mem (mulTab p q) = true :=
  List.all_eq_true.mp (List.all_eq_true.mp s4_closure_census p hp) q hq

-- Reference: [Dummit-Foote], Ch. 4, Sec. 4.1 (`S4` closed under `*`). REVIEW(citation).
/-- **Closure of the table**: the product of two table entries is a table entry. -/
theorem s4_mul_closed (p q : Equiv.Perm (Fin 4)) (hp : p ∈ s4Table) (hq : q ∈ s4Table) :
    p * q ∈ s4Table := by
  have hmem : s4Mem (mulTab p q) = true := s4_mul_mem_tab p q hp hq
  have hu : mulTab p q ∈ s4Tab := (s4Mem_iff (mulTab p q)).mp hmem
  have hu' : mulTab p q ∈ s4Table.map toTab := hu
  obtain ⟨p', hp', h'⟩ := List.mem_map.mp hu'
  exact Eq.subst (toTab_injective h') hp'

-- Reference: [Dummit-Foote], Ch. 4, Sec. 4.1 (inverses in `S4`). REVIEW(citation).
-- Enumeration fact: the kernel checks all 24 inverses.
/-- **Inverse census**: the image row of every inverse of a table entry is in
the image table. Proved by `rfl` enumeration. -/
theorem s4_inv_census : s4Table.all (fun p => s4Mem (invTab p)) = true := rfl

-- Reference: [Dummit-Foote], Ch. 4, Sec. 4.1 (`S4` is closed under inverses). REVIEW(citation).
/-- **Inversion closure of the table**: the inverse of a table entry is a table entry. -/
theorem s4_inv_mem (p : Equiv.Perm (Fin 4)) (hp : p ∈ s4Table) : p⁻¹ ∈ s4Table := by
  have hmem : s4Mem (invTab p) = true := List.all_eq_true.mp s4_inv_census p hp
  have hu : invTab p ∈ s4Tab := (s4Mem_iff (invTab p)).mp hmem
  have hu' : invTab p ∈ s4Table.map toTab := hu
  obtain ⟨p', hp', h'⟩ := List.mem_map.mp hu'
  exact Eq.subst (toTab_injective h') hp'

/-! ### The five conjugacy classes as data -/

-- Reference: [Dummit-Foote], Ch. 4, Sec. 4.3 (the identity class). REVIEW(citation).
/-- The conjugacy class of the identity (size 1), as image rows. -/
def s4ClassId : List S4Tuple := [(0, 1, 2, 3)]

-- Reference: [Dummit-Foote], Ch. 4, Sec. 4.3 (the six transpositions). REVIEW(citation).
/-- The conjugacy class of transpositions (size 6), as image rows. -/
def s4ClassTrans : List S4Tuple :=
  [(1, 0, 2, 3), (0, 2, 1, 3), (0, 1, 3, 2), (2, 1, 0, 3), (0, 3, 2, 1), (3, 1, 2, 0)]

-- Reference: [Dummit-Foote], Ch. 4, Sec. 4.3 (the eight 3-cycles). REVIEW(citation).
/-- The conjugacy class of 3-cycles (size 8), as image rows. -/
def s4Class3Cycle : List S4Tuple :=
  [(1, 2, 0, 3), (2, 0, 1, 3), (0, 2, 3, 1), (0, 3, 1, 2), (2, 1, 3, 0), (1, 3, 2, 0),
    (3, 1, 0, 2), (3, 0, 2, 1)]

-- Reference: [Dummit-Foote], Ch. 4, Sec. 4.3 (the six 4-cycles). REVIEW(citation).
/-- The conjugacy class of 4-cycles (size 6), as image rows. -/
def s4Class4Cycle : List S4Tuple :=
  [(1, 2, 3, 0), (1, 3, 0, 2), (2, 0, 3, 1), (3, 0, 1, 2), (2, 3, 1, 0), (3, 2, 0, 1)]

-- Reference: [Dummit-Foote], Ch. 4, Sec. 4.3 (the three double transpositions). REVIEW(citation).
/-- The conjugacy class of double transpositions (size 3), as image rows. -/
def s4Class22 : List S4Tuple := [(1, 0, 3, 2), (2, 3, 0, 1), (3, 2, 1, 0)]

-- Reference: [Dummit-Foote], Ch. 4, Sec. 4.3 (the five classes of `S4`). REVIEW(citation).
/-- The five conjugacy classes of `S4` as data. -/
def s4Classes : List (List S4Tuple) :=
  [s4ClassId, s4ClassTrans, s4Class3Cycle, s4Class4Cycle, s4Class22]

-- Reference: [Dummit-Foote], Ch. 4, Sec. 4.3 (class sizes 1, 6, 8, 6, 3). REVIEW(citation).
/-- The five conjugacy classes have sizes 1, 6, 8, 6, 3. -/
theorem s4_class_sizes :
    s4ClassId.length = 1 ∧ s4ClassTrans.length = 6 ∧ s4Class3Cycle.length = 8 ∧
      s4Class4Cycle.length = 6 ∧ s4Class22.length = 3 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

-- Reference: [Dummit-Foote], Ch. 4, Sec. 4.3 (classes are subsets of `S4`). REVIEW(citation).
-- Enumeration fact: the kernel checks all 24 class memberships.
/-- **Class subset census**: every class member is in the image table. `rfl`. -/
theorem s4_class_subset_census :
    s4Classes.all (fun c => c.all (fun t => s4Mem t)) = true := rfl

-- Reference: [Dummit-Foote], Ch. 4, Sec. 4.3. REVIEW(citation): pin section.
/-- Every member of every class is a table entry. -/
theorem s4_class_subset (c : List S4Tuple) (hc : c ∈ s4Classes) (t : S4Tuple) (ht : t ∈ c) :
    t ∈ s4Tab :=
  (s4Mem_iff t).mp (List.all_eq_true.mp (List.all_eq_true.mp s4_class_subset_census c hc) t ht)

-- Reference: [Dummit-Foote], Ch. 4, Sec. 4.3 (the classes partition `S4`). REVIEW(citation).
-- Enumeration fact: for each of the 24 rows the kernel counts exactly one class.
/-- **Class partition census**: every image row lies in exactly one class. `rfl`. -/
theorem s4_class_count_census :
    s4Tab.all (fun t =>
      (s4Classes.filter (fun c => c.any (fun u => u == t))).length == 1) = true :=
  rfl

-- Reference: [Dummit-Foote], Ch. 4, Sec. 4.3 (the classes partition `S4`). REVIEW(citation).
/-- **The classes partition the table**: every table row lies in a unique class. -/
theorem s4_class_unique (t : S4Tuple) (ht : t ∈ s4Tab) :
    ∃ c, c ∈ s4Classes ∧ t ∈ c ∧ ∀ c2, c2 ∈ s4Classes → t ∈ c2 → c2 = c := by
  have hlen : (s4Classes.filter (fun c => c.any (fun u => u == t))).length = 1 :=
    beq_iff_eq.mp (List.all_eq_true.mp s4_class_count_census t ht)
  obtain ⟨c, hc⟩ := List.length_eq_one_iff.mp hlen
  have hcMem : c ∈ s4Classes.filter (fun c => c.any (fun u => u == t)) :=
    Eq.subst (motive := fun L => c ∈ L) hc.symm (List.mem_singleton_self c)
  obtain ⟨hcmem, hcany⟩ := List.mem_filter.mp hcMem
  refine ⟨c, hcmem, mem_of_any_beq hcany, ?_⟩
  intro c2 hc2 ht2
  have h2 : c2 ∈ s4Classes.filter (fun c => c.any (fun u => u == t)) :=
    List.mem_filter.mpr ⟨hc2, any_beq_of_mem ht2⟩
  exact List.mem_singleton.mp (Eq.subst (motive := fun L => c2 ∈ L) hc h2)

-- Reference: [Dummit-Foote], Ch. 4, Sec. 4.3 (conjugation preserves cycle type). REVIEW(citation).
-- Enumeration fact: the kernel checks all 24 x 24 conjugations against all 5 classes.
/-- **Conjugation census**: if a table entry `p` lies in a class `c`, then so
does `g * p * g⁻¹` for every table entry `g`. Proved by `rfl` enumeration. -/
theorem s4_conj_census :
    s4Table.all (fun g => s4Table.all (fun p => s4Classes.all (fun c =>
      (!(c.any (fun u => u == toTab p))) || c.any (fun u => u == conjTab g p)))) = true :=
  rfl

-- Reference: [Dummit-Foote], Ch. 4, Sec. 4.3 (classes are conjugacy-stable). REVIEW(citation).
/-- **Each class is a conjugacy class**: conjugating a table entry by a table
entry stays in the same class. -/
theorem s4_conj_class (g p : Equiv.Perm (Fin 4)) (hg : g ∈ s4Table) (hp : p ∈ s4Table)
    (c : List S4Tuple) (hc : c ∈ s4Classes) (h : toTab p ∈ c) :
    conjTab g p ∈ c :=
  mem_of_any_beq (bool_impl
    (List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp s4_conj_census g hg) p hp) c hc)
    (any_beq_of_mem h))

/-! ### The sign by inversion count -/

-- Reference: [Rotman], Ch. 2 (sign = `(-1)^(inversions)`). REVIEW(citation): pin theorem.
/-- The inversion count of an image row `(a, b, c, d)`: the number of pairs
`i < j` with `t i > t j`. -/
def invCount (t : S4Tuple) : Nat :=
  (if t.1 > t.2.1 then 1 else 0) + (if t.1 > t.2.2.1 then 1 else 0) +
    (if t.1 > t.2.2.2 then 1 else 0) + (if t.2.1 > t.2.2.1 then 1 else 0) +
    (if t.2.1 > t.2.2.2 then 1 else 0) + (if t.2.2.1 > t.2.2.2 then 1 else 0)

-- Reference: [Rotman], Ch. 2 (sign by inversion count). REVIEW(citation): pin theorem.
/-- The sign of an image row by inversion count: `(-1) ^ invCount t`. -/
def signOf (t : S4Tuple) : ℤ := (-1) ^ invCount t

-- Reference: [Rotman], Ch. 2 (sign is multiplicative). REVIEW(citation): pin theorem.
-- Enumeration fact: the kernel checks all 24 x 24 = 576 sign products.
/-- **Sign census**: the inversion-count sign is multiplicative on all pairs of
table entries. Proved by `rfl` enumeration. -/
theorem sign_mul_census :
    s4Table.all (fun p => s4Table.all (fun q =>
      signOf (mulTab p q) == signOf (toTab p) * signOf (toTab q))) = true :=
  rfl

-- Reference: [Rotman], Ch. 2 (the sign is a homomorphism). REVIEW(citation).
/-- **Sign multiplicativity on the table**: `signOf (mulTab p q) =
signOf (toTab p) * signOf (toTab q)` for table entries `p`, `q`. -/
theorem sign_mul_table (p q : Equiv.Perm (Fin 4)) (hp : p ∈ s4Table) (hq : q ∈ s4Table) :
    signOf (mulTab p q) = signOf (toTab p) * signOf (toTab q) :=
  beq_iff_eq.mp (List.all_eq_true.mp (List.all_eq_true.mp sign_mul_census p hp) q hq)

-- Reference: [Dummit-Foote], Ch. 4, Sec. 4.3 (one representative per class). REVIEW(citation).
/-- A documented sample of 20 pairs: one representative of each of the five
classes, paired with each of the first four table entries. -/
def signSample : List (Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4)) :=
  [(1, 1), (1, s01), (1, s12), (1, s23), (s01, 1), (s01, s01), (s01, s12), (s01, s23),
    (s01 * s12, 1), (s01 * s12, s01), (s01 * s12, s12), (s01 * s12, s23),
    (s01 * s12 * s23, 1), (s01 * s12 * s23, s01), (s01 * s12 * s23, s12),
    (s01 * s12 * s23, s23), (s01 * s23, 1), (s01 * s23, s01), (s01 * s23, s12),
    (s01 * s23, s23)]

-- Reference: [Rotman], Ch. 2 (sign multiplicativity on the sample). REVIEW(citation).
-- Enumeration fact: the kernel checks the 20 sampled pairs.
/-- **Sampled sign census**: sign is multiplicative on the 20 sample pairs. `rfl`. -/
theorem sign_mul_sampled_census :
    signSample.all (fun pq =>
      signOf (mulTab pq.1 pq.2) == signOf (toTab pq.1) * signOf (toTab pq.2)) = true :=
  rfl

-- Reference: [Rotman], Ch. 2 (sign multiplicativity on the sample). REVIEW(citation).
/-- **Sign multiplicativity on a sampled set of pairs** (ticket #167 (c)): the
inversion-count sign is multiplicative on each of the 20 sampled pairs. The
full 24 x 24 census is `sign_mul_table`. -/
theorem sign_mul_sampled (pq : Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4)) (h : pq ∈ signSample) :
    signOf (mulTab pq.1 pq.2) = signOf (toTab pq.1) * signOf (toTab pq.2) :=
  beq_iff_eq.mp (List.all_eq_true.mp sign_mul_sampled_census pq h)

/-! ### The invariant ledger: `A4` and `V4` -/

-- Reference: [Dummit-Foote], Ch. 4 exercises (`A4` = even perms, order 12). REVIEW(citation).
/-- The even permutations of the table (`A4`, 12 elements) as image rows. -/
def a4Tab : List S4Tuple := s4Tab.filter (fun t => signOf t == 1)

-- Reference: [Dummit-Foote], Ch. 4 exercises (`|A4| = 12`). REVIEW(citation).
/-- `A4` has exactly 12 elements. -/
theorem a4_card : a4Tab.length = 12 := rfl

-- Reference: [Dummit-Foote], Ch. 4 exercises (`A4` is the even permutations). REVIEW(citation).
/-- Every member of `a4Tab` has sign `1`. -/
theorem a4_even (t : S4Tuple) (h : t ∈ a4Tab) : signOf t = 1 :=
  beq_iff_eq.mp (List.mem_filter.mp h).2

-- Reference: [Dummit-Foote], Ch. 4 exercises (`A4` subset of `S4`). REVIEW(citation).
/-- Every member of `a4Tab` is a table entry. -/
theorem a4_sub_tab (t : S4Tuple) (h : t ∈ a4Tab) : t ∈ s4Tab :=
  (List.mem_filter.mp h).1

-- Reference: [Dummit-Foote], Ch. 4 exercises (conjugation preserves sign). REVIEW(citation).
-- Enumeration fact: the kernel checks all 24 x 24 conjugations.
/-- **`A4` conjugation census**: conjugating a sign-`1` table entry by a table
entry keeps sign `1`. Proved by `rfl` enumeration. -/
theorem a4_conj_census :
    s4Table.all (fun g => s4Table.all (fun p =>
      (!(signOf (toTab p) == 1)) || (signOf (conjTab g p) == 1))) = true :=
  rfl

-- Reference: [Dummit-Foote], Ch. 4 exercises (conjugation preserves sign). REVIEW(citation).
/-- Conjugation by a table entry preserves sign `1`. -/
theorem a4_conj_sign (g p : Equiv.Perm (Fin 4)) (hg : g ∈ s4Table) (hp : p ∈ s4Table)
    (h : signOf (toTab p) = 1) : signOf (conjTab g p) = 1 :=
  beq_iff_eq.mp (bool_impl (List.all_eq_true.mp (List.all_eq_true.mp a4_conj_census g hg) p hp)
    (beq_iff_eq.mpr h))

-- Reference: [Dummit-Foote], Ch. 4 exercises (`A4` normal in `S4`). REVIEW(citation).
/-- **Normality of `A4` in the enumerated `S4`**: conjugating a table entry
whose image row lies in `a4Tab` by a table entry stays in `a4Tab`. -/
theorem a4_normal (g p : Equiv.Perm (Fin 4)) (hg : g ∈ s4Table) (hp : p ∈ s4Table)
    (h : toTab p ∈ a4Tab) : conjTab g p ∈ a4Tab := by
  have hmem : conjTab g p ∈ s4Tab := by
    have h2 : g * p ∈ s4Table := s4_mul_closed g p hg hp
    have h3 : g⁻¹ ∈ s4Table := s4_inv_mem g hg
    have h4 : (g * p) * g⁻¹ ∈ s4Table := s4_mul_closed (g * p) g⁻¹ h2 h3
    exact List.mem_map.mpr ⟨g * p * g⁻¹, h4, rfl⟩
  have hsign : signOf (conjTab g p) = 1 := a4_conj_sign g p hg hp (a4_even (toTab p) h)
  exact List.mem_filter.mpr ⟨hmem, beq_iff_eq.mpr hsign⟩

-- Reference: [Dummit-Foote], Ch. 4 exercises (`V4` normal in `S4`, order 4). REVIEW(citation).
/-- The Klein four subgroup `V4` of `S4` as image rows: identity and the three
double transpositions. -/
def v4Tab : List S4Tuple := [(0, 1, 2, 3), (1, 0, 3, 2), (2, 3, 0, 1), (3, 2, 1, 0)]

-- Reference: [Dummit-Foote], Ch. 4 exercises (`|V4| = 4`). REVIEW(citation).
/-- `V4` has exactly 4 elements. -/
theorem v4_card : v4Tab.length = 4 := rfl

-- Reference: [Dummit-Foote], Ch. 4 exercises (`V4` subset of `A4`). REVIEW(citation).
-- Enumeration fact: the kernel checks the 4 signs.
/-- **V4 even census**: every member of `V4` has sign `1`. Proved by `rfl`. -/
theorem v4_even_census : v4Tab.all (fun t => signOf t == 1) = true := rfl

-- Reference: [Dummit-Foote], Ch. 4 exercises (`V4` subset of `A4`). REVIEW(citation).
/-- Every member of `V4` is even (sign `1`). -/
theorem v4_even (t : S4Tuple) (h : t ∈ v4Tab) : signOf t = 1 :=
  beq_iff_eq.mp (List.all_eq_true.mp v4_even_census t h)

-- Reference: [Dummit-Foote], Ch. 4 exercises (`V4` normal in `S4`). REVIEW(citation).
-- Enumeration fact: the kernel checks all 24 x 24 conjugations against `V4`.
/-- **`V4` conjugation census**: if a table entry `p` lies in `v4Tab`, so does
`g * p * g⁻¹` for every table entry `g`. Proved by `rfl` enumeration. -/
theorem v4_conj_census :
    s4Table.all (fun g => s4Table.all (fun p =>
      (!(v4Tab.any (fun u => u == toTab p))) || v4Tab.any (fun u => u == conjTab g p))) = true :=
  rfl

-- Reference: [Dummit-Foote], Ch. 4 exercises (`V4` normal in `S4`). REVIEW(citation).
/-- **Normality of the Klein four group `V4` in the enumerated `S4`**:
conjugating a table entry whose image row lies in `v4Tab` by a table entry
stays in `v4Tab`. -/
theorem v4_normal (g p : Equiv.Perm (Fin 4)) (hg : g ∈ s4Table) (hp : p ∈ s4Table)
    (h : toTab p ∈ v4Tab) : conjTab g p ∈ v4Tab :=
  mem_of_any_beq (bool_impl (List.all_eq_true.mp (List.all_eq_true.mp v4_conj_census g hg) p hp)
    (any_beq_of_mem h))

end BoringMath.Symmetry
