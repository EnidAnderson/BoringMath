/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Data.Finset.Basic

/-!
# Partizan Conway games, rank-bounded encoding

CombinatorialGames ticket #334 (CGT.4). The pin `v4.35.0-rc3` has **no**
Conway game theory at all, so partizan games are built from scratch in the
boring way: a game of **birthday ≤ n + 1** is a pair of finite sets of games
of birthday ≤ n (left and right options). The rank-bounded family is a
structural recursion on `ℕ` (a rank-indexed *inductive* with options
`Finset (PGame n)` is kernel-rejected: nested inductive parameters cannot
mention the constructor-local rank), so still no quotients or well-founded
tricks; options live at strictly smaller rank. The unbounded type is the
sigma over ranks. Comparison (`≤`), surreal numbers, and arithmetic are the
next tickets (#334 onward; consumers: BoringLab games lane #276–#279).

## References
* [Conway] *On Numbers and Games*, ch. 1–3 (games as `{L | R}`).
* [Siegel] *Combinatorial Game Theory*, ch. 1 (birthday/rank encoding).
* Program register: BoringMath #331–#334; BoringLab #100/#107/#129–#133.
-/

namespace BoringMath

-- Reference: [Conway] ch. 1, `{L | R}` with finite option sets, stratified
-- by birthday (the rank-bounded encoding avoids negative occurrences).
/-- A **partizan Conway game of birthday ≤ n + 1**: finite sets of left and
right options, each of birthday ≤ n. -/
def PGame : ℕ → Type
  | 0 => Empty
  | (n + 1) => Finset (PGame n) × Finset (PGame n)

-- Reference: [Conway] ch. 1 (a game is given by its two option sets).
/-- The constructor: from option sets at rank `n`, a game at rank `n + 1`. -/
def PGame.mk (n : ℕ) (leftOptions rightOptions : Finset (PGame n)) : PGame (n + 1) :=
  (leftOptions, rightOptions)

-- Reference: [Conway] ch. 1 (the zero game `0 = { | }`).
/-- The **zero game** `0 = {∅ | ∅}` (definitional). -/
def PGame.zero : PGame 1 :=
  PGame.mk 0 ∅ ∅

-- Reference: [Conway] ch. 1 (the game `1 = {0 | }`).
/-- The game `1 = {0 | }`. -/
def PGame.one : PGame 2 :=
  PGame.mk 1 {PGame.zero} ∅

-- Reference: [Conway] ch. 1 (the game `−1 = { | 0}`).
/-- The game `−1 = { | 0}`. -/
def PGame.negOne : PGame 2 :=
  PGame.mk 1 ∅ {PGame.zero}

-- Reference: [Conway] ch. 1 (a game is determined by its option sets).
/-- The left options of a rank-bounded game. -/
def PGame.leftOptions {n : ℕ} (g : PGame (n + 1)) : Finset (PGame n) :=
  g.1

/-- The right options of a rank-bounded game. -/
def PGame.rightOptions {n : ℕ} (g : PGame (n + 1)) : Finset (PGame n) :=
  g.2

-- Reference: [Barendregt] ch. 2 (eta for inductives).
/-- Eta conversion for rank-bounded games (proved). -/
theorem PGame.eta {n : ℕ} (g : PGame (n + 1)) :
    PGame.mk n (g.leftOptions) (g.rightOptions) = g :=
  rfl

/-- Every rank-bounded game has a birthday (its rank) — the sigma type of all
Conway games. -/
def ConwayGame : Type := Σ n : ℕ, PGame n

end BoringMath
