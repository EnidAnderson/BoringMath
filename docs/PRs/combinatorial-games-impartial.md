# PR note — CombinatorialGames impartial gaps (#462, #464 + outcome N-criterion)

## Statement
`BoringMath/CombinatorialGames/` (Mex, Impartial, Outcome, Sum, Partizan) landed as
API, but three main results were missing or sorried. This candidate adds:

- `ImpartialGame.exists_move_grundy_eq_of_lt` (#462): every `m < G.grundy p` is
  attained by an option (`Impartial.lean`).
- `ImpartialGame.outcome_eq_n_iff` (Outcome.lean): N-position iff some option is
  a P-position.
- `ImpartialGame.outcome_sum_eq_p_iff` (#464, Sum.lean): `G + H` is a
  P-position at `(a, b)` iff `G.grundy a = H.grundy b` — advertised in the
  module docstring but previously unstated. Proved from
  `outcome_eq_p_iff_grundy_eq_zero` + `grundy_sum` (still the sanctioned sorry,
  ticket #463) + `nimSum_eq_zero_iff`.

Still open in the same lane: #463 (xor theorem proof), #465 (multi-heap Nim /
Bouton), #466–#469 (partizan order/outcome/arithmetic/surreals) — see
`docs/TICKET-REGISTER.md`, GitHub issues #372–#377, #387–#388.

## Literature
* [Sprague] 1935; [Grundy] 1939; [Conway] *On Numbers and Games* ch. 3;
  [Berlekamp–Conway–Guy] vol. 1 ch. 2; [Bouton] 1901.

## Where it would live in Mathlib
`Mathlib/SetTheory/Game/` is absent at pin v4.35.0-rc3; these would be new
modules there (or `Mathlib/Combinatorics/Game/`).

## Does Mathlib already have it?
No CGT at the pin (audited: `PGame`, `Nimber`, `surreal` — 0 hits).

## Review notes
Build: `lake build BoringMath.CombinatorialGames.Sum` exit 0; only pre-existing
warnings (Mex auxLemma, openClassical at Outcome.lean:27 / Sum.lean:29) plus
the sanctioned `grundy_sum` sorry remain. Style backstop clean for the new
declarations.
