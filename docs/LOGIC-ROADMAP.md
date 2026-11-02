# Logic roadmap — BoringMath/Logic/ (tickets #538–#541, proposed #335–#338)

Pin audit (mathlib v4.35.0-rc3): `Logic/` and a rich `ModelTheory/` (incl.
`ModelTheory/Complexity`), plus `Computability/` (Turing machines,
partial recursive functions). MISSING: proof theory (sequent calculus, cut
elimination), ludics/designs, and the complexity↔computability bridge.

## Ticket tree

- **#538** `Logic/ProofTheory/Sequent.lean` — SEED LANDED: `Sequent`,
  `SequentCalculus`, `cut_elimination` (Gentzen's Hauptsatz, sorry with
  plan). Home of #335.
- **#539** `Logic/Computability/Bridge.lean` — SEED LANDED:
  `DTIME_decidable` (every `DTIME t` language has a total computable
  characteristic function; sorry with plan via pin's `ToPartrec`).
  Feeds #302–#304 (Cook–Levin spine) and #339–#342.
- **#540** #336: cut-elimination consequences — consistency of arithmetic
  (Gentzen), interpolation (statement layer).
- **#541** #337–#338: ludics/designs and the games-ludics row #279
  (statement layer; docks BoringLab `Games/`).

## References
* [Gentzen 1935]; [Takeuti], ch. 1; [Girard] J.-Y. Girard, *Ludics* (1999);
  [Arora–Barak], ch. 1–2; [Sipser], ch. 7.
* mathlib pin v4.35.0-rc3: `ModelTheory`, `Computability.Partrec`,
  `Computability.Halting`; BoringMath pin: `Complexity.Defs` (#301).
