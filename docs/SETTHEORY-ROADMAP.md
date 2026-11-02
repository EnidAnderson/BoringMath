# Set theory roadmap — BoringMath/SetTheory/ (tickets #534–#537, proposed #331–#334)

Pin audit (mathlib v4.35.0-rc3): `SetTheory/` has ZFC/PSet, ordinals,
cardinals, and a thin `Descriptive/` (tree API only). MISSING: forcing,
Boolean-valued models, independence; the descriptive hierarchy (Borel/
analytic sets, perfect set theorem).

## Ticket tree

- **#534** `SetTheory/Forcing/Basic.lean` — SEED LANDED: `Incompatible`,
  `IsForcingNotion`, `IsGenericFilter`, Rasiowa–Sikorski
  `exists_generic_filter_countable` (sorry, plan in-file).
- **#535** `SetTheory/Descriptive.lean` — SEED LANDED: `IsPerfectSet`,
  perfect set theorem for closed sets (sorry). Extends to Borel/analytic
  sets (Kechris ch. II).
- **#536** #332: Boolean-valued models `V^B` and the forcing theorem
  (`φ` true in `V^B` iff `⊩ φ`), over pin's `CompleteBooleanAlgebra`.
- **#537** #333–#334: independence applications — the Neukirch–Uchida
  independence route #272 docks here (with `NumberTheory/ClassField`,
  planned #560); Cohen's `CH` independence as the first instance.

## References
* [Kunen], ch. VII; [Jech], ch. 14; [Kechris], ch. I–II.
* mathlib pin v4.35.0-rc3: `SetTheory.ZFC`, `SetTheory.Ordinal`,
  `SetTheory.Cardinal`, `Order.CompleteBooleanAlgebra`, `PolishSpace`.
