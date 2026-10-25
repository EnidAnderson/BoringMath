# The Boring Style — binding style rules

This document codifies the proof style used in `BoringMath` and `BoringLab`.
It is binding. It is a *refinement* of Mathlib's own style guidelines: every
rule here is compatible with Mathlib's, and wherever Mathlib would allow more
than we do, the stricter rule here wins. The word of the human reviewer is
final in any dispute.

The goal of the boring style is that every proof is an exact, explicit,
checkable document: long-term useful, fast to compile, easy to referee, and
pleasant for both human and agent readers. We work only in the disciplined,
"boring" subset of Lean.

## 1. Prime directive

Every proof is an **exact proof**: a chain of named, standard mathematical
steps, each visible on the page. Anything that resembles search,
normalization, clever simplification, or a sledgehammer is forbidden,
even "just this once". If an honest exact proof is not immediately
available, write a well-typed `sorry` (see §7) — never a clever tactic.

## 2. Tactic whitelist (default deny)

Only the following tactics may be used, and only in their explicit forms:

| Allowed | Remarks |
|---|---|
| `exact`, `refine`, `apply` | with explicit terms or explicit holes |
| `intro`, `intros` | |
| `have`, `show`, `change` | `have` with an explicit type ascription |
| `rw`, `rewrite` | only with explicitly named lemmas, e.g. `rw [eta g]` |
| `calc` | every step justified by a named lemma |
| `rfl` | **only** inside primitive definitional lemmas (§5) |
| `cases`, `rcases`, `obtain`, `rintro` | explicit patterns; name what you use |
| `induction`, `injection`, `subst` | |
| `funext` | the tactic form of the named axiom `funext` |
| `exfalso`, `left`, `right` | |
| `generalize`, `revert`, `clear` | |
| `unfold` | only with explicit constant names |
| `sorry` | see §7; highly encouraged as a temporary measure |

**Anything not listed is forbidden by default.** In particular, the
following are forbidden (non-exhaustive):

- **Normalization/rewrite automation:** `ring`, `ring_nf`, `norm_num`,
  `norm_cast`, `push_cast`, `field_simp`, `frac_...`, `abel`, `omega`,
  `linarith`, `nlinarith`, `polyrith`.
- **Simplification:** `simp`, `simp only`, `simpa`, `simp_all`, `simp_rw`,
  `squeeze_simp`, `dsimp` (all forms of `simp`/`dsimp`), `clean`.
- **Search/sledgehammers:** `aesop`, `tauto`, `grind`, `auto`, `solve_by_elim`,
  `exact?`, `apply?`, `rw?`, `suggest`, `trivial`, `assumption`,
  `contradiction`, `subst_vars`, `finish`, `ding`, `decide`,
  `native_decide` (the last is forbidden absolutely: kernel soundness).
- **Conversion magic:** `convert`, `convert_to`, `trans`-style unification
  helpers, `use`, `exists`, `constructor` (use `refine ⟨_, _⟩` or
  `apply Or.inl` instead), `ext` (use the named extensionality lemma, e.g.
  `funext`, `Set.ext`).

Term-level rules:

- Anonymous hypothesis terms `‹h›` are forbidden; hypotheses are always
  introduced and named explicitly.
- Dot-notation projections (`Eq.symm` via `h.symm`, `p.1`) are allowed: they
  resolve deterministically to named projections.
- Anonymous constructor terms `⟨_, _⟩` are allowed.

A tactic may be added to the whitelist only by a style-guide change approved
by the human reviewer, with a written justification in this file's history.

## 3. Naming

Every lemma is named after the standard mathematical theorem it represents,
in `snake_case` (e.g. `eta`, `eta_pair`, `schroeder_bernstein`,
`sprague_grundy`, `gelfond_schneider`). Idiosyncratic names
(`foo_helper`, `aux2`, `weird_trick`) are forbidden. Where the literature
gives no standard name, choose a descriptive mathematical name stating the
content. Otherwise, follow Mathlib's naming conventions so that the
declaration could be moved into Mathlib without renaming.

## 4. Literature references

Every `def`, `theorem`, `lemma`, `structure`, `instance`, and `abbrev`
carries an inline comment `-- Reference: ...` immediately above its
docstring, citing the standard mathematical literature with chapter and
section (or comparable) precision:

```lean
-- Reference: J. H. Conway, *On Numbers and Games*, 2nd ed., A K Peters, 2000,
-- Chapter 0, "All numbers are fractions".
-- REVIEW(citation): pin down the exact section in review.
/-- ... -/
theorem zero_ne_one ... := by ...
```

Rules:

- Prefer the original source plus one standard textbook treatment.
- For basic or folklore facts, cite the most standard textbook that states
  them.
- A citation that has not yet been verified against the physical text must
  carry a `REVIEW(citation)` tag. Before a candidate pull request is declared
  review-complete, every `REVIEW(citation)` tag must be resolved (verified
  or corrected) by the human reviewer.

## 5. Eta discipline

Every eta reduction (and every eta expansion, projection law, or other
definitional identification) must be peeled into its own named, typed lemma,
named after its standard mathematical designation:

- `BoringMath.eta` — eta conversion for functions;
- `BoringMath.eta_pair` — eta conversion for ordered pairs;
- `BoringLab.Game.eta` — eta conversion for the structure `Game`;
- and so on, one per type, as needed.

Consequences:

- `rfl` (and definitional unfolding) is permitted **only** in the proof of
  such primitive definitional lemmas. Elsewhere, a step that "is just `rfl`"
  must instead be an application of the corresponding named lemma.
- If a proof needs an eta step inline, stop, extract the step as a lemma,
  and rewrite the proof to cite it.
- When peeling a `sorry` (§7), eta reductions are peeled first: each becomes
  its own named lemma with its own reference.

## 6. Terms, statements, and structure

- Statements are written in the strongest standard mathematical form, with
  explicit binders; no `autoImplicit`, no relaxed implicit.
- Qualified names are preferred; `open` is allowed only for namespaces a
  file uses heavily, and never `open ... in`.
- One mathematical topic per module. Imports name specific modules only
  (never `import Mathlib`).
- Files are 100 columns or fewer; every file carries the standard copyright
  header (with the Hippocratic Mathematics License line); every public
  declaration carries a docstring.

## 7. The sorry protocol

A well-typed `sorry` on a precisely stated, correctly named, referenced
lemma is worth more than a clever proof. `sorry` is an encouraged,
legitimate temporary state, whether the statement is a world-open
conjecture or a triviality that has not yet been honestly instantiated.

Every `sorry` looks like this:

```lean
-- Reference: [Conway], Chapter 0 (the games `0` and `1` are distinct).
-- REVIEW(citation): ...
/-- The games `zero` and `one` are not equal. -/
theorem zero_ne_one : zero ≠ one := by
  -- TEMPORARY SORRY: the honest proof has not been instantiated yet.
  -- PEELING PLAN: <the next named lemmas/steps to extract>
  sorry
```

- The lemma statement is complete and permanent; only the proof is temporary.
- The peeling plan names the next steps. Peeling replaces a sorry'd proof by
  a chain of named lemmas, each itself proved honestly or sorry'd, until
  every remaining `sorry` is atomic: rfl-sized, a standard theorem, or
  genuinely open.
- A `sorry` is never closed by weakening its statement.
- In `BoringMath`, a candidate pull request must be sorry-free before it is
  declared review-complete; in `BoringLab`, sorries may persist
  indefinitely.
- `lake build` reports all sorries; `scripts/check-style.sh` lists them.

## 8. Candidate pull requests (`BoringMath`)

`BoringMath` is organized exactly as if its contents were pull requests one
could realistically submit to Mathlib — without ever actually pushing or
pull-requesting anywhere public.

- One branch per candidate: `pr/<area>-<topic>`; `main` advances only by the
  human reviewer's decision.
- Every commit is a *candidate commit*: the human reviews and may revise
  each one. Nothing lands without review.
- Each candidate has a note `docs/PRs/<topic>.md`: the statement, the
  literature, where it would live in Mathlib, whether Mathlib already has
  it, and review notes.
- Candidate commits are titled `feat(<area>): <summary>` or
  `fix(<area>): <summary>`, Mathlib style.

## 9. Enforcement

- `scripts/check-style.sh`: a grep-based backstop for banned tactics,
  missing references, and sorry inventory. It is best-effort; the human
  reviewer is authoritative.
- `lake build` must be warning-clean, except for the deliberate
  `declaration uses 'sorry'` warnings of §7.
- The Mathlib linter set is enabled (`weak.linter.mathlibStandardSet = true`);
  treat its warnings as errors to be fixed, not noise.

## 10. Review checklist (human)

For each candidate commit, check:

1. Every lemma is named after its standard mathematical theorem (§3).
2. Every declaration carries a verified literature reference (§4).
3. No forbidden tactic appears (§2).
4. Every eta/definitional step is peeled into a named lemma (§5).
5. Every remaining `sorry` has a peeling plan; no statement was weakened (§7).
6. The statement is the standard mathematical one, in Mathlib-compatible
   form; the PR note answers: does Mathlib already have it?
7. The file would be accepted into Mathlib as-is, stylistically.
