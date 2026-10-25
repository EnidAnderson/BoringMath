# The pull-request workflow (Work ↔ Code ↔ human)

This is the protocol by which the two Mistral agents and the human
mathematician collaborate through GitHub:

- **Mistral Work** (chat.mistral.ai): drafts mathematics and code, opens
  pull requests against `main` of `BoringMath` and `BoringLab`.
- **Mistral Vibe** (the coding agent on the Lean machine): fetches, builds,
  checks, and reviews those pull requests; asks the human questions when
  necessary; performs merges only on the human's instruction.
- **The human**: referee for every merge and the authority on all style
  and mathematical questions.

## Protocol

1. Work opens a PR (branch name `pr/<area>-<topic>` or similar, described in
   the PR body with the mathematical content and references).
2. Vibe fetches it locally:

   ```bash
   scripts/fetch-pr.sh <PR-number>          # in the repo that received the PR
   git checkout pr-<PR-number>
   ```

3. Vibe verifies it mechanically:

   ```bash
   lake build                                # must succeed; warnings only from
                                            # deliberate, documented sorries
   scripts/check-style.sh                    # zero violations
   ```

4. Vibe reviews it line by line against `docs/STYLE.md` (naming, references,
   eta discipline, sorry protocol, statement strength) and reports to the
   human: a summary, the per-commit review, any questions, and a
   recommendation.
5. The human decides: merge, request changes, or reject. Only on the
   human's explicit instruction does Vibe merge (`gh pr merge` or
   `git merge`) and push.
6. Neither agent ever pushes directly to `main`; `main` is protected.

## Rules for PRs from Work

- **Never submit PRs to upstream or third-party repositories** (mathlib,
  combinatorial-games, or any repository outside our own). The candidate-PR
  framing is an organizational device only. Compatibility fixes for external
  dependencies live in our own forks, documented as deltas on the wire
  ticket; upstream goodwill gestures (issues, PRs, comments) are not
  permitted.

- Every declaration carries a literature reference with `REVIEW(citation)`
  tags where unverified; citations from memory must be tagged.
- A PR may carry well-typed `sorry`s with peeling plans (see the sorry
  protocol in `docs/STYLE.md`); it must never silently weaken a statement.
- `BoringLab` depends on `BoringMath` by local path `../BoringMath`: both
  repositories must be cloned as sibling directories to build. PRs touching
  `BoringLab` are built only after the `BoringMath` main they depend on
  builds.
- A PR that changes `docs/STYLE.md` is a governance change: it requires the
  human's explicit approval before anything else in it is reviewed.

## Review checklist

Same as `docs/STYLE.md`, §10, plus:

1. Does the PR build warning-clean on the pinned toolchain?
2. Are all citations verified or explicitly `REVIEW(citation)`-tagged?
3. Does any statement duplicate something Mathlib already has? (The PR note
   `docs/PRs/<topic>.md` must answer this.)
4. Questions for the human are collected and asked once, concretely.

## Contributions and licensing

All contributions to this repository (including pull requests from the
work assistant) are accepted only under the Hippocratic Mathematics License
v1.0 (`LICENSE`). By opening a pull request, the contributor offers the
work under that license. Files destined for a hypothetical Mathlib
submission would be re-licensed Apache 2.0 upstream, at Mathlib's own
requirements; this repository's copy remains under the Hippocratic
Mathematics License.

## The modular fast-forward protocol (no-merge discipline)

Merging, in the strict sense, is the reconciliation of divergent work — a
sign that two PRs touched the same ground. This protocol makes that
structurally impossible:

1. **One PR = one new module + one new PR note.** A content PR adds
   exactly one new file under `BoringMath/<Area>/` and exactly one new
   file under `docs/PRs/`. New files only.
2. **No PR edits any file it did not create in that same PR.** In
   particular: never edit the lakefile, `docs/STYLE.md`, `scripts/`,
   another module, or another PR note. A module may *import* existing
   modules freely; importing is not editing.
3. **Shared-file changes are serialized.** The lakefile, the style
   guide, the scripts, and this protocol are the only shared mutable
   files. A PR touching them may be open only while no other PR is
   open, and it lands before any new content PR is opened. This is the
   single serialization point of the whole workflow.
4. **Landing is a rebase, never a merge.** Only rebase-merging is
   enabled on GitHub, linear history is required on `main`, and
   branches are deleted on landing. A landed PR contributes exactly
   its reviewed candidate commits to `main`, in order; git never
   reconciles anything, and no merge commit ever exists.
5. **Supersession, not revision.** A result that subsumes an earlier
   one is a new module; the earlier module is left untouched. Superseded
   modules are removed only by a periodic, human-ordered compaction PR
   (itself serialized per rule 3).
6. **Content PRs commute.** Because every content PR is purely
   additive, any set of open content PRs can land in any order. If two
   content PRs ever overlap, that is a protocol violation caught in
   review — not a merge situation.

The root import file is eliminated: the library is built by globs
(`BoringMath.+`), so no content PR ever touches a shared file in order
to be built.
