# The audit protocol

Every claim about what Mathlib does or does not provide is an AUDIT claim,
and audit claims obey the same honesty discipline as proofs: graded,
evidenced, never asserted from memory.

## Grades

- ABSENT — no declaration exists at the pinned revision.
- BARE — definitions exist, no usable API.
- PARTIAL — real API exists but is missing structure the program needs
  (the missing part is named).
- MATURE — usable for our purposes as-is.
- EXTERNAL — exists outside Mathlib (cite where).

Every grade carries an EVIDENCE grade:

- GOLD — file fetched and read at the pinned revision (`v4.35.0-rc3`).
- SILVER — directory listed at the pinned revision.
- BRONZE — GitHub code search scoped `repo:leanprover-community/mathlib4`.
  The index covers the default branch, not the pin: re-verify at the pin
  before citing in a shard PR.
- ZERO — recollection. Never citable. (Two ZERO-grade recollections were
  caught and corrected in the first audit: combinatorial games were
  believed present — they are ABSENT; model categories were believed
  absent — twenty files exist.)

## Search hygiene (binding)

1. ALWAYS scope: `repo:leanprover-community/mathlib4`. An unscoped search
   hits forks: an unscoped `PGame path:Mathlib/SetTheory/Game` query returns
   hits from fork checkouts and contaminates the audit (this happened in
   the first audit and is the reason this section exists).
2. Code search indexes the default branch, not the pinned tag. A BRONZE hit
   must be confirmed GOLD or SILVER at the pin before it grounds a shard.
3. Absence of a hit is weak evidence (index lag; generated names invisible
   to text search, e.g. `to_additive`-generated additive lemma names).
   Grade absence claims BRONZE and confirm at the pin when load-bearing.
4. Before staking API names on an ABSENT station, check for in-flight
   upstream PRs and branches (fork hits prove the ground is staked in
   fork-land at least); record what was found.

## The station entry format

Each station of the god's-eye map gets one entry:

- STATION: the foundation object.
- NEEDED-BY: the program station(s) it serves (dictionary line, motive
  construction, certificate line).
- NAIVE FORM: the trap — the set-theoretic / value-level translation we
  predict and refuse.
- RIGHT HOME: the structural form to build instead.
- EXTRACTION: how the classical form is projected out, stated plainly.
- MATHLIB: grade + evidence + paths.
- MINIMAL API: predicted new modules (never extend Mathlib in place; new
  modules only, named so they could land upstream), with dependencies on
  existing Mathlib libraries.
- FIRST SHARDS: the boring PRs that start it (Tier 0–2 sized).

## Audit PR mechanics

Audits are docs PRs: new files under `docs/AUDITS/` only, purely additive,
no shared-file edits. An audit is versioned by date in its filename and
never edited in place: supersede, do not revise (protocol rule 5). A shard
PR may cite an audit only at GOLD or SILVER evidence for its load-bearing
claims.
