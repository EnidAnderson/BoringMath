# Candidate PR: the graph correspondence (C.1)

Ticket: BoringMath issue #10 (WORK ORDER W2, TREE C.1: finite
correspondences — the graph law). Branch: `feat/correspondence-graph`.
Module: `BoringMath/AlgebraicGeometry/Correspondence/Graph.lean` (new
owner area: the correspondence layer has no upstream mirror at the pin;
the placement anticipates the SmCor layer of C.2, per
`docs/OWNERSHIP.md`).

## Statement

* `AlgebraicGeometry.graph` — **the graph of a morphism over a base**:
  the lift of the identity and the morphism against the projections of
  the fiber product — the universal property of the fiber product
  applied to the pair `(𝟙, f)`, with `f ≫ pY = pX`. Noncomputable: the
  fiber product carries chosen limit data.
* `graph_fst`, `graph_snd` — the graph composed with the first
  projection is the identity (a section), and with the second
  projection is the morphism (the pullback-lift laws).
* `AlgebraicGeometry.graphCorrespondence` — **the graph
  correspondence**: the pushforward of the fundamental cycle of the
  source along the graph — a cycle on the fiber product `X ×_S Y`. The
  quasicompactness of the graph is an explicit hypothesis (it holds
  automatically for separated targets over the base); the source is
  Noetherian (finitely many components).
* `support_graphCorrespondence` — the support is contained in the
  image of the support of the fundamental cycle along the graph.
* `isFinite_graphCorrespondence` — the graph correspondence has
  finite support.

## Scope note

The composition law `graphCorrespondence_comp` (the composite of the
graph correspondences is the graph correspondence of the composite) is
the named next peel: its statement requires the composition operation
on correspondences — `(pr₁₃)_* (pr₁₂^* c · pr₂₃^* d)` in the
Suslin–Voevodsky formula — whose pullback factor is the fiber-cycle
machinery shared with the flat pullback on #16. The sequencing is
recorded on the ticket.

## Literature

* F. Mazza, V. Voevodsky, C. Weibel, *An Introduction to Motivic
  Cohomology* (the chapter on finite correspondences: the graph of a
  morphism as a correspondence). REVIEW(citation): exact chapter to be
  pinned by the human referee.
* V. Voevodsky, *Lectures on motivic cohomology* (correspondences).
  REVIEW(citation): to be pinned.
* A. Suslin, V. Voevodsky, *Singular homology of abstract algebraic
  varieties* (the classical reference for finite correspondences).
  REVIEW(citation): to be pinned.
