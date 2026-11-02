# Algebraic topology roadmap — BoringMath/AlgebraicTopology/ (tickets #510–#519)

Pin audit (mathlib v4.35.0-rc3): `AlgebraicTopology/` at the pin has simplicial
sets, quasicategories, model categories, Reedy structures, singular homology,
Dold–Kan, the fundamental groupoid. MISSING (audited): prespectra/spectra, the
stable homotopy category, A¹-homotopy (the motives shadow lives in
`AlgebraicGeometry/Motives/A1.lean`), the six-functor substrate at true grade.

This folder hosts the F-line ("FOUNDATIONS-FIRST ring", TREE F.1–F.4) and the
∞-groupoid row #259.

## Ticket tree

- **#510** `AlgebraicTopology/Spectra/Basic.lean` — SEED LANDED: `Prespectrum`,
  `Prespectrum.susp` (+ proved `susp_X`), `IsStableCategory`,
  `exists_stable_category_of_spectra` (sorry). Home of TREE F.1/F.2/F.4.
- **#511** TREE F.1: stable categories — hearts, pretriangulated homotopy
  value categories (builds on `CategoryTheory/Triangulated/Verdier.lean`).
- **#512** TREE F.2: spectra as simplicial fibrant objects / symmetric
  spectra; `Ho(Spectra)` constructed.
- **#513** TREE F.4: (∞,1)-categorical substrate — route decision record
  (quasicategories vs model-category-native, both at pin).
- **#514** Dold–Kan strengthening + homotopy groups of simplicial sets
  (pin has `SimplicialSet`; gaps at the homotopy-group layer).
- **#515** A¹-homotopy interface: `Sm/S` localization against
  `𝔸¹`-projections, docking `AlgebraicGeometry/Motives/A1.lean` (C.4).
- **#516** TREE F.3: the six-functor substrate interface (exchange calculus;
  docks `AlgebraicGeometry/Correspondence` and `Fiber/BaseChange`).
- **#517** #259: ∞-groupoid version of the motivic consumer (statement layer).
- **#518** stable homotopy groups `πₙˢ` and the first computations
  (Hopf maps) — statement layer.
- **#519** reserved: `AlgebraicTopology/Homology/` generalizations of pin's
  singular homology.

## References
* [Hovey], ch. 7; [Lurie] HTT §1.1.2, §1.4.4; [Adams], ch. III;
  [Weibel], ch. 10.
* mathlib pin v4.35.0-rc3: `AlgebraicTopology.SimplicialSet`,
  `AlgebraicTopology.ModelCategory`, `AlgebraicTopology.Quasicategory`,
  `AlgebraicTopology.DoldKan`, `AlgebraicTopology.SingularHomology`.
