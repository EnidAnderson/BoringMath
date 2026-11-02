# Information theory roadmap — BoringMath/InformationTheory/ (tickets #542–#545, proposed #339–#342)

Pin audit (mathlib v4.35.0-rc3): `InformationTheory/` has Hamming and
Kullback–Leibler; `Analysis/SpecialFunctions/BinaryEntropy` has the binary
entropy. MISSING: Shannon entropy of a finite distribution and its laws,
Kolmogorov complexity, the coding theorems.

## Ticket tree

- **#542** `InformationTheory/Entropy.lean` — SEED LANDED: `shannonEntropy`,
  `shannonEntropy_nonneg`, `shannonEntropy_prod` (chain rule; both sorries
  with plans). Home of #339.
- **#543** #340: Kolmogorov complexity `K(x)` (statement layer; bridge to
  `Logic/Computability/Bridge.lean` #539 and `Complexity` #301–#308).
- **#544** #308/#341: BPP/PAC rows — entropy bounds as generalization bounds
  (docks `Science/Verification` #381–#390 and BoringLab Epistemology
  `OckhamBound` #285).
- **#545** #342: source/channel coding theorems (statement layer).

## References
* [Shannon 1948]; [Cover–Thomas], ch. 2; [Li–Vitányi], *An Introduction to
  Kolmogorov Complexity*, 4th ed., ch. 2.
* mathlib pin v4.35.0-rc3: `InformationTheory/Hamming`,
  `InformationTheory/KullbackLeibler`, `Analysis/SpecialFunctions/BinaryEntropy`.
