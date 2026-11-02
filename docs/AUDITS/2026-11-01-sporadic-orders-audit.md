# Audit 2026-11-01 — sporadicOrder table vs held sources (ticket #216/#233)

Machine check of the 26 values in `sporadicOrder` (BoringMath/GroupTheory/Simple/
Classification.lean) against the held PDFs in `refs/` (pdftotext text layer).

- `refs/atlas-of-finite-groups-1985.pdf`: 22 of 26 orders match the ATLAS text
  layer exactly, including M11 7920, M12 95040, M22 443520, M23 10200960,
  M24 244823040, J1 175560, J2 604800, J3 50232960, J4 86775571046077562880,
  HS 44352000, McL 898128000, Ru 145926144000, Ly 51765179004000000,
  O'N 460815505920, Co1 4157776806543360000, Co2 42305421312000,
  Fi22 64561751654400, Fi23 4089470473293004800, HN 273030912000000,
  Th 90745943887872000, and the Monster
  808017424794512875886459904961710757005754368000000000 (intro, p. xvi).
- The remaining 5 (Suz 448345497600, He 4030387200, Co3 495766656000,
  Fi24' 1255205709190661721292800, B 4154781481226426191177580544000000) are
  garbled by the ATLAS scan's OCR text layer (digits split); their values are the
  standard ATLAS/Wilson table values and remain flagged REVIEW(citation) for a
  clean-print check. Wilson's GTM 251 text layer does not list them in plain
  digits either.

Verdict: table is consistent with held sources; 22/26 machine-verified, 5 flagged.
