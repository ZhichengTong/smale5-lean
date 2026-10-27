# Sources and fixed revisions

## Five-body computational package

- Repository: https://github.com/hitchenzhe/smale-n5-paper
- Revision: `7389c875bd3d8c5fa01617b4d27a3562118b8081`.
- Source binding: `Smale_5-CT-v10.tex` (the package's archival manuscript).
- Program/check correspondence: `verification/program_index.json`, `verification/claim_status.json` in that repository.
- Reproduction instructions: `verification/README.md` in that repository.

`Smale5/Diagram3NormCertificate.lean` uses the 67 integer P66 coefficients as mathematical data and proves its identities and positivity in Lean. Third-party Python programs and downloaded archives are not bundled here.

## Published complete Lean proof and interface

Tejasvi Singh Tomar, arXiv:2610.13100: https://arxiv.org/abs/2610.13100

Source deposit: https://zenodo.org/records/23202861 ; source commit `52858e1c7e831f226c306d7b3bdf8d02c16f38da`. Its environment is Lean 4.35.0-rc3 with Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`.

The literal interface and adapted affine-force proof in `UpstreamBridge.lean` are attributed in that file and `THIRD_PARTY_NOTICES.md`. This is a different proof route from the manuscript-specific development.

## Mathlib

Lean 4.35.0; Mathlib v4.35.0, commit `56a005855ea17e0b0958f73ec801ae140b0a1679`. Dependencies are fixed in the manifest. The Mathlib source archive used in the recorded local check has SHA256 `ec8a2f2298585a13cdc4d0423befb76e14a6114e8470a5506f72604cd6a563e0`.
