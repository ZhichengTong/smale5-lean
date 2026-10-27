# Smale 5 Lean formalization

Lean 4 formalization of algebraic and analytic components of the planar five-body central-configuration finiteness argument, based on manuscript v16.

The checked library contains **20 modules and 121 public auxiliary theorems**, with standard logical axioms only (`propext`, `Classical.choice`, `Quot.sound`). It covers normalized Newtonian equations, centre of mass, virial and inertia identities, finite distance/four-product fibres, energy constancy along differentiable paths, selected Diagram 3 and Diagram 7 identities, and the finite-similarity adapter.

## Build and audit

Install Lean through [elan](https://github.com/leanprover/elan). The checked toolchain is Lean 4.35.0. Mathlib is pinned to `56a005855ea17e0b0958f73ec801ae140b0a1679` (v4.35.0).

```sh
lake exe cache get
python scripts/check.py
```

Python 3.10+ uses only its standard library. The script compiles every authored module in dependency order and reads `#print axioms` for every public theorem. Results are written under `verification/`. A normal `lake build` is also available after dependency setup.

## Layout

- `Smale5.lean`, `Smale5/`: checked library.
- `blueprint/`: statement/dependency blueprint.
- `verification/`: source hashes, complete declaration list and axiom audit.
- `manuscript/`: Lean-oriented v16 working edition, TeX and PDF.
- `integration/`: separate target applying the published upstream main theorem.
- `docs/STATUS.md`: completed components and remaining proof connections.
- `docs/SOURCES.md`, `THIRD_PARTY_NOTICES.md`: references and attribution.

## Main target

`Smale5.FiveBodyFiniteness` is the exact target proposition. The manuscript-specific proof still needs the curve-extraction, completion/order and local-diagram connections. The separate `integration/FullMain.lean` source applies another author's published complete proof; its full dependency chain has not been rebuilt locally. It is outside the default checked library.

See [中文说明](README.zh-CN.md) and [verification status](docs/STATUS.md).
