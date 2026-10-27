# Verification status

## Checked components

The default `Smale5` library contains 20 modules and 121 public auxiliary theorems. Every declaration is listed in `verification/audited-declarations.json`; the complete axiom report is `verification/axioms.log`.

Verified components include the actual normalized equations, finite fixed-distance and fixed-four-product fibres, U=I, energy constancy on continuous normalized paths differentiable in the interval interior, Diagram 3 elimination/norm identities and both-sign complex-root nonvanishing for positive unequal real parameters, Diagram 7 inertia identities, conditional order contradiction, and the finite-similarity adapter.

## Remaining connections for manuscript v16

1. Extract the required irreducible algebraic curve from an infinite positive normalized locus, preserving the positive arc and the required energy constancy.
2. Construct its completed normalized curve and compatible orders, and prove the needed pole/degree-zero consequences.
3. Connect the local diagram classification, Puiseux expansions, chart coverage and analytic exclusions to those global orders.
4. Integrate remaining computational certificates and their analytic applications, including the Diagram 3 fifth-order jet-to-obstruction identity.

The public N5 Python package was replayed successfully (77 exact checks plus the separate 64-sign Diagram 4 census; 42 applicable computational claim groups). Selected Diagram 3 norm/P66 results have additionally been proved in Lean.

`FiveBodyFiniteness` remains the final target proposition. The separate published-proof integration source is outside this checked library and awaits a complete upstream rebuild.
