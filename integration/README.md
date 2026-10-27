# Separate published-proof integration

These two source files are outside the default `Smale5` library.

`VerifyDefinitions.lean` checks that the adapter proposition is definitionally equal to the actual published `CC5Full.MainTheorem`; this interface check passed locally with the unchanged upstream Basic/System sources.

`FullMain.lean` applies `CC5Full.Core.Compose.MainTheorem_holds` to the checked adapter. A complete compatible build of the upstream project and local adapter is required before it can be checked. The upstream full source is available at https://zenodo.org/records/23202861 (Lean 4.35.0-rc3, Mathlib c55e6e7). Its generated modules are separate source archives; they are not bundled in this Lean-component repository.

The `Smale5.FiveBodyFiniteness` target has not yet been checked through this complete dependency chain locally. The recorded upstream fresh-build cost is about 863 CPU-hours; that is an upstream measurement, not a local timing result.
