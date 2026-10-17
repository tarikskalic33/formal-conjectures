# AEGIS Ω — optimized actual Weil–Schur handoff for DeepMind review

**Scope:** exact-source mathematical integration and a review-ready conditional theorem.
This document is **not** a claim that RH has been proved.

## Immutable references

- DeepMind `google-deepmind/formal-conjectures` upstream main checked at `e750f777b32aeae464c01809e0d223dd62e99fab`.
- Upstream official theorem file: `FormalConjectures/Millennium/RiemannHypothesis.lean`; blob `5b1dcd5c46ab4a5f449d7d4a5c5ddce7c89c3542`.
- The fork has the **same** official theorem blob on main, including its catalog placeholder `by sorry`; the catalog file is not changed in this PR.
- Preexisting AEGIS proof assembly: `tarikskalic33/formal-conjectures` PR #88 exact source `aacdd511877e3e725dbee05b1167ee38b681ab31`.
- New external source anchor: `https://github.com/tarikskalic33/formal-conjectures/blob/4242d9a58254132178a19c0d35e9c572739282fe/AEGISOverlay/RHOptimizedSchurGlobalJoinV1.lean`.
- Lean pin: 4.33.1. Mathlib pin: `0df444a360eaa60ab8c11dca51a86af692955474`.

## New theorem and why it matters

The new module `AEGISOverlay/RHOptimizedSchurGlobalJoinV1.lean` composes:

1. `AEGIS.RHActualUniversalFineGramV1.every_moment_zero_packet_actual_fine_gram_with_support`: for **every** moment-zero Weil packet, constructs finite supported atoms, a diagonal gain `5671/3200`, exact reconstruction, and the genuine full mixed Gram.
2. `AEGIS.RHScaleRowCompositionV1.actual_optimized_weighted_schur_unequal_energy_from_fine_diagonals`: optimized `34727/32768` margin for actual finite Weil atoms of **unequal** energy with arbitrarily many indices, provided genuine mixed-entry and weighted-row bounds are supplied.
3. `AEGIS.RHRestrictedWeilBridgeV13.final_sign_implies_rh_v13`: canonical Mathlib RH target.

The joined declaration is
`AEGIS.RHOptimizedSchurGlobalJoinV1.riemannHypothesis_of_optimized_actual_row_producer`.

Its conclusion is **exactly** `RiemannHypothesis`. Its **`hselect` hypothesis** is visible in the Lean type and is *not* discharged. It selects one possibly different finite reconstruction per source packet, with actual nonnegative symmetric costs `c`, positive weights `w`, analytic mixed bound involving the genuine `B` pairing, and weighted row ceiling `46688/65536`. This avoids the invalid demand that *every* admissible decomposition (including repeated atoms) satisfy that ceiling. Prime-power and Archimedean interactions remain essential.

## Verification boundary

- Baseline PR #88 cofinal replay `38799949777` (311 modules) succeeded for the **preexisting** source; its strict axiom audit recorded standard foundational axioms. It is not proof of this **new** module.
- The newly committed join has `#print axioms` for its two theorems. This PR does **not** report a verified kernel result for that newly introduced source until an exact-head replay runs.
- The old scalar/narrow-window constructor covers `693/2000` logarithmic width only; it cannot be applied by type conversion to an arbitrary `n * pi` window.
- The new theorem does not derive `hselect`. An all-green workflow, a formal criterion equivalence, and the absence of `sorryAx` from a **conditional** theorem do not prove the premise.

### Kernel acceptance commands in a provisioned exact-source environment

Use the already pinned PR #88 source / Lean / Mathlib / AEGIS dependencies with the new branch checked out; its ordinary default `lake build` is not enough to import the separately pinned AEGIS research modules without their prerequisite olean materialization.

```bash
lake env lean -o .lake/build/lib/lean/AEGISOverlay/RHOptimizedSchurGlobalJoinV1.olean \
  AEGISOverlay/RHOptimizedSchurGlobalJoinV1.lean
```

Require a zero-error run, exact SHA receipt, and only `propext`, `Classical.choice`, and `Quot.sound` in both emitted `#print axioms` reports. Do **not** misreport a missing cached dependency as a disproved theorem.

## DeepMind submission gate

Official instructions:
- `https://github.com/google-deepmind/formal-conjectures/blob/e750f777b32aeae464c01809e0d223dd62e99fab/PROOFS.md`
- `https://github.com/google-deepmind/formal-conjectures/blob/e750f777b32aeae464c01809e0d223dd62e99fab/CONTRIBUTING.md`

Their policy allows the upstream *catalog* theorem to remain `by sorry` while a **separately verified, complete** external proof is linked using `@[formal_proof using lean4 at "..."]`. A `sorryAx` dependency in the external theorem is **not** permitted as proof evidence.

**Do not add a `formal_proof` attribute yet.** The missing admission check is a closed, caller-free Lean declaration:

```lean
example : _root_.RiemannHypothesis :=
  AEGIS.SomeVerifiedModule.unconditional_riemannHypothesis
```

The exact external declaration must compile with no added mathematical parameters and only accepted foundational axioms. Then a separate, narrow upstream-ready PR can add its immutable exact-commit `formal_proof` reference without changing the official theorem's statement or GRH declarations. A Google CLA and upstream review are separate submission requirements.

## Preservation and review

This is stacked onto the existing PR #88 exact head, never merged or rebased into the protected main by automation. No old proof files, saved receipts, or existing mathematical theorem statements have been changed. This PR extends its own inherited cofinal workflow to compile and audit the new module, and extends the exported proof graph; the separately pinned PR #88 exact-head source and green receipts remain intact. To propose an upstream change, start from the current DeepMind main and carry **only** the final verified link — not the complete AEGIS research tree or this conditional handoff.
