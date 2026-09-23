<!--
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-->

# AEGIS Ω RH formal contribution status — 2026-09-23

This document is an evidence-first public map of the AEGIS Ω Riemann Hypothesis / Weil-criterion formalization effort. It deliberately separates theorem producers, conditional bridges, hosted execution evidence, and open load-bearing obligations.

It does **not** mark the Riemann Hypothesis as solved. It records substantially stronger formal infrastructure than a statement-only contribution and defines the exact trigger for a future `formal_proof using lean4` submission against the Google DeepMind Formal Conjectures target.

## Exact sources

- External target repository: `google-deepmind/formal-conjectures`
- External target: `FormalConjectures/Millenium/RiemannHypothesis.lean::riemannHypothesis`
- Target type: Mathlib `RiemannHypothesis`
- Lean toolchain: `leanprover/lean4:v4.33.1`
- Mathlib pin: `0df444a360eaa60ab8c11dca51a86af692955474`
- AEGIS proof-source head: `589adf0480bd4d7c12c9828027ea6228398377f4`
- Fork replay candidate branch: `proof/rh-606-port-v1`
- Fork replay candidate head at publication start: `21b83db22447a8f4a75c6cd8b2329605fd6230d4`

The fork replay applies explicit, reviewable Lean-4.33 compatibility corrections to the pinned AEGIS source. Therefore the fork is **not** represented as byte-identical source preservation.

## What is already materially formalized

The AEGIS chain contains a large theorem DAG connecting the explicit formula, Mellin transforms, logarithmic transport, moment constraints, translated packets, zero-side summability, pole isolation, and restricted-Weil contradiction machinery.

The following transitions have already been observed in hosted fork replay without `sorryAx` in their printed axiom footprint:

| Transition | Hosted axiom footprint observed |
| --- | --- |
| finite-dilation Mellin filter and endpoint annihilation | standard kernel axioms only |
| exact off-line Mellin seed packet | `propext, Classical.choice, Quot.sound` |
| moment-zero two-point spectral detector | `propext, Classical.choice, Quot.sound` |
| multiplicity-weighted zero-pair coefficient witness | `propext, Classical.choice, Quot.sound` |
| actual zero-summand witness | `propext, Classical.choice, Quot.sound` |
| translation-gap invariance, including diagonal translation at zero | `propext, Classical.choice, Quot.sound` |
| final-sign translated component and norm bounds | `propext, Classical.choice, Quot.sound` |
| finite-dilation V11 Mellin factor and moment annihilation | `propext, Classical.choice, Quot.sound` |
| mixed Mellin transform factorization for the actual repository cross-correlation | `propext, Classical.choice, Quot.sound` |
| RH-to-final-sign direction, including critical-line norm-square and zero-quadratic nonnegativity | `propext, Classical.choice, Quot.sound` |

A later exact-head replay also compiled `WeilMixedMellinFactorV10.logCross_transform_factor_v10` and `mellin_mixed_factor_v10` and printed only `propext, Classical.choice, Quot.sound` before advancing to the next module. On exact fork head `1781bc53eff90d723780a550ab8112b83fdd6386`, the hosted replay then compiled `autocorrelation_mellin_critical_normSq_v11`, `rh_zero_summand_nonnegative_v11`, `rh_zero_quadratic_nonnegative_v11`, and `rh_implies_final_sign_residual_v11`; every printed axiom footprint was exactly `propext, Classical.choice, Quot.sound`, after which the replay advanced to `WeilStrictStripSeedV11`. Hosted GitHub runner receipts establishing the newly listed transitions include exact-head runs in the fork replay lane. In particular, the translation-gap/final-sign run printed the three translation invariance theorems and three translated-bound theorems with no `sorryAx`; a subsequent exact-head run printed both V11 finite-dilation load-bearing theorems with the same standard axiom footprint before advancing to the next module. These receipts are historical for their exact commits and are not silently rebound to later heads.

The important point is structural: the formalization does not merely state a Weil criterion. It constructs concrete compact-smooth packets, enforces the repository moment conditions, transports them through exact Mellin identities, and produces nonzero spectral witnesses at actual nontrivial zeta zeros.

## Formal structure beyond the minimum target

Several independent research lanes go beyond the minimal theorem statement.

### Exact spectral witness construction

For prescribed strict-strip points, the chain constructs a compact-smooth positive-half-line packet with nonvanishing Mellin transform at both points. A finite-dilation filter then enforces the required moment-zero conditions without destroying the target Mellin values.

This yields a repository-admissible moment-zero detector for a nontrivial zero `rho` and its autocorrelation-paired point `1 - conj rho`.

### Actual zero-summand nonvanishing

The moment-zero detector is connected to the repository's actual multiplicity-weighted zero functional. The resulting theorem produces a packet for which the corresponding canonical zero summand is nonzero.

This is stronger than merely proving that an abstract test functional separates points: the witness is tied to the exact zero-side summand used by the AEGIS explicit-formula spine.

### Translation and finite packet geometry

A parallel AEGIS closure-swarm branch (`4f1b52a454be9779bf39245cb4343d8d8e4b7270`) contains unconditional finite-family results including a canonical four-packet coercive estimate and a canonical four-packet sign theorem. These are not yet a universal final-sign producer, but they establish a nontrivial finite translated-packet positivity/negativity geometry with explicit constants and no supplied PSD hypothesis.

These results are recorded as a separate producer lane and are not silently promoted into the `589adf...` proof source.

## Current hosted replay boundary

Hosted execution is no longer globally absent: the fork has produced real GitHub-hosted jobs with non-empty runner steps and has compiled successive parts of the 131-module PR606 closure.

Historical exact-head replay on the fork has already progressed through the off-line seed, moment-zero detector, and actual zero-summand witness. The current candidate head above includes the next compatibility correction for translated-diagonal invariance.

A hosted run is evidence only for the exact commit it executed. A later head does not inherit hosted authority until its own run completes.

## The two remaining mathematical producers

The central gate still separates two obligations.

### 1. Restricted-Weil implication

The chain now contains substantial downstream machinery: Laplace/Cauchy transforms on the right half-plane, centered-zero pole isolation, nonzero residue witnesses, and the actual zero-summand detector.

The remaining task is to package those ingredients into a theorem term of type

```lean
UniversalZeroQuadraticNonnegativeV10 → RiemannHypothesis
```

without introducing additional assumptions.

### 2. Universal sign producer

A separate theorem must inhabit

```lean
UniversalZeroQuadraticNonnegativeV10
```

equivalently the repository-wide final sign residual on the full moment-zero compact-smooth class.

Finite three/four-packet coercivity, zero-shift equivalence, translated-kernel bounds, or conditional O₀ globalization are strong ingredients, but none is silently treated as this universal producer.

## Closed compact-support exhaustion / globalization step

A separate AEGIS branch, `proof/rh-window-exhaustion-v1` at
`05b6a49692baa7b88cc580c8bbf52e6eb6658450`, closes an important logical
globalization boundary.

Its theorem
`weil_compact_smooth_negativity_iff_all_windows_v1` proves that the full
compact-smooth moment-zero sign obligation is equivalent to the sign obligation
on every finite symmetric logarithmic support window. The subsequent theorem
`weil_compact_smooth_negativity_iff_positive_nat_windows_v1` reduces the
continuum of positive real windows to the cofinal countable family of positive
integer windows.

This means **compact-support exhaustion itself is closed**: no density or
limit argument is needed merely to pass from all finite windows to the full
repository packet class.

The remaining producer is sharper and narrower:

```text
for every positive window radius n,
prove WindowArithmeticNonpositiveV1 n
```

That distinction matters. “Globalization/exhaustion” is not the same open
problem as “prove the sign on each arbitrary window.” The former has a formal
theorem; the latter is the load-bearing analytic producer.

The older O₀/Coq globalization lane is a different abstraction: it proves
`GlobalizationReadyV1 → GlobalWeilPositivityV1` and still requires a
`GlobalizationReadyV1` inhabitant. It should not be conflated with the
already-closed Lean compact-window exhaustion theorem.

## Alternative terminal: Li criterion

AEGIS also contains a provider-bound Li-criterion terminal that proves the exact equivalence

```lean
(∀ n : ℕ, 0 ≤ (LiCriterion.taylorCoeff LiCriterion.riemannXi n).re)
  ↔ RiemannHypothesis
```

This is a clean alternate terminal, not a shortcut: the unconditional producer for all Li-coefficient nonnegativities remains a separate obligation.

## DeepMind contribution trigger

The intended external contribution should change from `research open` / no formal proof only after all of the following are simultaneously true on one exact commit:

1. a theorem of type `RiemannHypothesis` is produced without an unresolved premise;
2. the complete import closure replays under the pinned Lean/Mathlib environment;
3. `#print axioms` for the terminal theorem contains no `sorryAx` or unexpected custom axiom;
4. all compatibility changes are content-addressed and reviewable;
5. the exact commit has a non-empty hosted runner receipt;
6. an independent reviewer can verify that the terminal theorem matches the DeepMind target semantically.

At that point the correct Formal Conjectures contribution shape is a stable external `formal_proof using lean4` reference to the exact proof commit, followed by human review.

## Research novelty candidates

The project should make novelty claims only after literature and expert review. The strongest candidates visible in the formal artifacts are:

- a constructive moment-annihilating spectral witness pipeline tied directly to the canonical zeta-zero summand;
- a translation-gap formulation of the arithmetic sesquilinear form enabling finite packet geometry;
- explicit finite translated-packet coercivity with rational constants;
- a proof-engineering architecture where mathematical transitions, hosted replay receipts, source provenance, and axiom footprints are treated as separate first-class objects.

These are presented as **novelty candidates**, not priority claims.

## Current disposition

```text
RH_SOURCE_DAG        = ADVANCED
HOSTED_FORK_REPLAY   = EXECUTED_PARTIALLY
RH_CERTIFICATE       = NOT_YET_INHABITED
UNIVERSAL_PRODUCER   = OPEN
RESTRICTED_IMPL      = OPEN_AS_TERMINAL_TERM
DEEPMIND_SUBMISSION  = NOT_YET_ADMISSIBLE
MAIN_MERGE           = NOT_PERFORMED
AUTHORITY_EFFECT     = NONE
```

The next valid promotion event is not another label. It is a clean exact-head theorem producer plus replay receipt.
