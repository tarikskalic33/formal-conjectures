# PR #7031 — execution audit and proof-closure plan

**Audit date:** 2026-10-09  
**Audited fork HEAD:** `37e8a5dd1fd7febec380dd562417168714cc86c4`  
**Upstream target:** `google-deepmind/formal-conjectures#7031`  
**Status:** evidence-backed audit; this document is not a proof of RH.

## Executive disposition

PR #7031 does not currently establish the Riemann Hypothesis. The decisive blocker is mathematical, not merely CI: the official theorem's application leaves the universal large-window premise open. Separately, the PR is not a self-contained upstream build because its terminal imports depend on modules supplied from external repositories and raw Lean compilation.

The next objective is not to rename, suppress, or route around the open goal. It is to identify a genuinely unconditional producer for the exact universal sign statement, prove its missing hypotheses from existing source-bound results, and then compile the official target with a clean axiom audit.

## Exact proof junction

The official target in `FormalConjectures/Millennium/RiemannHypothesis.lean` is:

```lean
theorem riemannHypothesis : RiemannHypothesis := by
  apply AEGIS.RHSmallWindowCanonicalJoinV1.riemannHypothesis_of_above_693_over_2000_v1
```

The invoked theorem in `AegisRH/SmallWindow/RHSmallWindowCanonicalJoinV1.lean` explicitly requires

```lean
hLarge : ∀ L : ℝ, (693 / 2000 : ℝ) < L →
  WindowArithmeticNonpositiveV1 L
```

Its proof reduces that premise to `UniversalZeroQuadraticNonnegativeV10`, then invokes the restricted-Weil kernel bridge. The finite cutoff only discharges windows at or below (693/2000); it does not prove the universal complement.

In `AegisRH/PR606/Source/RHMillenniumGateV10.lean`, the exact terminal positivity target is

```lean
UniversalZeroQuadraticNonnegativeV10 :=
  ∀ g : WeilCompactSmoothGV1,
    WeilMomentConditionsV1 g →
    0 ≤ (∑' rho : RiemannNontrivialZeroIndexV2,
      WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re
```

The same module proves equivalences between this target, `FinalSignResidualV1`, and `ZeroShiftComponentDominanceV1`. Those equivalences translate the target; they do not prove it unconditionally. The PR's V13 bridge claims the implication from the universal positivity target to RH. The accompanying source notes also identify RH as implying the corresponding final-sign residual. Therefore, treating this target as a routine missing lemma would conceal the central RH difficulty.

## Separate engineering blocker

The review reports that a normal target build stops at the import `RHRestrictedWeilCriterionV13` (unknown module prefix). The PR's replay workflow assembles dependencies from AEGIS-OMEGA and the Li-criterion repository, patches a provider source for compatibility, and compiles modules with raw `lean -o`. This may be useful as a reproducible research replay, but it is not a self-contained upstream project build and does not establish the mathematics.

The audit must keep these statuses distinct:

- **Build/integration:** whether the exact target and all imports build from declared, pinned dependencies.
- **Kernel trust:** whether the target's transitive theorem dependencies use only allowed axioms and contain no admitted proof.
- **Mathematics:** whether the universal sign premise is actually derived without assuming RH or an equivalent statement.

A green build in an isolated assembled environment is evidence for compilation in that environment only.

## Execution plan

### Gate 0 — freeze and reproduce

1. Pin the fork HEAD, base SHA, Lean toolchain, Mathlib revision, provider SHAs, and source blob hashes.
2. Reproduce the reviewer-reported first-import failure with a clean ordinary build.
3. Reproduce the target's residual goal in the isolated replay environment, recording the full compiler output and exact command.
4. Preserve logs and receipts; do not overwrite source or cache artifacts while diagnosing.

**Exit condition:** two separate receipts: ordinary-build/import disposition and mathematical residual-goal disposition.

### Gate 1 — close the dependency/provenance audit

1. Compute the complete transitive import graph for `RHRestrictedWeilCriterionV13` and the official RH target.
2. For every module, record repository, commit SHA, path, source hash, compiler command, and whether it is upstream, fork-native, or a compatibility override.
3. Diff every `Compat/` file against its upstream counterpart; explicitly flag changed theorem statements and missing declarations.
4. Keep any raw-Lean replay in a clearly labelled research workflow; do not present it as the standard upstream build.

**Exit condition:** every imported declaration has auditable source provenance and a reproducible build recipe.

### Gate 2 — attack the mathematical obstruction, not the wrapper

Work on this exact target first:

`UniversalZeroQuadraticNonnegativeV10`

1. Expand the definition of `FinalSignResidualV1` and `ZeroShiftComponentDominanceV1`; compare their quantifiers, domains, admissibility conditions, and signs with the zero-quadratic target.
2. Search all archived Lean sources for unconditional producers of the precise missing interfaces named in `research/rh/RH_PROOF_JUNCTIONS_20261008.md`, especially:
   - `FixedKernelArithmeticRemainderBoundedV1`
   - `SubexponentialAtTopV1 (primeOnlyOrbitV1 detectingPacket)`
   - the positive-half-line exponential-type-zero bound `hPrime`
   - the bounded arithmetic / `-K(-t)` comparison `hBridge`
3. For each candidate producer, inspect its full statement and transitive dependencies. Reject it if it assumes RH, the final sign, the universal zero-quadratic inequality, or a proposition already equivalent to one of them.
4. Prioritize one concrete producer and compile it independently; do not add another stack of theorem names until it closes an identified premise.
5. If no unconditional producer exists in the corpus, record that as a verified search result, then derive a new analytic inequality from the explicit formula or prime-only representation. The needed statement must cover the full unbounded parameter range, not just finitely many windows.

**Exit condition:** an unconditional Lean theorem inhabiting the exact missing proposition, with source-bound dependencies and no circular premise. If this cannot yet be produced, leave the official theorem open and record the precise residual goal.

### Gate 3 — adversarial mathematical checks

For every proposed global inequality:

1. Check normalization, signs, complex conjugation, zero multiplicities, trivial/pole contributions, and all convergence/interchange hypotheses.
2. Test boundary cases around (L=693/2000), then test the large-(L) regime; finite numerical certificates are diagnostics, not a proof of a universal statement.
3. Verify whether monotonicity genuinely extends a bound to larger (L). The current cutoff argument only propagates a known cutoff result to smaller windows.
4. Build a dependency audit that detects circularity, including the RH-to-sign direction.
5. Run `#print axioms` on the new producer, its consumer, and the final theorem. Allow only the repository's explicitly accepted foundational axioms; reject `sorryAx`, `admit`, unapproved axioms, and external unverified theorem authority.

**Exit condition:** proof review plus kernel audit, not merely numerical agreement or successful elaboration of helper modules.

### Gate 4 — official target and repository admission

1. Replace the target's application only after the large-window premise has a proven producer.
2. Compile `FormalConjectures/Millennium/RiemannHypothesis.lean` in the repository's standard build system with declared dependencies only.
3. Run the official target gate and inspect the complete receipt; do not force a successful exit code into an audit after a failed compile.
4. Confirm the theorem is still the official Mathlib `RiemannHypothesis`, with unchanged semantics.
5. Minimize the eventual upstream patch to the official theorem and only the necessary accepted support files; keep the large research archive and unrelated results out of the upstream PR.

**Exit condition:** clean standard build, closed goal, acceptable axiom report, reproducible commit-pinned evidence, and independent mathematical review.

## Immediate next experiment

Search and audit the four interfaces listed under Gate 2, starting with the prime-only `hPrime` / `hBridge` path referenced by the existing proof-junction crosswalk. The result must be one of:

- **PRODUCER FOUND:** exact declaration + source hash + complete dependency/axiom audit + consumer compilation;
- **CANDIDATE FALSIFIED:** the declaration is conditional, circular, has mismatched quantifiers, or does not imply the target;
- **NO PRODUCER IN AUDITED CORPUS:** list the searched source roots and exact names, then state the remaining mathematical lemma precisely.

Do not reopen PR #7031 with the same theorem application or with CI changes that merely make external imports visible. Do not describe RH as proved until the official target closes unconditionally and passes the kernel audit.

## Evidence links

- PR/review: https://github.com/google-deepmind/formal-conjectures/pull/7031#pullrequestreview-5467416079
- Official target: https://github.com/tarikskalic33/formal-conjectures/blob/37e8a5dd1fd7febec380dd562417168714cc86c4/FormalConjectures/Millennium/RiemannHypothesis.lean
- Canonical join: https://github.com/tarikskalic33/formal-conjectures/blob/37e8a5dd1fd7febec380dd562417168714cc86c4/AegisRH/SmallWindow/RHSmallWindowCanonicalJoinV1.lean
- Millennium gate: https://github.com/tarikskalic33/formal-conjectures/blob/37e8a5dd1fd7febec380dd562417168714cc86c4/AegisRH/PR606/Source/RHMillenniumGateV10.lean
- Existing proof-junction crosswalk: https://github.com/tarikskalic33/formal-conjectures/blob/37e8a5dd1fd7febec380dd562417168714cc86c4/research/rh/RH_PROOF_JUNCTIONS_20261008.md


## Follow-up source inspection — prime-only terminal

The archived prime-only route is now source-inspected at the audited HEAD:

- `AEGISOverlay/RHPrimeOnlyGrowthBridgeV1.lean` explicitly says that neither the prime-only subexponential estimate nor the kernel/arithmetic bounded-remainder estimate is proved; both remain inputs to its terminal.
- `AEGISOverlay/RHKernelSubexponentialV1.lean` says the subexponential estimate is not proved and identifies a dyadic self-compression bound as a possible arithmetic target, but does not assert such a bound.
- `AEGISOverlay/RHPrimeOnlyReflectedBridgeV2.lean` gives the corrected reflected orientation, comparing the arithmetic orbit with `-K(-t)), not `K(t)`. Its bridge is conditional.
- `AEGISOverlay/RHPrimeOnlyReflectedTailV3.lean` improves the needed bridge to an eventual tail bound, but the terminal still requires both:
  `hPrime : SubexponentialAtTopV1 (primeOnlyOrbitV1 detectingPacket)`
  and
  `hBridge : EventuallyReflectedFixedKernelArithmeticRemainderBoundedV3`.
  It derives RH from those premises; it does not produce either premise.

This makes the next experiment sharper: prove or falsify the **eventual reflected dictionary/remainder** from the exact signed-prime/actual-`B` identity on its stated separated-translation tail, including the analytic integrability/identification needed to connect Lean's totalized integrals to the source representation. Independently investigate the **prime-only subexponential estimate**; the file's proposed dyadic inequality is a conjectural target, not established evidence. Even if the bridge is proved, the prime-only growth bound remains a load-bearing RH-equivalent obligation and cannot be inferred from finite numerical windows.

The width-obstruction artifact `AEGISOverlay/RHWidthQuantifierObstructionV1.lean` is also important: it formally demonstrates that positivity at a width chosen separately for each finite dimension does not imply positivity at one fixed width for all dimensions. Do not globalize a finite-window or finite-shift result without a proved compatibility/convergence theorem for the actual quadratic form.


## Follow-up inspection — V8 narrows the open obligation further

The fork also contains `AEGISOverlay/RHSignedPrimeIntervalExtensionV8.lean`. At source level, it provides an unconditional chain:

`eventually_finite_chebyshev_integral_extends_v8`
→ `eventual_signed_prime_equals_combined_v8`
→ `eventual_reflected_kernel_remainder_bounded_v8`.

The V8 comments and theorem statements say that the Abel/Chebyshev dictionary and the eventual reflected-kernel remainder no longer need an extra dictionary premise. The actual RH consumer is then

`riemannHypothesis_of_prime_only_subexponential_growth_v8`

with the sole explicit input

`hPrime : SubexponentialAtTopV1 (primeOnlyOrbitV1 detectingPacket)`.

**Important evidence qualification:** I have inspected these source declarations, but this chat's connector returned no workflow runs for the audited HEAD. The V8 chain therefore still requires exact-head compilation and `#print axioms` replay before it can be labelled machine-verified in this audit.

The reflected bridge V2 proves that, given the bridge, the fixed packet's prime-only subexponential estimate is equivalent to RH. Since V8 purports to supply that bridge unconditionally, proving `hPrime` is not a routine engineering task: it is the remaining RH-equivalent arithmetic growth theorem on this route.

### Revised immediate experiment

1. Compile V8 and its complete import closure at the pinned HEAD; run `#print axioms` for the three dictionary/remainder producers and the RH consumer.
2. Confirm the V8 source has no hidden premise or declaration mismatch and that its integrals are connected to the analytic source representation under proved integrability conditions.
3. Then focus solely on the prime-only estimate. First formalize the proposed dyadic self-compression target for `S(d) = primeOnlyOrbitV1 detectingPacket d`; prove it from the explicit prime discrepancy formula or refute the proposed bound with a valid counterexample. If the dyadic inequality is insufficient under the exact definition of `SubexponentialAtTopV1`, state and prove the required stronger estimate.
4. Do not claim closure if the proof of the growth estimate invokes RH, the universal zero-quadratic sign, fixed-packet sign positivity, or the equivalent eventual boundedness criterion.

This is the shortest identified route in the current source corpus: the reflected kernel dictionary is supplied at source level by V8; the prime-only subexponential bound remains the decisive mathematical obligation.
