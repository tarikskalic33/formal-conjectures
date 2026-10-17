# AEGIS Ω — strongest recovered RH proof producers (2026-10-16)

## Authority and precise scope

This is a source-intake and proof-composition atlas, **not an unconditional RH certificate**.
It is grounded in the exact source of PR #89 inherited from PR #88, the source-bound
PR #88 replay package, and separate AEGIS / fork historical branches.
New integration changes are deliberately limited to PR #89. No mathematical theorem
statement, canonical RH definition, or protected `main` has been changed.

**Root-selection regression fixed:** Earlier `RHProofGraphExport.lean` listed just
26 roots on the PR #88 archived receipt (28 before this update on PR #89), while
the archived import closure contained 311 Lean source modules and 68,856
**reachable declarations**, mostly library dependencies. The small root selection
cannot substantiate a negative claim about the complete AEGIS corpus.
This PR now selects 66 source-present roots across established lanes and
fails explicitly if selected roots are absent. The separate Python evidence
emitter enforces 17 non-droppable mathematical roots. These numbers describe
**scope of inspection**, not numbers of RH proofs. The new exact-head CI must
still run before a successful updated-root replay can be claimed.

## Source-backed strongest results and their actual domains

| Producer / source | Actual theorem scope | Mathematical output | What cannot be inferred merely from this theorem |
|---|---|---|---|
| `AEGIS.RHKreinMultiplicativeTransportV1.every_moment_zero_packet_finite_actual_weil_partition` / `AEGISOverlay/RHKreinMultiplicativeTransportV1.lean` | Every moment-zero test packet; **arbitrary finite smooth partition of unity** | Actual Weil test packets; both annihilated moments preserved; exact reconstruction | No mixed-sign inequality is part of this result |
| `AEGIS.RHKreinMultiplicativeTransportV1.every_packet_actual_two_block_zero_quadratic` / same file | Every moment-zero packet and smooth splitter | Actual two-block decomposition and full zeta-zero quadratic identity with genuine `B(u,v)` mixed term | Identity alone does not assign the mixed-term sign |
| `AEGIS.RHActualUniversalFineGramV1.every_moment_zero_packet_actual_fine_gram_with_support` / `AEGISOverlay/RHActualUniversalFineGramV1.lean` | **Every** moment-zero compact smooth Weil packet | Existential finite fine partition with individual centers, width-1/128 support, each diagonal gain `5671/3200`, exact full genuine Gram identity | Does not constrain the distances between all its independently located centers |
| `AEGIS.RHActualMixedDefectV1.fine_cluster_nine_exact_counterpart` / `AEGISOverlay/RHActualMixedDefectV1.lean` | Every finite family of moment-zero fine atoms and **every complex coefficient vector**, provided all centers lie within `35/256` of a common center | Actual signed Weil coercivity with `1/10` energy; full mixed contributions retained | The common-center hypothesis is substantive; it is not present in every arbitrary fine partition |
| `AEGIS.RHActualElevenLatticeV1.actual_eleven_lattice_arithmetic_nonpositive` / `AEGISOverlay/RHActualElevenLatticeV1.lean` | Every width-1/128 moment-zero **mother packet** and every complex combination of its 11 specified lattice translates | Unconditional actual arithmetic Weil nonpositivity for the entire 11-lattice family and genuine 55 mixed pairs | Does not assert every arbitrary compact packet equals a lattice combination |
| `AEGIS.RHActualElevenLatticeV1.actual_eleven_lattice_optimized_q16_coercive` / same file | The same source-specific 11-translates family, with actual arithmetic `B` estimates | Optimized outward-rounded Q16.16 coercivity | Numeric margin by itself does not widen the family of test packets |
| `AEGIS.RHBaguaActualWeilV1.bagua_actual_full_weighted_margin` and `bagua_complementary_phase_coupling_margin` / `AEGISOverlay/RHBaguaActualWeilV1.lean` | Precise finite Bagua/Walsh sectors and window premises of those declarations | Exact genuine mixed Gram and signed complementary-sector controls | No automatic unrestricted support exhaustion |
| `AEGIS.RHTimeSliceWeilV1.fsTwoThreeShiftGroup_dense` / `AEGISOverlay/RHTimeSliceWeilV1.lean` | Entire real translation axis | Density of additive subgroup from exact `log 2` and `log 3` femtosecond reparameterized spectral shifts | Density alone does not certify a sign at the sampled shifts |
| `AEGIS.RHTimeSliceWeilV1.timeSliceFamily_full_weighted_margin` / same file | Every finite exact time-slice family subject to stated common-window geometry | Full Weil mixed-family weighted coercivity | Geometry on arbitrary shifts is an explicit premise |
| `AEGIS.RHSignedPrimeIntervalExtensionV8.eventual_signed_prime_equals_combined_v8` / `AEGISOverlay/RHSignedPrimeIntervalExtensionV8.lean` | The actual signed Abel/Chebyshev prime integral dictionary, eventually in its proved parameter regime | **Unconditional** exact signed-prime-to-combined arithmetic identity | Not an unconditional growth or sign bound on every shift |
| `AEGIS.RHSignedPrimeIntervalExtensionV8.eventual_reflected_kernel_remainder_bounded_v8` / same file | Eventual reflected remainder in the V8 dictionary | **Unconditional** bounded remainder bridge | Cannot be silently substituted for `SubexponentialAtTopV1 primeOnlyOrbitV1` |
| `AEGIS.RHExistingProofFusionV1.complementary_packets_and_signed_dictionary` / `AEGISOverlay/RHExistingProofFusionV1.lean` | Independent complementary moment-zero partition and the V8 signed-prime dictionary | Exact unconditional *combined* output preserving both separately proved facts | Neither conjunct by itself asserts the complete Weil sign |
| `AEGIS.RHLogThreeSignedPrimeProducerV1.actual_signed_prime_gap_two_log_three` / `AEGISOverlay/RHLogThreeSignedPrimeProducerV1.lean` | Actual signed von Mangoldt cross contribution on the source's precise `2 log 3` gap geometry | Exact signed-prime gap estimate | No implicit bound across every unrelated center difference |
| `AEGIS.RHGlobalizationChainV13.globalization_limit_nonneg` / `AEGISOverlay/RHGlobalizationChainV13.lean` | Abstract convergence/lower-bound framework under its stated limits | Mathematically proved limit passage | It does not manufacture the concrete Weil bounds supplied as premises |
| `AEGIS.RHNarrowDetectingTrigramDenseV1.dense_narrow_detector_iff_riemannHypothesis` / `AEGISOverlay/RHNarrowDetectingTrigramDenseV1.lean` | Dense fixed detecting-packet four-phase tests | Exact RH equivalence on that detecting class | The sampled signed tests are a proposition to be established, not a new axiom |
| `AEGIS.RHNineFacesV13.nine_faces_of_rh_v13` / upstream AEGIS #679 imported source | Nine RH-equivalent criteria | Kernel-facing links among fixed-window, universal, prime, and zero sides | An equivalence is not an independent unconditional proof of either side |

## Already compiled sufficient RH terminals: compare, do not invent another criterion

1. `RHActualUniversalFineGramV1.riemannHypothesis_of_one_actual_mixed_budget_per_packet`:
   `∀ g, moment-zero g → ∃ n gs, reconstructed g ∧ diagonal gain ∧ actual mixed defect budget`.
   This needs **one certified genuine finite reconstruction for each original packet**,
   not a certified row bound for every possible partition.
2. `RHActualUniversalFineGramV1.riemannHypothesis_of_universal_actual_signed_row_certificates`:
   uses **signed real** `B` entries and a symmetric real row certificate.
3. `RHOptimizedSchurGlobalJoinV1.riemannHypothesis_of_optimized_actual_row_producer`:
   a stronger diagonal versus optimized *weighted* row interface whose
   `hselect` is not discharged by this terminal alone.
4. `RHSignedPrimeIntervalExtensionV8.riemannHypothesis_of_prime_only_subexponential_growth_v8`:
   uses the independently established V8 signed-prime dictionary, but assumes
   the exact prime-only orbit growth statement.
5. `RHCofinalActualTerminalV1.riemannHypothesis_of_cofinal_lower_certificates`:
   consumes actual packet-indexed cofinal certificates, with its exact convergence
   and bound hypotheses.
6. `RHTimeSliceWeilV1.riemannHypothesis_of_fsTwoThreeDetectorSign`:
   consumes global signed tests on the dense two-prime spectral subgroup.

The correct final criterion is *any one* mathematically sufficient terminal
whose hypotheses can be supplied by a proven unconditional producer. Neither
`hselect` nor a particular Schur normalization is mandated by the objective
`theorem unconditional_riemannHypothesis : RiemannHypothesis`.

## Non-repeatable integration checks

- Do not silently drop any of the 17 mandatory source roots. Enforce the guard
  in `research/rh/assembly/export_evidence.py`.
- Keep **source-present**, **selected-head kernel compiled**, **external verified
  historical source**, and **actual canonical RH closure** as different assertions.
- If a producer cannot be applied to an RH consumer, record the exact Lean type
  and failed unification, not a general claim that no universal theorem exists.
- Before introducing a new hypothesis or proof architecture, try each listed
  conditional terminal against **all** stronger existing sources.
- A null `RH_PROVEN_UNCONDITIONALLY` in a limited audit means "not established
  by those roots"; it is not evidence of impossibility elsewhere.
- No status-file rewrite may promote RH authority without a closed proof term,
  trusted kernel run, exact source/Mathlib SHA and foundational-axiom audit.

## Source anchors

- Fork [PR #89](https://github.com/tarikskalic33/formal-conjectures/pull/89),
  parent [PR #88](https://github.com/tarikskalic33/formal-conjectures/pull/88),
  historical [PR #83](https://github.com/tarikskalic33/formal-conjectures/pull/83).
- AEGIS [PR #679](https://github.com/Aegis-Omega/AEGIS-OMEGA/pull/679),
  [PR #721](https://github.com/Aegis-Omega/AEGIS-OMEGA/pull/721).
- The historical PR #88 source-bound replay package includes 311 source
  snapshots and 26 proof export roots; the PR #89 2026-10-16 work adds
  9 more recovered V8/fusion/Nine Faces roots to 57 earlier expanded roots.
- The AEGIS archive/corpus census reports numerous unindexed branches and
  1,353 distinct archived Git source blobs. The selected PR #89 DAG is
  **not** the complete cross-branch corpus.

**Next mathematically decisive action:** consume genuine signed mixed-term
information from the already proved prime/Arch and near-cluster lanes to
construct the *one-per-source-packet* certificate accepted by
`riemannHypothesis_of_one_actual_mixed_budget_per_packet`, OR
prove the exact fixed-detector sign on the dense group using the V8 signed
arithmetic bridge. Both are candidates, not predeclared unavoidable gaps.
