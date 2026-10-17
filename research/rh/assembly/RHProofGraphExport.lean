/-
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
-/
import AEGISOverlay.AEGIS_RH_Unconditional
import AEGISOverlay.RHFiniteActualGramJoinV1
import AEGISOverlay.RHActualLocalGramCoercivityV1
import AEGISOverlay.RHActualMixedDefectV1
import AEGISOverlay.RHActualElevenLatticeV1
import RHFourBlockConcreteV3
import AEGISOverlay.RHActualUniversalFineGramV1
import AEGISOverlay.RHArchRow29V1
import AEGISOverlay.RHScaleRowCompositionV1
import AEGISOverlay.RHOptimizedSchurGlobalJoinV1
import AEGISOverlay.RHKreinMultiplicativeTransportV1
import AEGISOverlay.RHTimeSliceWeilV1
import AEGISOverlay.RHLogThreeSignedPrimeProducerV1
import AEGISOverlay.RHFourLogThreeActualPrimeV1
import AEGISOverlay.RHBaguaRotatingTwoPairMellinV1
import AEGISOverlay.RHNarrowDetectingTrigramDenseV1
import AEGISOverlay.RHGlobalizationChainV13
import AEGISOverlay.RHCrossRepositoryFiveSpineV1
import RHCofinalActualTerminalV1
import RHExistingProofFusionV1
import RHNineFacesV13
import RHCofinalSchurAdapterV1
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms
import Lean.Meta.Basic

open Lean Elab Command

set_option maxHeartbeats 0

elab "#export_rh_proof_graph" : command => do
  let env ← getEnv
  let roots : List Name := [
    "AEGIS.RHFiniteFinePartitionV1.exists_finite_smooth_local_partition",
    "AEGIS.RHActualUniversalFineGramV1.every_moment_zero_packet_actual_fine_gram",
    "AEGIS.RHActualUniversalFineGramV1.every_moment_zero_packet_actual_fine_gram_with_support",
    "AEGIS.RHActualUniversalFineGramV1.actual_sign_of_one_fine_mixed_budget",
    "AEGIS.RHActualUniversalFineGramV1.riemannHypothesis_of_one_actual_mixed_budget_per_packet",
    "AEGIS.RHActualUniversalFineGramV1.riemannHypothesis_of_universal_actual_signed_row_certificates",
    "AEGIS.RHActualMixedDefectV1.distinct_fine_prime_zero_below_log_two",
    "AEGIS.RHActualMixedDefectV1.distinct_fine_actual_B_below_log_two",
    "AEGIS.RHActualMixedDefectV1.distinct_fine_actual_B_q16_middle_gap",
    "AEGIS.RHArchRow29V1.geometric_arch_row_29",
    "AEGIS.RHArchRow29V1.actual_B_re_le_signed_prime_plus_arch145",
    "AEGIS.RHArchRow29V1.actual_far_fine_gram_coercive_of_signed_prime_arch29_row",
    "AEGIS.RHScaleRowCompositionV1.actual_nine_macro_coercive_of_signed_cross_rows",
    "AEGIS.RHOptimizedSchurGlobalJoinV1.actual_packet_sum_nonpositive_of_optimized_rows",
    "AEGIS.RHOptimizedSchurGlobalJoinV1.riemannHypothesis_of_optimized_actual_row_producer",
    "AEGIS.RHActualUniversalFineGramV1.every_packet_actual_fine_mixed_defect_lower_bound",
    "AEGIS.RHFourBlockPrimeEightV3.farthest_prime_sum_exact_v3",
    "AEGIS.RHFourBlockPrimeEightV3.farthest_B_norm_bound_v3",
    "AEGIS.RHFourBlockConcreteV3.four_packet_coercive_v3",
    "AEGIS.RHFourBlockConcreteV3.canonical_four_packet_sign_v3",
    "AEGIS.RHFourBlockIntegerWeightedSchurV1.actual_four_block_coercive_of_three_gap_bounds",
    "AEGIS.RHActualElevenLatticeV1.actual_eleven_lattice_arithmetic_nonpositive",
    "AEGIS.RHActualElevenLatticeV1.actual_eleven_lattice_q16_coercive",
    "AEGIS.RHActualElevenLatticeV1.actual_eleven_lattice_coercive",
    "AEGIS.RHActualElevenLatticeV1.actual_eleven_lattice_weighted_q16_coercive",
    "AEGIS.RHActualElevenLatticeV1.all_actual_eleven_mixed_bounds",
    "AEGIS.RHActualLocalGramCoercivityV1.every_packet_actual_fine_coercive_gram",
    "AEGIS.RHActualMixedDefectV1.actual_nine_over_64_mixed_norm_le",
    "AEGIS.RHAssemblyV1.narrow_window_schur_family",
    "AEGIS.RHAssemblyV1.narrow_window_schur_norm_family",
    "AEGIS.RHAssemblyV1.actual_global_signed_weil_iff_RiemannHypothesis",
    "AEGIS.RHAssemblyV1.riemannHypothesis_of_actual_global_signed_weil",
    "AEGIS.RHFourLogThreeWeightedRHBridgeV1.weighted_reconstruction_arithmetic_nonpositive",
    "AEGIS.RHFourLogThreeWeightedRHBridgeV1.riemannHypothesis_of_weighted_four_log_three_reconstruction",
    "AEGIS.RHFeshbachWeilClosureV2.riemannHypothesis_of_window_schur_families",
    "AEGIS.RHFiniteActualGramJoinV1.every_packet_actual_finite_gram",
    "AEGIS.RHCofinalSchurAdapterV1.actual_zero_quadratic_nonnegative_of_gram_bounds",
    /- Source-present stronger producers and independent RH routes.
        Recording a root does not establish the premises of its terminal. -/
    "AEGIS.RHKreinMultiplicativeTransportV1.every_moment_zero_packet_two_actual_weil_packets",
    "AEGIS.RHKreinMultiplicativeTransportV1.every_packet_actual_two_block_zero_quadratic",
    "AEGIS.RHKreinMultiplicativeTransportV1.every_moment_zero_packet_finite_actual_weil_partition",
    "AEGIS.RHActualMixedDefectV1.fine_cluster_nine_exact_counterpart",
    "AEGIS.RHActualMixedDefectV1.fine_cluster_nine_mixed_defect_opposite",
    "AEGIS.RHTimeSliceWeilV1.fsTwoThreeShiftGroup_dense",
    "AEGIS.RHTimeSliceWeilV1.fsTwoThreeDetectorSign_iff_riemannHypothesis",
    "AEGIS.RHTimeSliceWeilV1.timeSliceFamily_full_weighted_margin",
    "AEGIS.RHTimeSliceWeilV1.timeSliceFamily_signed_prime_arch29",
    "AEGIS.RHTimeSliceWeilV1.timeSliceEight_actual_full_gram",
    "AEGIS.RHTimeSliceWeilV1.bagua_time_64_pow_2_pow_3_q16",
    "AEGIS.RHBaguaActualWeilV1.bagua_actual_full_weighted_margin",
    "AEGIS.RHBaguaActualWeilV1.bagua_complementary_phase_coupling_margin",
    "AEGIS.RHLogThreeSignedPrimeProducerV1.actual_signed_prime_gap_two_log_three",
    "AEGIS.RHFourLogThreeActualPrimeV1.actual_prime_four_log_three_exact",
    "AEGIS.RHFourLogThreeActualPrimeV1.full_four_log_three_prime_row",
    "AEGIS.RHFourLogThreeActualPrimeV1.full_four_log_three_prime_row_arch29",
    "AEGIS.RHFourLogThreeActualPrimeV1.actual_mixed_B_norm_four_log_three",
    "AEGIS.RHFourLogThreeActualPrimeV1.actual_prime_four_log_three_signed_cost_at_centers",
    "AEGIS.RHFourLogThreeActualPrimeV1.actual_mixed_B_norm_at_centers",
    "AEGIS.RHFourLogThreeActualPrimeV1.actual_four_log_three_same_mother_family_sign",
    "AEGIS.RHFourLogThreeActualPrimeV1.actual_prime_four_log_three_complex_at_centers",
    "AEGIS.RHFourLogThreeActualPrimeV1.actual_prime_four_log_three_norm_cost_at_centers",
    "AEGIS.RHFourLogThreeActualPrimeV1.actual_four_log_three_prime_norm_family_sign",
    "AEGIS.RHFourLogThreeActualPrimeV1.actual_four_log_three_weighted_norm_coercive",
    "AEGIS.RHBaguaRotatingTwoPairMellinV1.rotatingBaguaCoeff_opposite",
    "AEGIS.RHBaguaRotatingTwoPairMellinV1.rotating_bagua_two_moments",
    "AEGIS.RHBaguaRotatingTwoPairMellinV1.rotating_bagua_complementary_moments",
    "AEGIS.RHBaguaRotatingTwoPairMellinV1.rotating_bagua_four_block_exact",
    "AEGIS.RHBaguaRotatingTwoPairMellinV1.rotating_bagua_actual_atom_mellin",
    "AEGIS.RHBaguaRotatingTwoPairMellinV1.rotating_bagua_fs_atom_mellin",
    "AEGIS.RHBaguaRotatingTwoPairMellinV1.rotating_bagua_four_phase_mellin_weil_coercive",
    "AEGIS.RHBaguaRotatingTwoPairMellinV1.rotating_bagua_two_point_mellin_and_moments",
    "AEGIS.RHBaguaRotatingTwoPairMellinV1.rotating_bagua_two_pair_four_phase_mellin_join",
    "AEGIS.RHBaguaRotatingTwoPairMellinV1.rotating_bagua_phase_zero",
    "AEGIS.RHBaguaRotatingTwoPairMellinV1.actual_sparse_walsh_bagua_mode_negative",
    "AEGIS.RHLogThreeSignedPrimeProducerV1.actual_two_log_three_gram_coercive",
    "AEGIS.RHNarrowDetectingTrigramDenseV1.dense_narrow_detector_iff_riemannHypothesis",
    "AEGIS.RHGlobalizationChainV13.rh_of_vanishing_error_on_exhaustion",
    "AEGIS.RHCrossRepositoryFiveSpineV1.narrow_packet_local_actual_arithmetic_sign",
    "AEGIS.RHCrossRepositoryFiveSpineV1.three_nine_faces_of_cofinal",
    "AEGIS.RHFixedPacketDenseShiftV1.dense_fixed_packet_sign_iff_universal",
    "AEGIS.RHActualElevenLatticeV1.actual_eleven_lattice_optimized_q16_coercive",
    "AEGIS.RHActualElevenLatticeV1.all_actual_eleven_diagonal_bounds",
    "AEGIS.RHActualUniversalFineGramV1.riemannHypothesis_of_uniform_actual_fine_mixed_budget",
    "AEGIS.RHActualUniversalFineGramV1.riemannHypothesis_of_universal_actual_q16_pair_certificates",
    "AEGIS.RHActualUniversalFineGramV1.actual_fine_gram_coercive_of_signed_real_row_certificate",
    "AEGIS.RHScaleRowCompositionV1.actual_weighted_schur_unequal_energy_from_fine_diagonals",
    "AEGIS.RHScaleRowCompositionV1.actual_optimized_weighted_schur_unequal_energy_from_fine_diagonals",
    "AEGIS.RHCofinalActualTerminalV1.universal_of_cofinal_lower_certificates",
    "AEGIS.RHCofinalActualTerminalV1.riemannHypothesis_of_cofinal_lower_certificates",
    "AEGIS.RHExistingProofFusionV1.signed_dictionary_and_reflected_tail",
    "AEGIS.RHExistingProofFusionV1.rh_iff_prime_only_orbit_eventually_bounded",
    "AEGIS.RHExistingProofFusionV1.complementary_packets_and_signed_dictionary",
    "AEGIS.RHSignedPrimeIntervalExtensionV8.eventual_signed_prime_equals_combined_v8",
    "AEGIS.RHSignedPrimeIntervalExtensionV8.eventual_reflected_kernel_remainder_bounded_v8",
    "AEGIS.RHSignedPrimeIntervalExtensionV8.riemannHypothesis_of_prime_only_subexponential_growth_v8",
    "AEGIS.RHNineFacesV13.rh_iff_all_windows_v13",
    "AEGIS.RHNineFacesV13.rh_iff_nat_windows_v13",
    "AEGIS.RHNineFacesV13.nine_faces_of_rh_v13"].map
      (fun s => (s.splitOn ".").foldl Name.str Name.anonymous)
  let mut pending := roots
  let mut seen : NameSet := {}
  let mut rows : Array Json := #[]
  while !pending.isEmpty do
    let n := pending.head!
    pending := pending.tail!
    if seen.contains n then continue
    seen := seen.insert n
    if let some ci := (env.setExporting false).find? n then
      let deps := ci.getUsedConstantsAsSet.toList
      pending := deps ++ pending
      let mod := match env.getModuleIdxFor? n with
        | some i => env.header.modules[i.toNat]!.module.toString
        | none => "RHProofGraphExport"
      let ax := match ci with | .axiomInfo _ => true | _ => false
      let axioms ← collectAxioms n
      rows := rows.push (Json.mkObj [
        ("identifier", toJson n.toString),
        ("module", toJson mod),
        ("type_expr", toJson (toString ci.type)),
        ("direct_dependencies", toJson (deps.map Name.toString)),
        ("is_axiom", toJson ax),
        ("axioms", toJson (axioms.map Name.toString)),
        ("has_body", toJson (ci.value? (allowOpaque := true)).isSome)])
    else
      throwError m!"RH_REQUIRED_PROOF_ROOT_NOT_IN_ENV: {n}"
  liftIO <| IO.FS.createDirAll "evidence-cofinal/assembly"
  liftIO <| IO.FS.writeFile "evidence-cofinal/assembly/proof-terms.json"
    (Json.mkObj [("roots",toJson (roots.map Name.toString)),
      ("declarations",Json.arr rows)]).pretty
  logInfo m!"PROOF_TERM_GRAPH_DECLARATIONS {rows.size}"

  /- Canonical proof search: check Lean definitional equality with the actual
     Mathlib RH target instead of comparing pretty-printed type strings.
     Every theorem imported into the kernel environment is considered. -/
  let (semanticRhNames, semanticTheoremsChecked) ← liftTermElabM do
    let rhType : Expr := mkConst ``RiemannHypothesis
    let mut rhProofNames : Array Name := #[]
    let mut checked : Nat := 0
    for (n, ci) in env.constants.toList do
      if let .thmInfo _ := ci then
        checked := checked + 1
        if (← Lean.Meta.isDefEq ci.type rhType) then
          rhProofNames := rhProofNames.push n
    return (rhProofNames, checked)
  logInfo m!"RH_SEMANTIC_THEOREMS_CHECKED {semanticTheoremsChecked} DEFEQ_RH_TYPE_CANDIDATES {semanticRhNames.size}"

  /- Unlike root-dependency traversal, this independent inventory scans EVERY
     declaration already present in the imported kernel environment. A valid
     theorem need not be referenced by one of our chosen 66 roots. The official
     RH target with 'sorry' may also appear, so record full axiom dependencies
     instead of treating any matching theorem name as proof authority. -/
  let mut importedRh : Array Json := #[]
  let mut inspected : Nat := 0
  for (n, ci) in env.constants.toList do
    inspected := inspected + 1
    let ty := toString ci.type
    if semanticRhNames.contains n then
      let axs ← collectAxioms n
      let mod := match env.getModuleIdxFor? n with
        | some i => env.header.modules[i.toNat]!.module.toString
        | none => "RHProofGraphExport"
      let ax := match ci with | .axiomInfo _ => true | _ => false
      importedRh := importedRh.push (Json.mkObj [
        ("identifier", toJson n.toString),
        ("module", toJson mod),
        ("type_expr", toJson ty),
        ("type_defeq_riemann_hypothesis", toJson true),
        ("is_axiom", toJson ax),
        ("axioms", toJson (axs.map Name.toString)),
        ("has_body", toJson (ci.value? (allowOpaque := true)).isSome)])
  liftIO <| IO.FS.writeFile "evidence-cofinal/assembly/environment-rh-candidates.json"
    (Json.mkObj [
      ("scope", toJson "all constants in the compiled/imported Lean environment"),
      ("inspected_count", toJson inspected),
      ("semantic_theorems_checked", toJson semanticTheoremsChecked),
      ("defeq_target_type", toJson "RiemannHypothesis"),
      ("declarations", Json.arr importedRh)]).pretty
  logInfo m!"RH_IMPORTED_ENVIRONMENT_SCANNED {inspected} DEFEQ_TYPE_CANDIDATES {importedRh.size}"

#export_rh_proof_graph
