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
import RHKreinTrigramAdaptiveCells08V1
import WeilWindowExhaustionV1

/-!
AEGIS Ω adaptive trigram, memory-sharded kernel replay.
All 373 original rational `decide +kernel` checks remain in imported exact source modules.
No axioms, no sorry, no change to RH target.
-/

set_option autoImplicit false
noncomputable section
namespace AEGIS.RHKreinTrigramAdaptiveV1
open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinCellBatchV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1
open AEGIS.RHKreinFiniteCertificateDataV1
open AEGIS.RHKreinFirstCellV1
open AEGIS.RHKreinSecondCellReductionV1

/-- Same 375 original rational cells, folded in eight kernel-checked stages. -/
theorem finite_interval_nonneg : NonnegOnQ 0 300 := foldTo0374

theorem finiteIntervalCertificate_trigram_v1 : FiniteIntervalCertificateV1 := by
  intro t ht0 ht300
  exact finite_interval_nonneg t ht0 ht300

/-- The finite trigram certificate plus proved evenness and |t| >= 300 tail
supply the actual pointwise certificate at all real frequencies. -/
theorem pointwiseCertificate_trigram_v1 :
    AEGIS.RHKreinExplicitCorrectionV1.PointwiseCertificate :=
  AEGIS.RHKreinFiniteCertificateAssemblyV1.pointwiseCertificate_of_finite_interval_v1
    finiteIntervalCertificate_trigram_v1

/-- Actual 1/16 zero-quadratic margin for moment-zero packets of
logarithmic half-width at most 2/5; this does not assert RH. -/
theorem zero_quadratic_margin_trigram_v1
    (g : WeilCompactSmoothGV1) (r a : ℝ)
    (hr0 : 0 ≤ r) (hr : r ≤ 2 / 5)
    (hw : AEGIS.RHDyadicDiagonalV13.HalfWidthAt g r a)
    (hm : WeilMomentConditionsV1 g) :
    (1 / 16) * AEGIS.WeilDisjointEnergyV2.energy g.1 ≤
      (∑' rho : RiemannNontrivialZeroIndexV2,
        WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re := by
  exact AEGIS.RHKreinExplicitCorrectionV1.actual_zero_quadratic_margin
    pointwiseCertificate_trigram_v1 g r a hr0 hr hw hm

/-- Unconditional arithmetic Weil sign for every two-moment test packet
    whose logarithmic support is contained in a radius-2/5 window.
    The positive 1/16 spectral-energy margin is inherited from the genuine
    analytic Trigram certificate, not assumed as a hypothesis. -/
theorem arithmetic_sign_window_two_fifths_trigram_v1
    (g : WeilCompactSmoothGV1)
    (hw : AEGIS.RHDyadicDiagonalV13.HalfWidthAt g (2 / 5 : ℝ) 0)
    (hm : WeilMomentConditionsV1 g) :
    (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re ≤ 0 := by
  have hmargin :=
    zero_quadratic_margin_trigram_v1 g (2 / 5 : ℝ) 0
      (by norm_num) (by norm_num) hw hm
  have henergy :
      0 ≤ (1 / 16 : ℝ) * AEGIS.WeilDisjointEnergyV2.energy g.1 :=
    mul_nonneg (by norm_num)
      (AEGIS.WeilDisjointEnergyV2.energy_nonnegative g.1)
  exact
    (AEGIS.WeilAutocorrelationExplicitFormulaV10.autocorrelation_arithmetic_nonpositive_iff_zero_nonnegative_v10
      g hm).mpr (henergy.trans hmargin)

/-- A genuine unconditional radius-2/5 Weil window certificate,
    in precisely the original AEGIS WindowArithmeticNonpositiveV1 type. -/
theorem window_two_fifths_trigram_v1 :
    AEGIS.WeilWindowExhaustionV1.WindowArithmeticNonpositiveV1
      (2 / 5 : ℝ) := by
  intro g hm hw
  apply arithmetic_sign_window_two_fifths_trigram_v1 g ?_ hm
  change AEGIS.WeilThreeBlockTranslatedPacketsV22.LogSupportIn
    g (0 - (2 / 5 : ℝ)) (0 + (2 / 5 : ℝ))
  simpa only [AEGIS.WeilWindowExhaustionV1.LogWindowContainsV1,
    zero_sub, zero_add] using hw

/-- Monotone transfer of the genuine 2/5 certificate to every smaller
    positive log window, without any unproved global hypothesis. -/
theorem window_le_two_fifths_trigram_v1
    {L : ℝ} (hL : L ≤ (2 / 5 : ℝ)) :
    AEGIS.WeilWindowExhaustionV1.WindowArithmeticNonpositiveV1 L :=
  AEGIS.WeilWindowExhaustionV1.windowArithmeticNonpositive_mono_v1
    hL window_two_fifths_trigram_v1

end AEGIS.RHKreinTrigramAdaptiveV1

#print axioms AEGIS.RHKreinTrigramAdaptiveV1.finiteIntervalCertificate_trigram_v1
#print axioms AEGIS.RHKreinTrigramAdaptiveV1.pointwiseCertificate_trigram_v1
#print axioms AEGIS.RHKreinTrigramAdaptiveV1.zero_quadratic_margin_trigram_v1
#print axioms AEGIS.RHKreinTrigramAdaptiveV1.arithmetic_sign_window_two_fifths_trigram_v1
#print axioms AEGIS.RHKreinTrigramAdaptiveV1.window_two_fifths_trigram_v1
#print axioms AEGIS.RHKreinTrigramAdaptiveV1.window_le_two_fifths_trigram_v1
