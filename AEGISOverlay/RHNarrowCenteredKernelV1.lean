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

import AEGISOverlay.RHNarrowFixedDetectorV1

/-!
# Centered two-point Weil window for the one narrow detector

Use the genuine 7/32 half-width three-cell certificate, centered at d/2
rather than the origin. This doubles the rigorously certified translation
interval to |d| ≤ 3/8, for every complex coefficient c.

All statements concern the SAME previously constructed narrow detector.
They do not assert unrestricted-shift positivity or the Riemann hypothesis.
-/

set_option autoImplicit false
noncomputable section

open Set Complex
open scoped ComplexConjugate

namespace AEGIS.RHNarrowCenteredKernelV1

open AEGIS.RHNarrowFixedDetectorV1
open AEGIS.WeilZeroTwoPointV11
open AEGIS.WeilZeroTranslationV11
open AEGIS.WeilZeroKernelHermitianV11
open AEGIS.WeilAutocorrelationExplicitFormulaV10

/-- Recenter the two translated supports at d/2 to use both sides of
    the certified 7/32 window. The admissible shift doubles to 3/8. -/
theorem centered_twoPoint_halfWidth (d : ℝ)
    (hd : |d| ≤ (3 / 8 : ℝ)) (c : ℂ) :
    AEGIS.RHDyadicDiagonalV13.HalfWidthAt
      (WeilTwoPointTranslateV11 narrowDetectingPacket d c)
      (7 / 32 : ℝ) (d / 2) := by
  let g := narrowDetectingPacket
  have hdlo := (abs_le.mp hd).1
  have hdhi := (abs_le.mp hd).2
  have hg : AEGIS.WeilThreeBlockTranslatedPacketsV22.LogSupportIn
      g (-(1 / 32 : ℝ)) (1 / 32 : ℝ) :=
    narrowDetectingPacket_logWindow
  have hleft : AEGIS.WeilThreeBlockTranslatedPacketsV22.LogSupportIn
      g (d / 2 - (7 / 32 : ℝ)) (d / 2 + (7 / 32 : ℝ)) := by
    intro t ht
    have h := hg ht
    exact ⟨by linarith [h.1, hdhi], by linarith [h.2, hdlo]⟩
  have htrans := AEGIS.WeilThreeBlockTranslatedPacketsV22.translate_logSupportIn
    g d (-(1 / 32 : ℝ)) (1 / 32 : ℝ) hg
  have hright : AEGIS.WeilThreeBlockTranslatedPacketsV22.LogSupportIn
      (AEGIS.WeilThreeBlockTranslatedPacketsV22.translatePacket g d)
      (d / 2 - (7 / 32 : ℝ)) (d / 2 + (7 / 32 : ℝ)) := by
    intro t ht
    have h := htrans ht
    exact ⟨by linarith [h.1, hdlo], by linarith [h.2, hdhi]⟩
  change AEGIS.WeilThreeBlockTranslatedPacketsV22.LogSupportIn
    (WeilTwoPointTranslateV11 g d c)
    (d / 2 - (7 / 32 : ℝ)) (d / 2 + (7 / 32 : ℝ))
  unfold AEGIS.WeilThreeBlockTranslatedPacketsV22.LogSupportIn
  apply closure_minimal ?_ isClosed_Icc
  intro t ht
  by_contra houtside
  have hfirst : AEGIS.WeilLogCoordinateIsometryV21.logLift g.1 t = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hs => houtside (hleft hs))
  have hsecond :
      AEGIS.WeilLogCoordinateIsometryV21.logLift
        (AEGIS.WeilThreeBlockTranslatedPacketsV22.translatePacket g d).1 t = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hs => houtside (hright hs))
  have heq :
      AEGIS.WeilLogCoordinateIsometryV21.logLift
        (WeilTwoPointTranslateV11 g d c).1 t =
        AEGIS.WeilLogCoordinateIsometryV21.logLift g.1 t +
        c * AEGIS.WeilLogCoordinateIsometryV21.logLift
          (AEGIS.WeilThreeBlockTranslatedPacketsV22.translatePacket g d).1 t := by
    change ((Real.exp (t / 2) : ℂ) *
        (g.1 (Real.exp t) +
          c * (AEGIS.WeilThreeBlockTranslatedPacketsV22.translatePacket g d).1
            (Real.exp t))) =
      ((Real.exp (t / 2) : ℂ) * g.1 (Real.exp t)) +
        c * ((Real.exp (t / 2) : ℂ) *
          (AEGIS.WeilThreeBlockTranslatedPacketsV22.translatePacket g d).1
            (Real.exp t))
    ring
  apply ht
  rw [heq, hfirst, hsecond]
  ring

/-- Arithmetic nonpositivity of the actual two-point Weil packet throughout
    the centered 3/8 interval, for all complex coefficients c. -/
theorem centered_twoPoint_arithmetic_nonpositive (d : ℝ)
    (hd : |d| ≤ (3 / 8 : ℝ)) (c : ℂ) :
    (WeilExplicitRightSideV1
      (WeilAutocorrelationV1
        (WeilTwoPointTranslateV11 narrowDetectingPacket d c))).re ≤ 0 := by
  have hm := twoPointTranslate_preserves_moments_v11
    narrowDetectingPacket d c narrowDetectingPacket_moments
  have hc := AEGIS.RHThreeCellClassV13.cell_coercive
    (WeilTwoPointTranslateV11 narrowDetectingPacket d c)
    (d / 2) (centered_twoPoint_halfWidth d hd c) hm
  have he := AEGIS.WeilDisjointEnergyV2.energy_nonnegative
    (WeilTwoPointTranslateV11 narrowDetectingPacket d c).1
  linarith

/-- The real zero quadratic inherits the centered arithmetic certificate. -/
theorem centered_twoPoint_zero_quadratic_nonnegative (d : ℝ)
    (hd : |d| ≤ (3 / 8 : ℝ)) (c : ℂ) :
    0 ≤ (WeilAutocorrelationZeroQuadraticV11
      (WeilTwoPointTranslateV11 narrowDetectingPacket d c)).re := by
  have hm := twoPointTranslate_preserves_moments_v11
    narrowDetectingPacket d c narrowDetectingPacket_moments
  exact
    (autocorrelation_arithmetic_nonpositive_iff_zero_nonnegative_v10
      (WeilTwoPointTranslateV11 narrowDetectingPacket d c) hm).mp
        (centered_twoPoint_arithmetic_nonpositive d hd c)

/-- Real and imaginary cross-kernel bounds for every centered shift. -/
theorem centered_kernel_components (d : ℝ)
    (hd : |d| ≤ (3 / 8 : ℝ)) :
    |(WeilZeroTranslationKernelV11 narrowDetectingPacket d).re| ≤
      (WeilAutocorrelationZeroQuadraticV11 narrowDetectingPacket).re ∧
    |(WeilZeroTranslationKernelV11 narrowDetectingPacket d).im| ≤
      (WeilAutocorrelationZeroQuadraticV11 narrowDetectingPacket).re := by
  apply weil_four_phase_nonnegative_components_v1
  intro c _hc
  rw [← AEGIS.RHFixedPacketFourPhaseV1.twoPoint_zero_quadratic_re_eq_four_phase_value
    narrowDetectingPacket narrowDetectingPacket_moments d c]
  exact centered_twoPoint_zero_quadratic_nonnegative d hd c

/-- Uniform norm bound on the true zero translation kernel, over |d| ≤ 3/8. -/
theorem centered_kernel_norm_bound (d : ℝ)
    (hd : |d| ≤ (3 / 8 : ℝ)) :
    ‖WeilZeroTranslationKernelV11 narrowDetectingPacket d‖ ≤
      2 * (WeilAutocorrelationZeroQuadraticV11 narrowDetectingPacket).re := by
  apply weil_four_phase_nonnegative_norm_bound_v1
  intro c _hc
  rw [← AEGIS.RHFixedPacketFourPhaseV1.twoPoint_zero_quadratic_re_eq_four_phase_value
    narrowDetectingPacket narrowDetectingPacket_moments d c]
  exact centered_twoPoint_zero_quadratic_nonnegative d hd c

end AEGIS.RHNarrowCenteredKernelV1

#print axioms AEGIS.RHNarrowCenteredKernelV1.centered_twoPoint_halfWidth
#print axioms AEGIS.RHNarrowCenteredKernelV1.centered_twoPoint_arithmetic_nonpositive
#print axioms AEGIS.RHNarrowCenteredKernelV1.centered_twoPoint_zero_quadratic_nonnegative
#print axioms AEGIS.RHNarrowCenteredKernelV1.centered_kernel_components
#print axioms AEGIS.RHNarrowCenteredKernelV1.centered_kernel_norm_bound
