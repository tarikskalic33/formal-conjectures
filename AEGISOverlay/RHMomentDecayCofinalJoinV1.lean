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

import WeilMomentAnnihilatorV1
import WeilAutocorrelationClosureV1
import ZeroCountingMellinSummabilityV1
import FormalConjecturesUtil.FixedWindowLimitBridge

open Filter Topology

namespace AEGIS.RHMomentDecayCofinalJoinV1

/-- Existing filter + existing Mellin decay; no positivity is assumed. -/
theorem corrected_packet_moments_and_decay (f : WeilCompactSmoothGV1) :
    WeilMomentConditionsV1 (WeilMomentAnnihilatorV1 f) ∧
      HasUniformMellinVerticalCubicDecayV1 (WeilMomentAnnihilatorV1 f).1 :=
  ⟨weil_moment_annihilator_moments_v1 f,
    weil_compact_smooth_mellin_vertical_cubic_decay_v1 (WeilMomentAnnihilatorV1 f)⟩

/-- Apply the summability theorem to the actual autocorrelation carrier. -/
theorem corrected_autocorrelation_zero_summable (f : WeilCompactSmoothGV1) :
    Summable (WeilZeroIndexSummandV1
      (WeilAutocorrelationV1 (WeilMomentAnnihilatorV1 f))) := by
  exact weil_compact_smooth_zero_summable_v1
    (WeilAutocorrelationCompactSmoothV1 (WeilMomentAnnihilatorV1 f))

/-- Norm convergence discharges scaled error directly, on the same sequence. -/
theorem scaled_error_of_cofinal_norm_convergence
    {N : ℕ → ℕ} {normSq : ℕ → ℝ} {normSqLimit : ℝ}
    (hN : Tendsto N atTop atTop)
    (hnorm : Tendsto normSq atTop (𝓝 normSqLimit)) :
    Tendsto
      (fun j => FormalConjecturesUtil.FixedWindowLimitBridge.invFourthError 0 (N j) *
        normSq j) atTop (𝓝 0) := by
  simpa using
    (FormalConjecturesUtil.FixedWindowLimitBridge.tendsto_invFourthError_along_cofinal hN).mul hnorm

/-- Use the existing limit bridge for the actual zero quadratic.
The finite lower bound and its actual approximation limit remain explicit. -/
theorem actual_zero_quadratic_nonnegative_of_cofinal_lower_bound
    (g : WeilCompactSmoothGV1)
    {N : ℕ → ℕ} {q normSq : ℕ → ℝ} {normSqLimit : ℝ}
    (hN : Tendsto N atTop atTop)
    (hq : Tendsto q atTop
      (𝓝 ((∑' rho : RiemannNontrivialZeroIndexV2,
        WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re)))
    (hnorm : Tendsto normSq atTop (𝓝 normSqLimit))
    (hlower : ∀ j,
      -(FormalConjecturesUtil.FixedWindowLimitBridge.invFourthError 0 (N j)) *
        normSq j ≤ q j) :
    0 ≤ (∑' rho : RiemannNontrivialZeroIndexV2,
      WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re :=
  FormalConjecturesUtil.FixedWindowLimitBridge.nonneg_of_cofinal_invFourth_fixed_window_lower_bound
    hN hq hnorm hlower

end AEGIS.RHMomentDecayCofinalJoinV1

#print axioms AEGIS.RHMomentDecayCofinalJoinV1.corrected_packet_moments_and_decay
#print axioms AEGIS.RHMomentDecayCofinalJoinV1.corrected_autocorrelation_zero_summable
#print axioms AEGIS.RHMomentDecayCofinalJoinV1.scaled_error_of_cofinal_norm_convergence
#print axioms AEGIS.RHMomentDecayCofinalJoinV1.actual_zero_quadratic_nonnegative_of_cofinal_lower_bound
