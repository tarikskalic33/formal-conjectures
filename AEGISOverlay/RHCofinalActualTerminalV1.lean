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

import RHMomentDecayCofinalJoinV1
import RHFeshbachWeilClosureV2
import RHRestrictedWeilBridgeV13

/-!
AEGIS Ω — cofinal actual-zero terminal, using the October 14 moment-decay join.
The all-packets cofinal certificate remains an explicit premise.
-/

open Filter Topology

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHCofinalActualTerminalV1

/-- For each actual moment-zero packet, a single cofinal approximant sequence
carries the zero sum, norm convergence and the genuine N^-4 lower bound. -/
def EveryPacketCofinalLowerCertificate : Prop :=
  ∀ g : WeilCompactSmoothGV1, WeilMomentConditionsV1 g →
    ∃ (N : ℕ → ℕ) (q normSq : ℕ → ℝ) (normSqLimit : ℝ),
      Tendsto N atTop atTop ∧
      Tendsto q atTop
        (𝓝 ((∑' rho : RiemannNontrivialZeroIndexV2,
          WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re)) ∧
      Tendsto normSq atTop (𝓝 normSqLimit) ∧
      (∀ j : ℕ,
        -(FormalConjecturesUtil.FixedWindowLimitBridge.invFourthError 0 (N j)) *
          normSq j ≤ q j)

/-- Reuse the kernel-checked cofinal lower-bound transfer without rebuilding it. -/
theorem universal_of_cofinal_lower_certificates
    (h : EveryPacketCofinalLowerCertificate) :
    AEGIS.RHMillenniumGateV10.UniversalZeroQuadraticNonnegativeV10 := by
  intro g hm
  obtain ⟨N, q, normSq, normSqLimit, hN, hq, hnorm, hlower⟩ := h g hm
  exact AEGIS.RHMomentDecayCofinalJoinV1.actual_zero_quadratic_nonnegative_of_cofinal_lower_bound
    g hN hq hnorm hlower

/-- The real Mathlib target; the all-packets certificate is still required. -/
theorem riemannHypothesis_of_cofinal_lower_certificates
    (h : EveryPacketCofinalLowerCertificate) : RiemannHypothesis :=
  AEGIS.RHRestrictedWeilBridgeV13.restricted_weil_criterion_kernel_bridge_v13
    (universal_of_cofinal_lower_certificates h)

end AEGIS.RHCofinalActualTerminalV1

#print axioms AEGIS.RHCofinalActualTerminalV1.universal_of_cofinal_lower_certificates
#print axioms AEGIS.RHCofinalActualTerminalV1.riemannHypothesis_of_cofinal_lower_certificates
