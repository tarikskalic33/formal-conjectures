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

import RHFeshbachScaledErrorV1
import RHExistingProofFusionV1

/-!
Source-bound scaled Weil adapter. Same actual zeta-zero quadratic and
Feshbach lower bound; scaled-error convergence replaces norm convergence.
The all-packet family remains an explicit typed input, not an axiom.
-/

open Filter Topology

namespace AEGIS.RHFeshbachScaledWeilV1

structure PacketScaledSchurFamily (g : WeilCompactSmoothGV1) where
  N : ℕ → ℕ
  a : ℕ → ℝ
  re_b : ℕ → ℝ
  q : ℕ → ℝ
  nv : ℕ → ℝ
  nw : ℕ → ℝ
  β : ℕ → ℝ
  c : ℕ → ℝ
  μ : ℕ → ℝ
  normSq : ℕ → ℝ
  cofinal : Tendsto N atTop atTop
  reproducesZeroQuadratic : Tendsto
    (fun j => a j + 2 * re_b j + q j) atTop
    (𝓝 ((∑' rho : RiemannNontrivialZeroIndexV2,
      WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re))
  scaledErrorVanishes : Tendsto
    (fun j =>
      FormalConjecturesUtil.FixedWindowLimitBridge.invFourthError 0 (N j) *
        normSq j) atTop (𝓝 0)
  shiftNonnegative : ∀ j, 0 ≤ μ j
  tailNonnegative : ∀ j, 0 ≤ nw j
  tailCoercivity : ∀ j, c j * nw j ^ 2 ≤ q j
  crossBound : ∀ j, re_b j ^ 2 ≤ β j * nw j ^ 2
  betaNonnegative : ∀ j, 0 ≤ β j
  shiftBelowGap : ∀ j, μ j < c j
  schurLower : ∀ j,
    -(FormalConjecturesUtil.FixedWindowLimitBridge.invFourthError 0 (N j)) *
      normSq j ≤ a j - μ j * nv j ^ 2 - β j / (c j - μ j)

/-- Exact actual zero quadratic from a scaled-error Schur family. -/
theorem packet_zero_quadratic_nonnegative
    (g : WeilCompactSmoothGV1) (h : PacketScaledSchurFamily g) :
    0 ≤ (∑' rho : RiemannNontrivialZeroIndexV2,
      WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re := by
  apply AEGIS.RHFeshbachScaledErrorV1.nonneg_of_invFourth_scaled_error
    h.reproducesZeroQuadratic h.scaledErrorVanishes
  intro j
  have hshift : 0 ≤ h.μ j * (h.nv j ^ 2 + h.nw j ^ 2) :=
    mul_nonneg (h.shiftNonnegative j)
      (add_nonneg (sq_nonneg _) (sq_nonneg _))
  calc
    -(FormalConjecturesUtil.FixedWindowLimitBridge.invFourthError 0 (h.N j)) *
        h.normSq j ≤ h.a j - h.μ j * h.nv j ^ 2 - h.β j / (h.c j - h.μ j) :=
      h.schurLower j
    _ ≤ h.a j + 2 * h.re_b j + h.q j -
          h.μ j * (h.nv j ^ 2 + h.nw j ^ 2) :=
      AEGIS.RHFeshbachCoreV1.feshbach_lower
        (h.a j) (h.re_b j) (h.q j) (h.nv j) (h.nw j)
        (h.β j) (h.c j) (h.μ j)
        (h.tailNonnegative j) (h.tailCoercivity j)
        (h.crossBound j) (h.betaNonnegative j) (h.shiftBelowGap j)
    _ ≤ h.a j + 2 * h.re_b j + h.q j := sub_le_self _ hshift

theorem packet_weil_nonpositive
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g)
    (h : PacketScaledSchurFamily g) :
    (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re ≤ 0 :=
  (AEGIS.WeilAutocorrelationExplicitFormulaV10.autocorrelation_arithmetic_nonpositive_iff_zero_nonnegative_v10
    g hm).mpr (packet_zero_quadratic_nonnegative g h)

/-- Typed RH terminal; no new premise is hidden in the proof body. -/
theorem riemannHypothesis_of_window_scaled_schur_families
    (h : ∀ n : ℕ, 0 < n →
      ∀ g : WeilCompactSmoothGV1,
        WeilMomentConditionsV1 g →
        AEGIS.WeilWindowExhaustionV1.LogWindowContainsV1 g
          ((n : ℝ) * Real.pi) →
        PacketScaledSchurFamily g) :
    RiemannHypothesis := by
  apply AEGIS.RHExistingProofFusionV1.rh_iff_pi_nat_windows.mpr
  intro n hn g hm hw
  exact packet_weil_nonpositive g hm (h n hn g hm hw)

end AEGIS.RHFeshbachScaledWeilV1

#print axioms AEGIS.RHFeshbachScaledWeilV1.packet_zero_quadratic_nonnegative
#print axioms AEGIS.RHFeshbachScaledWeilV1.packet_weil_nonpositive
#print axioms AEGIS.RHFeshbachScaledWeilV1.riemannHypothesis_of_window_scaled_schur_families
