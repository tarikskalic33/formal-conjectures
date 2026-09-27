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

import RHKreinPrimeSymbolV1
import RHKreinFourierFactorV1
import Mathlib.Tactic

/-!
# Repository arithmetic RHS in Mathlib Fourier frequency

This module closes the normalization layer between the already kernel-checked
angular-frequency Krein identity and Mathlib's Fourier convention.

The existing angular theorem is stated in t with Fourier samples at
-t/(2*pi) and t/(2*pi). Here we change variables t = 2*pi*xi on the whole
real line. The Jacobian cancels the explicit 1/(4*pi) down to 1/2, with
both orientation channels retained.

The second theorem inserts the same-window factorization
logLift g = chi'' - chi/4, yielding the exact Mathlib-frequency multiplier

  W_M(xi) = ((2*pi*xi)^2 + 1/4)^2.

No parity shortcut is used here. The final reduction from the symmetric
two-channel mass to one Fourier mass is intentionally separate.

No positivity or RH conclusion is asserted.
-/

open Set MeasureTheory Complex FourierTransform
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHKreinRepositorySpectralBridgeV1

open AEGIS.RHKreinSymbolIntegrationV1
open AEGIS.RHKreinPrimeSymbolV1
open AEGIS.RHKreinFourierFactorV1
open AEGIS.RHDyadicDiagonalV13
open AEGIS.WeilLogCoordinateIsometryV21

/-- Exact Mathlib-frequency polynomial multiplier coming from chi'' - chi/4. -/
def mathlibWeight (xi : ℝ) : ℝ :=
  ((2 * Real.pi * xi) ^ 2 + 1 / 4) ^ 2

/-- The first-post-log2 Weil symbol in Mathlib frequency coordinates. -/
def mathlibSymbol (xi : ℝ) : ℝ :=
  (Complex.digamma
      ((1 / 4 : ℂ) + (((Real.pi * xi : ℝ) : ℂ) * I))).re -
    Real.log Real.pi -
    Real.sqrt 2 * Real.log 2 *
      Real.cos (2 * Real.pi * xi * Real.log 2)

/-- The explicit Mathlib-frequency symbol is exactly the existing angular
symbol evaluated at t = 2*pi*xi. -/
theorem mathlibSymbol_eq_angular_v1 (xi : ℝ) :
    mathlibSymbol xi = symbol (2 * Real.pi * xi) := by
  unfold mathlibSymbol symbol archSymbol
  have hz :
      (1 / 4 : ℂ) +
          (((2 * Real.pi * xi : ℝ) : ℂ) * I) / 2 =
        (1 / 4 : ℂ) + (((Real.pi * xi : ℝ) : ℂ) * I) := by
    push_cast
    ring
  rw [hz]
  ring

/-- The existing paired critical mass after the whole-line substitution
t = 2*pi*xi. -/
theorem criticalSpectralMass_two_pi_v1
    (g : WeilCompactSmoothGV1) (xi : ℝ) :
    criticalSpectralMass g (2 * Real.pi * xi) =
      Complex.normSq (𝓕 (logLift g.1) (-xi)) +
      Complex.normSq (𝓕 (logLift g.1) xi) := by
  unfold criticalSpectralMass
  have hp : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hneg : -(2 * Real.pi * xi) / (2 * Real.pi) = -xi := by
    field_simp [hp]
  have hpos : -(-(2 * Real.pi * xi)) / (2 * Real.pi) = xi := by
    field_simp [hp]
  rw [hneg, hpos]

/-- Whole-line change of variables from angular frequency to Mathlib
frequency. Both +/- xi Fourier channels remain visible. -/
theorem symbol_mass_angular_to_mathlib_v1
    (g : WeilCompactSmoothGV1) :
    (∫ t : ℝ, symbol t * criticalSpectralMass g t) =
      (2 * Real.pi) *
        ∫ xi : ℝ, mathlibSymbol xi *
          (Complex.normSq (𝓕 (logLift g.1) (-xi)) +
            Complex.normSq (𝓕 (logLift g.1) xi)) := by
  let Q : ℝ → ℝ := fun xi =>
    symbol (2 * Real.pi * xi) *
      criticalSpectralMass g (2 * Real.pi * xi)
  have hcv := Measure.integral_comp_div Q (2 * Real.pi)
  have hpi : 0 < (2 * Real.pi : ℝ) := by positivity
  have hlhs :
      (fun t : ℝ => Q (t / (2 * Real.pi))) =
        fun t : ℝ => symbol t * criticalSpectralMass g t := by
    funext t
    dsimp [Q]
    have hp : (2 * Real.pi : ℝ) ≠ 0 := ne_of_gt hpi
    have ht : 2 * Real.pi * (t / (2 * Real.pi)) = t := by
      field_simp [hp]
    rw [ht]
  rw [hlhs] at hcv
  rw [abs_of_pos hpi, Real.smul_def] at hcv
  calc
    (∫ t : ℝ, symbol t * criticalSpectralMass g t)
        = (2 * Real.pi) * ∫ xi : ℝ, Q xi := hcv
    _ = (2 * Real.pi) *
        ∫ xi : ℝ, mathlibSymbol xi *
          (Complex.normSq (𝓕 (logLift g.1) (-xi)) +
            Complex.normSq (𝓕 (logLift g.1) xi)) := by
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun xi => by
        dsimp [Q]
        rw [← mathlibSymbol_eq_angular_v1,
          criticalSpectralMass_two_pi_v1])

/-- KREIN_REPOSITORY_SPECTRAL_BRIDGE_V1, normalization layer.

For every repository packet whose full logarithmic support width is below
log 3, the actual repository arithmetic RHS is exactly the symmetric
Mathlib-frequency spectral integral. -/
theorem repository_arithmetic_rhs_mathlib_frequency_v1
    (g : WeilCompactSmoothGV1) (r a : ℝ)
    (hw : HalfWidthAt g r a) (hr : 2 * r < Real.log 3) :
    (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re =
      -(1 / 2 : ℝ) *
        ∫ xi : ℝ, mathlibSymbol xi *
          (Complex.normSq (𝓕 (logLift g.1) (-xi)) +
            Complex.normSq (𝓕 (logLift g.1) xi)) := by
  rw [actual_arithmetic_real_eq_symbol_integral g r a hw hr,
    symbol_mass_angular_to_mathlib_v1]
  have hp : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  field_simp [hp]
  ring

/-- Insert the repository same-window moment-zero factorization. -/
theorem repository_arithmetic_rhs_krein_factorized_v1
    (g : WeilCompactSmoothGV1) (r a : ℝ) (hr0 : 0 ≤ r)
    (hw : HalfWidthAt g r a) (hr : 2 * r < Real.log 3)
    (hm : WeilMomentConditionsV1 g) :
    ∃ chi : ℝ → ℂ,
      ContDiff ℝ ∞ chi ∧
      tsupport chi ⊆ Icc (a - r) (a + r) ∧
      Integrable chi ∧
      (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re =
        -(1 / 2 : ℝ) *
          ∫ xi : ℝ, mathlibSymbol xi * mathlibWeight xi *
            (Complex.normSq (𝓕 chi (-xi)) +
              Complex.normSq (𝓕 chi xi)) := by
  obtain ⟨chi, hchi, hchis, hchii, hfactor⟩ :=
    actual_packet_fourier_factor g (a - r) (a + r)
      (by linarith) hw hm
  refine ⟨chi, hchi, hchis, hchii, ?_⟩
  rw [repository_arithmetic_rhs_mathlib_frequency_v1 g r a hw hr]
  apply congrArg (fun x : ℝ => -(1 / 2 : ℝ) * x)
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun xi => by
    have hp : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    have hminus := hfactor (2 * Real.pi * xi)
    have hplus := hfactor (-(2 * Real.pi * xi))
    have hm1 : -(2 * Real.pi * xi) / (2 * Real.pi) = -xi := by
      field_simp [hp]
    have hp1 : -(-(2 * Real.pi * xi)) / (2 * Real.pi) = xi := by
      field_simp [hp]
    rw [hm1] at hminus
    rw [hp1] at hplus
    have hwgt :
        ((2 * Real.pi * xi) ^ 2 + 1 / 4) ^ 2 = mathlibWeight xi := by
      rfl
    have hwgt' :
        ((-(2 * Real.pi * xi)) ^ 2 + 1 / 4) ^ 2 = mathlibWeight xi := by
      unfold mathlibWeight
      ring
    rw [hwgt] at hminus
    rw [hwgt'] at hplus
    rw [hminus, hplus]
    ring)

end AEGIS.RHKreinRepositorySpectralBridgeV1

#print axioms AEGIS.RHKreinRepositorySpectralBridgeV1.mathlibSymbol_eq_angular_v1
#print axioms AEGIS.RHKreinRepositorySpectralBridgeV1.symbol_mass_angular_to_mathlib_v1
#print axioms AEGIS.RHKreinRepositorySpectralBridgeV1.repository_arithmetic_rhs_mathlib_frequency_v1
#print axioms AEGIS.RHKreinRepositorySpectralBridgeV1.repository_arithmetic_rhs_krein_factorized_v1
