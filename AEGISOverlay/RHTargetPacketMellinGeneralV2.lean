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

import RestrictedWeilCriterionResidueWitnessV11
import Mathlib.Tactic

/-!
AEGIS Omega -- general Mellin transform for the narrow targeted packet, V2.

This module upgrades the existing target-value identity for `TargetPacketV11 alpha`
to every complex Mellin parameter `s`:

  M(TargetPacketV11 alpha)(s)
    = s * (s - 1) * E(s - alpha),

where `E` is the bilateral exponential transform of the fixed seed `psi0`.
The proof is ordinary compact-support integration by parts encoded through
explicit antiderivatives. No RH statement is made.

AUTHORITY_EFFECT = NONE.
-/

open Set Filter MeasureTheory Complex
open scoped Topology ContDiff

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHTargetPacketMellinGeneralV2

open AEGIS.WeilMomentKillerConstructionV1
open AEGIS.RestrictedWeilCriterionTargetWitnessV11
open AEGIS.RestrictedWeilCriterionResidueWitnessV11

/-- Exponential weight in the logarithmic coordinate. -/
def weightV2 (s : ℂ) (u : ℝ) : ℂ :=
  Complex.exp (u • s)

/-- Entire seed transform used by the general target-packet formula. -/
def seedMellinV2 (z : ℂ) : ℂ :=
  ∫ u : ℝ, weightV2 z u * (psi0 u : ℂ)

private theorem contDiff_deriv_complex_v2
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (deriv f) :=
  (contDiff_infty_iff_deriv.mp hf).2

private theorem integral_deriv_eq_zero_complex_v2
    {F : ℝ → ℂ}
    (hF : ContDiff ℝ 1 F)
    (hFc : HasCompactSupport F) :
    ∫ u : ℝ, deriv F u = 0 := by
  have hint : Integrable (deriv F) :=
    (hF.continuous_deriv le_rfl).integrable_of_hasCompactSupport hFc.deriv
  have h :=
    intervalIntegral.integral_Iic_add_Ioi
      (f := deriv F) (b := (0 : ℝ))
      hint.integrableOn hint.integrableOn
  rw [HasCompactSupport.integral_Iic_deriv_eq hF hFc 0,
    HasCompactSupport.integral_Ioi_deriv_eq hF hFc 0] at h
  simpa using h.symm

private theorem weight_contDiff_v2 (s : ℂ) :
    ContDiff ℝ ∞ (weightV2 s) := by
  unfold weightV2
  fun_prop

/-- Compact-support integration by parts with a complex exponential weight. -/
theorem weighted_integral_deriv_v2
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hFc : HasCompactSupport F) (s : ℂ) :
    (∫ u : ℝ, weightV2 s u * deriv F u) =
      -s * ∫ u : ℝ, weightV2 s u * F u := by
  let G : ℝ → ℂ := fun u => weightV2 s u * F u
  have hG : ContDiff ℝ 1 G := by
    dsimp [G]
    exact (weight_contDiff_v2 s).of_le (by simp) |>.mul (hF.of_le (by simp))
  have hGc : HasCompactSupport G := by
    dsimp [G]
    exact hFc.mul_left
  have hder :
      deriv G = fun u => s * weightV2 s u * F u + weightV2 s u * deriv F u := by
    funext u
    have hlin : HasDerivAt (fun x : ℝ => x • s) s u := by
      simpa using (hasDerivAt_id' u).smul_const s
    have hw : HasDerivAt (weightV2 s) (s * weightV2 s u) u := by
      unfold weightV2
      convert hlin.cexp using 1 <;> ring
    have hFu := (hF.differentiable (by simp) u).hasDerivAt
    have hp := hw.mul hFu
    dsimp [G]
    rw [hp.deriv]
    ring
  have hz : ∫ u : ℝ, deriv G u = 0 :=
    integral_deriv_eq_zero_complex_v2 hG hGc
  rw [hder] at hz
  have hWF : Integrable (fun u : ℝ => weightV2 s u * F u) :=
    ((weight_contDiff_v2 s).mul hF).continuous.integrable_of_hasCompactSupport hFc.mul_left
  have hA : Integrable (fun u : ℝ => s * weightV2 s u * F u) := by
    simpa [mul_assoc] using hWF.const_mul s
  have hFd : ContDiff ℝ ∞ (deriv F) := contDiff_deriv_complex_v2 hF
  have hB : Integrable (fun u : ℝ => weightV2 s u * deriv F u) :=
    ((weight_contDiff_v2 s).mul hFd).continuous.integrable_of_hasCompactSupport hFc.deriv.mul_left
  rw [integral_add hA hB, integral_const_mul] at hz
  linear_combination hz

/-- The second weighted derivative contributes `s^2`. -/
theorem weighted_integral_second_deriv_v2
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hFc : HasCompactSupport F) (s : ℂ) :
    (∫ u : ℝ, weightV2 s u * deriv (deriv F) u) =
      s ^ 2 * ∫ u : ℝ, weightV2 s u * F u := by
  have hFd : ContDiff ℝ ∞ (deriv F) := contDiff_deriv_complex_v2 hF
  calc
    (∫ u : ℝ, weightV2 s u * deriv (deriv F) u)
        = -s * ∫ u : ℝ, weightV2 s u * deriv F u :=
          weighted_integral_deriv_v2 (deriv F) hFd hFc.deriv s
    _ = -s * (-s * ∫ u : ℝ, weightV2 s u * F u) := by
          rw [weighted_integral_deriv_v2 F hF hFc s]
    _ = s ^ 2 * ∫ u : ℝ, weightV2 s u * F u := by ring

/-- General transform of the targeted D(D+1) modulation. -/
theorem targetPhi_weighted_general_v2 (alpha s : ℂ) :
    (∫ u : ℝ, weightV2 s u * TargetPhiV11 alpha u) =
      s * (s - 1) *
        (∫ u : ℝ, weightV2 s u * TargetPsiV11 alpha u) := by
  have hF := targetPsi_contDiff_v11 alpha
  have hFc := targetPsi_hasCompactSupport_v11 alpha
  have hFd : ContDiff ℝ ∞ (deriv (TargetPsiV11 alpha)) :=
    contDiff_deriv_complex_v2 hF
  have h1 : Integrable
      (fun u : ℝ => weightV2 s u * deriv (TargetPsiV11 alpha) u) :=
    ((weight_contDiff_v2 s).mul hFd).continuous.integrable_of_hasCompactSupport
      hFc.deriv.mul_left
  have hFdd : ContDiff ℝ ∞ (deriv (deriv (TargetPsiV11 alpha))) :=
    contDiff_deriv_complex_v2 hFd
  have h2 : Integrable
      (fun u : ℝ => weightV2 s u * deriv (deriv (TargetPsiV11 alpha)) u) :=
    ((weight_contDiff_v2 s).mul hFdd).continuous.integrable_of_hasCompactSupport
      hFc.deriv.deriv.mul_left
  unfold TargetPhiV11
  simp_rw [mul_add]
  rw [integral_add h1 h2,
    weighted_integral_deriv_v2 (TargetPsiV11 alpha) hF hFc s,
    weighted_integral_second_deriv_v2 (TargetPsiV11 alpha) hF hFc s]
  ring

/-- The weighted targeted seed is exactly the shifted fixed seed transform. -/
theorem weighted_targetPsi_eq_seed_v2 (alpha s : ℂ) :
    (∫ u : ℝ, weightV2 s u * TargetPsiV11 alpha u) =
      seedMellinV2 (s - alpha) := by
  unfold seedMellinV2
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun u => by
    unfold weightV2 TargetPsiV11
    have hexp :
        Complex.exp (u • s) * Complex.exp (-(u • alpha)) =
          Complex.exp (u • (s - alpha)) := by
      rw [← Complex.exp_add]
      congr 1
      simp only [smul_eq_mul]
      ring
    rw [show Complex.exp (u • s) * ((psi0 u : ℂ) * Complex.exp (-(u • alpha))) =
        (psi0 u : ℂ) * (Complex.exp (u • s) * Complex.exp (-(u • alpha))) by ring,
      hexp]
    ring)

/-- General Mellin identity for every target parameter and every Mellin argument. -/
theorem targetPacket_mellin_general_v2 (alpha s : ℂ) :
    mellin (TargetPacketV11 alpha).1 s =
      s * (s - 1) * seedMellinV2 (s - alpha) := by
  rw [targetPacket_mellin_log_v11]
  have h := targetPhi_weighted_general_v2 alpha s
  rw [weighted_targetPsi_eq_seed_v2 alpha s] at h
  simpa [weightV2, smul_eq_mul, mul_comm] using h

end AEGIS.RHTargetPacketMellinGeneralV2

#print axioms AEGIS.RHTargetPacketMellinGeneralV2.weighted_integral_deriv_v2
#print axioms AEGIS.RHTargetPacketMellinGeneralV2.weighted_integral_second_deriv_v2
#print axioms AEGIS.RHTargetPacketMellinGeneralV2.targetPhi_weighted_general_v2
#print axioms AEGIS.RHTargetPacketMellinGeneralV2.weighted_targetPsi_eq_seed_v2
#print axioms AEGIS.RHTargetPacketMellinGeneralV2.targetPacket_mellin_general_v2
