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

/-
AEGIS Ω — bounded zero spectrum -> decay of the genuine zero-translation kernel.

Standalone, parameterized integration point for a 7/8 zero-free theorem.
It imports *existing AEGIS proofs* rather than copying external mathematics.

The external nonvanishing theorem is an explicit argument, NOT an axiom.
No RH assertion is made. Kernel replay has NOT been performed for this file.
AUTHORITY_EFFECT = NONE. RH_PROVEN_UNCONDITIONALLY = false.
-/

import RHGlobalGrowthBoundaryV1
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

open Filter Topology Complex

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHSevenEighthsKernelBridgeV1

open AEGIS.WeilZeroTwoPointV11 AEGIS.RHZeroKernelLaplaceV12

/-- Comparator statement, kept as a proposition so no external theorem is
silently imported or promoted. -/
def SevenEighthsZetaNonvanishing : Prop :=
  ∀ s : ℂ, (7 / 8 : ℝ) < s.re → riemannZeta s ≠ 0

/-- Excludes zeros to the right of the stated comparator boundary. -/
theorem zero_real_part_le_seven_eighths
    (hQ : SevenEighthsZetaNonvanishing)
    (rho : RiemannNontrivialZeroIndexV2) :
    rho.1.re ≤ (7 / 8 : ℝ) := by
  exact le_of_not_gt (fun h => (hQ rho.1 h) rho.2.1)

/-- Rescale AEGIS's *actual* zero-translation kernel, preserving each zero
coefficient and using the same absolutely summable zero index. -/
private theorem scaled_kernel_eq_tsum
    (g : WeilCompactSmoothGV1) (rate t : ℝ) :
    Complex.exp (-((rate : ℂ) * (t : ℂ))) *
        WeilZeroTranslationKernelV11 g t =
      ∑' rho : RiemannNontrivialZeroIndexV2,
        WeilZeroCoefficientV11 g rho *
          Complex.exp ((rho.1 - (1 / 2 : ℂ) - (rate : ℂ)) * (t : ℂ)) := by
  have hs := zero_translation_kernel_summable_v11 g t
  unfold WeilZeroTranslationKernelV11
  rw [← hs.tsum_mul_left]
  apply tsum_congr
  intro rho
  unfold WeilZeroTranslationFactorV11
  calc
    Complex.exp (-((rate : ℂ) * (t : ℂ))) *
        (WeilZeroCoefficientV11 g rho *
          Complex.exp ((rho.1 - (1 / 2 : ℂ)) * (t : ℂ))) =
      WeilZeroCoefficientV11 g rho *
        (Complex.exp (-((rate : ℂ) * (t : ℂ))) *
          Complex.exp ((rho.1 - (1 / 2 : ℂ)) * (t : ℂ))) := by ring
    _ = _ := by
      rw [← Complex.exp_add]
      congr 2
      ring

/-- Algebraic real-part calculation, with real-valued time. -/
private theorem shifted_exponent_re
    (rho : RiemannNontrivialZeroIndexV2) (rate t : ℝ) :
    ((rho.1 - (1 / 2 : ℂ) - (rate : ℂ)) * (t : ℂ)).re =
      -((rate + (1 / 2 : ℝ) - rho.1.re) * t) := by
  simp only [Complex.mul_re, Complex.sub_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  norm_num <;> ring

/-- General AEGIS spectral-cap transport: if every nontrivial zero has
real part at most `cap`, the zero-translation kernel is little-o of
`exp(rate * t)` for every `rate > cap - 1/2`.

This theorem does NOT assert a cap; one must supply `hcap`. -/
theorem scaled_kernel_decay_of_zero_cap
    (g : WeilCompactSmoothGV1) (cap rate : ℝ)
    (hcap : ∀ rho : RiemannNontrivialZeroIndexV2, rho.1.re ≤ cap)
    (hrate : cap - (1 / 2 : ℝ) < rate) :
    Tendsto
      (fun t : ℝ =>
        Complex.exp (-((rate : ℂ) * (t : ℂ))) *
          WeilZeroTranslationKernelV11 g t)
      atTop (𝓝 (0 : ℂ)) := by
  have hpositive (rho : RiemannNontrivialZeroIndexV2) :
      0 < rate + (1 / 2 : ℝ) - rho.1.re := by
    have h := hcap rho
    linarith
  have hterm : ∀ rho : RiemannNontrivialZeroIndexV2,
      Tendsto
        (fun t : ℝ =>
          WeilZeroCoefficientV11 g rho *
            Complex.exp ((rho.1 - (1 / 2 : ℂ) - (rate : ℂ)) * (t : ℂ)))
        atTop (𝓝 (0 : ℂ)) := by
    intro rho
    have hexp : Tendsto
        (fun t : ℝ =>
          Complex.exp ((rho.1 - (1 / 2 : ℂ) - (rate : ℂ)) * (t : ℂ)))
        atTop (𝓝 (0 : ℂ)) := by
      apply Complex.tendsto_exp_nhds_zero_iff.mpr
      have hlin0 := tendsto_neg_atTop_atBot.comp
        ((tendsto_id : Tendsto (fun t : ℝ => t) atTop atTop).const_mul_atTop
          (hpositive rho))
      have hlin :
          Tendsto (fun t : ℝ =>
            -((rate + (1 / 2 : ℝ) - rho.1.re) * t)) atTop atBot := by
        simpa [Function.comp_def] using hlin0
      convert hlin using 1
      funext t
      exact shifted_exponent_re rho rate t
    simpa only [mul_zero] using hexp.const_mul (WeilZeroCoefficientV11 g rho)
  have hbound : ∀ᶠ t : ℝ in atTop,
      ∀ rho : RiemannNontrivialZeroIndexV2,
        ‖WeilZeroCoefficientV11 g rho *
          Complex.exp ((rho.1 - (1 / 2 : ℂ) - (rate : ℂ)) * (t : ℂ))‖ ≤
        ‖WeilZeroCoefficientV11 g rho‖ := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht rho
    have hre :
        ((rho.1 - (1 / 2 : ℂ) - (rate : ℂ)) * (t : ℂ)).re ≤ 0 := by
      rw [shifted_exponent_re]
      exact mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (hpositive rho).le) ht
    rw [norm_mul, Complex.norm_exp]
    exact mul_le_of_le_one_right (norm_nonneg _)
      (Real.exp_le_one_iff.mpr hre)
  have hlim := tendsto_tsum_of_dominated_convergence
    (zero_coefficient_norm_summable_v12 g) hterm hbound
  simpa only [tsum_zero, ← scaled_kernel_eq_tsum] using hlim

/-- OpenAI's 7/8 comparator (if imported with a verified proof) improves the
AEGIS endpoint growth bound from the old 1/2 threshold to any exponent
strictly greater than 3/8. The assumption `hQ` is *visible and mandatory*. -/
theorem scaled_kernel_decay_of_seven_eighths
    (hQ : SevenEighthsZetaNonvanishing)
    (g : WeilCompactSmoothGV1) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    Tendsto
      (fun t : ℝ =>
        Complex.exp (-((((3 / 8 : ℝ) + epsilon) : ℂ) * (t : ℂ))) *
          WeilZeroTranslationKernelV11 g t)
      atTop (𝓝 (0 : ℂ)) := by
  have hrate :
      (7 / 8 : ℝ) - (1 / 2 : ℝ) < (3 / 8 : ℝ) + epsilon := by
    linarith
  exact scaled_kernel_decay_of_zero_cap g (7 / 8) ((3 / 8 : ℝ) + epsilon)
    (zero_real_part_le_seven_eighths hQ) hrate

end AEGIS.RHSevenEighthsKernelBridgeV1

#print axioms AEGIS.RHSevenEighthsKernelBridgeV1.zero_real_part_le_seven_eighths
#print axioms AEGIS.RHSevenEighthsKernelBridgeV1.scaled_kernel_decay_of_zero_cap
#print axioms AEGIS.RHSevenEighthsKernelBridgeV1.scaled_kernel_decay_of_seven_eighths
