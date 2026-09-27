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

import RHRestrictedWeilBridgeV13
import WeilZeroTwoPointV11
import Mathlib.Tactic

/-!
# Reflection defect of a nontrivial zeta zero

For a nontrivial zero `rho`, define the functional-equation reflection defect

  rho - (1 - conj rho).

Its imaginary part vanishes identically and its real part is exactly
`2 * Re rho - 1`.  Hence the Riemann critical-line condition is literally
the vanishing of one real square.

The same defect is already encoded in the repository's centered translation
factor:

  exp ((rho - 1/2) d).

Its norm is

  exp (((Re defect) / 2) d).

Thus a zero is on the critical line iff its spectral translation factor has
unit norm for every real translation (equivalently, already at d = 1).

This file is algebraic packaging of the existing restricted-Weil machinery.
It does not prove the final-sign residual and therefore does not prove RH.
-/

open Complex
open scoped ComplexConjugate

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHReflectionDefectV1

open AEGIS.WeilZeroTwoPointV11
open AEGIS.RHZeroKernelLaplaceV12
open AEGIS.RHRestrictedWeilBridgeV13
open AEGIS.RHFinalClosureV1

/-- Functional-equation reflection defect of a canonical nontrivial zero. -/
def ZeroReflectionDefectV1 (rho : RiemannNontrivialZeroIndexV2) : ℂ :=
  rho.1 - (1 - conj rho.1)

/-- The defect is purely real. -/
theorem zero_reflection_defect_im_v1 (rho : RiemannNontrivialZeroIndexV2) :
    (ZeroReflectionDefectV1 rho).im = 0 := by
  simp [ZeroReflectionDefectV1]

/-- Its real coordinate is exactly twice the displacement from the critical line. -/
theorem zero_reflection_defect_re_v1 (rho : RiemannNontrivialZeroIndexV2) :
    (ZeroReflectionDefectV1 rho).re = 2 * rho.1.re - 1 := by
  simp [ZeroReflectionDefectV1]
  ring

/-- Same identity in the centered-zero coordinate already used by the V12
Laplace/resolvent criterion. -/
theorem zero_reflection_defect_re_centered_v1
    (rho : RiemannNontrivialZeroIndexV2) :
    (ZeroReflectionDefectV1 rho).re =
      2 * (WeilCenteredZeroExponentV12 rho).re := by
  rw [zero_reflection_defect_re_v1, centered_re_v13]
  ring

/-- The squared reflection defect is exactly four times the squared
critical-line displacement. -/
theorem zero_reflection_defect_normSq_v1
    (rho : RiemannNontrivialZeroIndexV2) :
    Complex.normSq (ZeroReflectionDefectV1 rho) =
      4 * (rho.1.re - 1 / 2) ^ 2 := by
  rw [Complex.normSq_apply, zero_reflection_defect_re_v1,
    zero_reflection_defect_im_v1]
  ring

/-- The critical line is exactly the fixed-point set of the zeta reflection. -/
theorem zero_reflection_defect_eq_zero_iff_v1
    (rho : RiemannNontrivialZeroIndexV2) :
    ZeroReflectionDefectV1 rho = 0 ↔ rho.1.re = 1 / 2 := by
  constructor
  · intro h
    have hre := congrArg Complex.re h
    rw [zero_reflection_defect_re_v1] at hre
    simp only [zero_re] at hre
    linarith
  · intro h
    apply Complex.ext
    · rw [zero_reflection_defect_re_v1]
      linarith
    · rw [zero_reflection_defect_im_v1]
      simp

/-- Equivalent nonnegative-square form. -/
theorem zero_reflection_defect_normSq_eq_zero_iff_v1
    (rho : RiemannNontrivialZeroIndexV2) :
    Complex.normSq (ZeroReflectionDefectV1 rho) = 0 ↔
      rho.1.re = 1 / 2 := by
  rw [Complex.normSq_eq_zero, zero_reflection_defect_eq_zero_iff_v1]

/-- The repository translation factor exposes the reflection defect directly
in its norm. -/
theorem zero_translation_factor_norm_eq_defect_exp_v1
    (rho : RiemannNontrivialZeroIndexV2) (d : ℝ) :
    ‖WeilZeroTranslationFactorV11 rho d‖ =
      Real.exp (((ZeroReflectionDefectV1 rho).re / 2) * d) := by
  unfold WeilZeroTranslationFactorV11
  rw [Complex.norm_exp]
  congr 1
  simp [ZeroReflectionDefectV1, Complex.mul_re, Complex.sub_re]
  ring

/-- A single nonzero translation already detects whether the centered
spectral exponent has nonzero real part.  We use d = 1. -/
theorem unit_translation_factor_norm_eq_one_iff_v1
    (rho : RiemannNontrivialZeroIndexV2) :
    ‖WeilZeroTranslationFactorV11 rho 1‖ = 1 ↔
      ZeroReflectionDefectV1 rho = 0 := by
  rw [zero_translation_factor_norm_eq_defect_exp_v1]
  constructor
  · intro h
    rw [mul_one, Real.exp_eq_one_iff] at h
    apply Complex.ext
    · simpa using (show (ZeroReflectionDefectV1 rho).re = 0 by linarith)
    · rw [zero_reflection_defect_im_v1]
      simp
  · intro h
    have hre := congrArg Complex.re h
    simp only [zero_re] at hre
    rw [mul_one, Real.exp_eq_one_iff]
    linarith

/-- Critical-line membership is equivalent to unit modulus of every
translation factor. -/
theorem zero_re_half_iff_all_translation_factors_unit_v1
    (rho : RiemannNontrivialZeroIndexV2) :
    rho.1.re = 1 / 2 ↔
      ∀ d : ℝ, ‖WeilZeroTranslationFactorV11 rho d‖ = 1 := by
  constructor
  · intro hr d
    rw [zero_translation_factor_norm_eq_defect_exp_v1]
    have hz := (zero_reflection_defect_eq_zero_iff_v1 rho).2 hr
    have hre := congrArg Complex.re hz
    simp only [zero_re] at hre
    rw [hre]
    simp
  · intro h
    exact (zero_reflection_defect_eq_zero_iff_v1 rho).1
      ((unit_translation_factor_norm_eq_one_iff_v1 rho).1 (h 1))

/-- Existing final-sign machinery forces the elementary reflection defect to
vanish for every nontrivial zero.  This isolates the genuinely difficult
input from the trivial algebraic endpoint. -/
theorem final_sign_zero_reflection_defect_v1
    (h : FinalSignResidualV1) (rho : RiemannNontrivialZeroIndexV2) :
    ZeroReflectionDefectV1 rho = 0 := by
  have h1 : rho.1.re ≤ 1 / 2 :=
    zero_re_le_half_of_final_sign_v13 h rho
  obtain ⟨sigma, hsigma⟩ := exists_reflected_zero_v13 rho
  have h2 := zero_re_le_half_of_final_sign_v13 h sigma
  rw [hsigma] at h2
  simp only [sub_re, one_re] at h2
  have hr : rho.1.re = 1 / 2 := by linarith
  exact (zero_reflection_defect_eq_zero_iff_v1 rho).2 hr

/-- Therefore final sign makes every individual zero translation factor
unit-modulus, pointwise in the translation parameter. -/
theorem final_sign_all_translation_factors_unit_v1
    (h : FinalSignResidualV1) (rho : RiemannNontrivialZeroIndexV2) :
    ∀ d : ℝ, ‖WeilZeroTranslationFactorV11 rho d‖ = 1 := by
  exact (zero_re_half_iff_all_translation_factors_unit_v1 rho).1
    ((zero_reflection_defect_eq_zero_iff_v1 rho).1
      (final_sign_zero_reflection_defect_v1 h rho))

end AEGIS.RHReflectionDefectV1

#print axioms AEGIS.RHReflectionDefectV1.zero_reflection_defect_normSq_v1
#print axioms AEGIS.RHReflectionDefectV1.zero_reflection_defect_eq_zero_iff_v1
#print axioms AEGIS.RHReflectionDefectV1.zero_translation_factor_norm_eq_defect_exp_v1
#print axioms AEGIS.RHReflectionDefectV1.zero_re_half_iff_all_translation_factors_unit_v1
#print axioms AEGIS.RHReflectionDefectV1.final_sign_zero_reflection_defect_v1
#print axioms AEGIS.RHReflectionDefectV1.final_sign_all_translation_factors_unit_v1
