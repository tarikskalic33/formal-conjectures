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

import RHRiemannThetaFormulaV1
import RHThetaTailV1

/-!
# `𝓜A(w)` by three exponentials

For `re w ≤ 1`,

  `‖𝓜A(w) − Σ_{n<3} 2 ∫_{x>1} x^{w−1} e^{−π (n+1)² x} dx‖ ≤ 4 e^{−16π} / (16π)`,

using `A = 1_{x>1}(θ − 1)`, the theta tail bound and `|x^{w−1}| ≤ 1` on `x ≥ 1`.
AUTHORITY_EFFECT = NONE.
-/

open Complex Set MeasureTheory HurwitzZeta Real

namespace AEGIS.RHMellinThreeTermsV1

open AEGIS.RHRiemannThetaFormulaV1 AEGIS.RHThetaTailV1

/-- `∫_{x>1} x^{w−1} e^{−π (n+1)² x} dx`. -/
noncomputable def G (n : ℕ) (w : ℂ) : ℂ :=
  ∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (w - 1) * ((rexp (-π * (n + 1) ^ 2 * x) : ℝ) : ℂ)

/-- The theta remainder after three terms. -/
noncomputable def E (x : ℝ) : ℝ :=
  evenKernel 0 x - 1 - ∑ n ∈ Finset.range 3, 2 * rexp (-π * (n + 1) ^ 2 * x)

lemma norm_cpow_le_one {x : ℝ} (hx : 1 ≤ x) {w : ℂ} (hw : w.re ≤ 1) : ‖(x : ℂ) ^ (w - 1)‖ ≤ 1 := by
  rw [norm_cpow_eq_rpow_re_of_pos (lt_of_lt_of_le one_pos hx)]
  exact Real.rpow_le_one_of_one_le_of_nonpos hx (by simp; linarith)

lemma continuousOn_cpow (w : ℂ) : ContinuousOn (fun x : ℝ => (x : ℂ) ^ (w - 1)) (Ioi 0) := by
  intro x hx
  exact ((continuousAt_cpow_const (ofReal_mem_slitPlane.mpr hx)).comp
    continuous_ofReal.continuousAt).continuousWithinAt

lemma integrableOn_term (n : ℕ) {w : ℂ} (hw : w.re ≤ 1) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (w - 1) * ((rexp (-π * (n + 1) ^ 2 * x) : ℝ) : ℂ))
      (Ioi 1) := by
  have ha : -π * ((n : ℝ) + 1) ^ 2 < 0 := by
    have := Real.pi_pos; have : (0 : ℝ) < ((n : ℝ) + 1) ^ 2 := by positivity
    nlinarith
  refine Integrable.mono' (integrableOn_exp_mul_Ioi ha 1) ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ((continuousOn_cpow w).mono (Ioi_subset_Ioi zero_le_one)).mul ?_
    exact (continuous_ofReal.comp (Real.continuous_exp.comp (by fun_prop))).continuousOn
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun x hx => ?_)
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have := norm_cpow_le_one (le_of_lt hx) hw
    calc ‖(x : ℂ) ^ (w - 1)‖ * rexp (-π * ((n : ℝ) + 1) ^ 2 * x)
        ≤ 1 * rexp (-π * ((n : ℝ) + 1) ^ 2 * x) :=
          mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
      _ = rexp (-π * ((n : ℝ) + 1) ^ 2 * x) := one_mul _

lemma mellin_A_eq (w : ℂ) :
    mellin A w = ∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (w - 1) * ((evenKernel 0 x - 1 : ℝ) : ℂ) := by
  have h1 : mellin A w = ∫ x in Ioi (0 : ℝ),
      (Ioi (1 : ℝ)).indicator (fun x : ℝ => (x : ℂ) ^ (w - 1) * ((evenKernel 0 x - 1 : ℝ) : ℂ)) x := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    by_cases hx : 1 < x
    · rw [indicator_of_mem (show x ∈ Ioi (1 : ℝ) from hx), smul_eq_mul, A_apply_of_one_lt hx]
    · rw [indicator_of_notMem (show x ∉ Ioi (1 : ℝ) from hx), smul_eq_mul]
      simp [A, indicator_of_notMem (show x ∉ Ioi (1 : ℝ) from hx)]
  rw [h1, setIntegral_indicator measurableSet_Ioi,
    inter_eq_right.mpr (Ioi_subset_Ioi zero_le_one)]

lemma integrableOn_main (w : ℂ) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (w - 1) * ((evenKernel 0 x - 1 : ℝ) : ℂ)) (Ioi 1) := by
  have h := (mellinConvergent_indicator (measurableSet_Ioi (a := (1 : ℝ))) w).mono_set
    (Ioi_subset_Ioi zero_le_one)
  refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
  simp only []
  rw [smul_eq_mul, show (Ioi (1 : ℝ)).indicator P.f_modif x = A x from rfl,
    A_apply_of_one_lt (show 1 < x from hx)]

/-- **Three-term approximation of `𝓜A`.** -/
theorem mellin_A_three_terms {w : ℂ} (hw : w.re ≤ 1) :
    ‖mellin A w - ∑ n ∈ Finset.range 3, 2 * G n w‖ ≤ 4 * rexp (-16 * π) / (16 * π) := by
  have hint : ∀ n ∈ Finset.range 3, IntegrableOn
      (fun x : ℝ => 2 * ((x : ℂ) ^ (w - 1) * ((rexp (-π * (n + 1) ^ 2 * x) : ℝ) : ℂ))) (Ioi 1) :=
    fun n _ => (integrableOn_term n hw).const_mul 2
  have hsum : ∑ n ∈ Finset.range 3, 2 * G n w = ∫ x in Ioi (1 : ℝ),
      ∑ n ∈ Finset.range 3, 2 * ((x : ℂ) ^ (w - 1) * ((rexp (-π * (n + 1) ^ 2 * x) : ℝ) : ℂ)) := by
    rw [integral_finsetSum _ hint]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [G, integral_const_mul]
  have hdiff : mellin A w - ∑ n ∈ Finset.range 3, 2 * G n w =
      ∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (w - 1) * ((E x : ℝ) : ℂ) := by
    rw [mellin_A_eq, hsum, ← integral_sub (integrableOn_main w) (integrable_finsetSum _ hint)]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    simp only [E, Finset.sum_range_succ, Finset.sum_range_zero]; push_cast; ring
  have ha : -16 * π < 0 := by have := Real.pi_pos; linarith
  have hbound : ‖∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (w - 1) * ((E x : ℝ) : ℂ)‖ ≤
      ∫ x in Ioi (1 : ℝ), 4 * rexp (-16 * π * x) := by
    refine norm_integral_le_of_norm_le ((integrableOn_exp_mul_Ioi ha 1).const_mul 4) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun x hx => ?_)
    have hx1 : 1 ≤ x := le_of_lt hx
    obtain ⟨h0, h1⟩ := theta_tail_bound hx1
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ E x from h0)]
    calc ‖(x : ℂ) ^ (w - 1)‖ * E x ≤ 1 * E x :=
          mul_le_mul_of_nonneg_right (norm_cpow_le_one hx1 hw) (show 0 ≤ E x from h0)
      _ ≤ 4 * rexp (-16 * π * x) := by rw [one_mul]; exact (show E x ≤ _ from h1)
  rw [hdiff]
  refine hbound.trans (le_of_eq ?_)
  rw [integral_const_mul, integral_exp_mul_Ioi ha 1]
  field_simp

end AEGIS.RHMellinThreeTermsV1

#print axioms AEGIS.RHMellinThreeTermsV1.mellin_A_three_terms
