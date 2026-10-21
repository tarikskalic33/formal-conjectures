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
/- Uniform exact scalar interface for the kappa=40 fixed-window consumer.
This does not supply a pointwise Krein certificate or prove a trace bound. -/
import CvSFrequencyIntervalV1
namespace AEGIS.CvSKreinScalarUniformV1
private theorem pi_ge_three : (3 : ℝ) ≤ Real.pi := by
  exact le_trans (by norm_num [AEGIS.CvSFrequencyIntervalV1.piLo])
    AEGIS.CvSFrequencyIntervalV1.pi_bounds.1

/-- A sufficient parameter range, with no nonnegativity assumption on T. -/
theorem gap_lower {m T : ℝ} (hm : 31/16 ≤ m) (hT : T ≤ 6) :
    (15/16 : ℝ) ≤ m - T/(2*Real.pi) := by
  have hd : (0 : ℝ) < 2*Real.pi := by positivity
  have hh : T/(2*Real.pi) ≤ 1 := by
    apply (div_le_iff₀ hd).2
    linarith [pi_ge_three]
  linarith

/-- The exact lower Schur reserve is conservatively rounded to one half. -/
theorem schur_budget_with_reserve {m T : ℝ} (hm : 31/16 ≤ m) (hT : T ≤ 6) :
    (40 : ℝ) + 1/2 ≤ (2*Real.pi)^2*(6/5 : ℝ)*(m-T/(2*Real.pi)) := by
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) pi_ge_three 2
  have hc : (216/5 : ℝ) ≤ (2*Real.pi)^2*(6/5 : ℝ) := by nlinarith
  have h1 := mul_le_mul_of_nonneg_right hc (by norm_num : (0 : ℝ) ≤ 15/16)
  have h2 := mul_le_mul_of_nonneg_left (gap_lower hm hT)
    (by positivity : (0 : ℝ) ≤ (2*Real.pi)^2*(6/5 : ℝ))
  linarith

theorem schur_budget {m T : ℝ} (hm : 31/16 ≤ m) (hT : T ≤ 6) :
    (40 : ℝ) ≤ (2*Real.pi)^2*(6/5 : ℝ)*(m-T/(2*Real.pi)) := by
  have h := schur_budget_with_reserve hm hT
  linarith

theorem chosen_budget : (40 : ℝ) ≤
    (2*Real.pi)^2*(6/5 : ℝ)*((31/16 : ℝ)-6/(2*Real.pi)) :=
  schur_budget le_rfl le_rfl
end AEGIS.CvSKreinScalarUniformV1
#check @AEGIS.CvSKreinScalarUniformV1.gap_lower
#print axioms AEGIS.CvSKreinScalarUniformV1.gap_lower
#check @AEGIS.CvSKreinScalarUniformV1.schur_budget_with_reserve
#print axioms AEGIS.CvSKreinScalarUniformV1.schur_budget_with_reserve
#print axioms AEGIS.CvSKreinScalarUniformV1.schur_budget
#print axioms AEGIS.CvSKreinScalarUniformV1.chosen_budget
