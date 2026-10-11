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

import RHCellMomentsV1

/-!
# `∫_{x>1} x^z e^{−αx} dx` as geometric cells plus a tail

For `α > 0`, `re z ≤ 0`, `a_j = (9/8)^j`:

  `∫_{x>1} f = Σ_{j<J} ∫_{a_j}^{a_{j+1}} f + ∫_{x>a_J} f`,   `‖∫_{x>X} f‖ ≤ e^{−αX}/α` (`X ≥ 1`).

AUTHORITY_EFFECT = NONE.
-/

open Complex Set MeasureTheory

namespace AEGIS.RHCellSplitV1

/-- `x^z e^{−αx}`. -/
noncomputable def f (z : ℂ) (α x : ℝ) : ℂ := (x : ℂ) ^ z * ((Real.exp (-α * x) : ℝ) : ℂ)

variable {z : ℂ}

lemma norm_f_le {α x : ℝ} (hx : 1 ≤ x) (hz : z.re ≤ 0) : ‖f z α x‖ ≤ Real.exp (-α * x) := by
  rw [f, norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have h : ‖(x : ℂ) ^ z‖ ≤ 1 := by
    rw [norm_cpow_eq_rpow_re_of_pos (by linarith)]
    exact Real.rpow_le_one_of_one_le_of_nonpos hx hz
  calc ‖(x : ℂ) ^ z‖ * Real.exp (-α * x) ≤ 1 * Real.exp (-α * x) :=
        mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    _ = Real.exp (-α * x) := one_mul _

lemma continuousOn_f (z : ℂ) (α : ℝ) : ContinuousOn (f z α) (Ioi 0) :=
  (AEGIS.RHCellMomentsV1.continuousOn_cpow z).mul
    (continuous_ofReal.comp (by fun_prop)).continuousOn

lemma integrableOn_f {α c : ℝ} (hα : 0 < α) (hc : 1 ≤ c) (hz : z.re ≤ 0) :
    IntegrableOn (f z α) (Ioi c) := by
  have ha : -α < 0 := by linarith
  refine Integrable.mono' (integrableOn_exp_mul_Ioi ha c) ?_ ?_
  · exact ((continuousOn_f z α).mono (Ioi_subset_Ioi (by linarith))).aestronglyMeasurable
      measurableSet_Ioi
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun x hx => ?_)
    exact norm_f_le (by linarith [show c < x from hx]) hz

lemma intervalIntegrable_f {α u v : ℝ} (hu : 1 ≤ u) (hv : 1 ≤ v) :
    IntervalIntegrable (f z α) volume u v := by
  refine ContinuousOn.intervalIntegrable ((continuousOn_f z α).mono fun x hx => ?_)
  rcases Set.mem_uIcc.mp hx with h | h
  · exact lt_of_lt_of_le one_pos (hu.trans h.1)
  · exact lt_of_lt_of_le one_pos (hv.trans h.1)

/-- **Tail.** -/
theorem tail_le {α X : ℝ} (hα : 0 < α) (hX : 1 ≤ X) (hz : z.re ≤ 0) :
    ‖∫ x in Ioi X, f z α x‖ ≤ Real.exp (-α * X) / α := by
  have ha : -α < 0 := by linarith
  calc ‖∫ x in Ioi X, f z α x‖ ≤ ∫ x in Ioi X, Real.exp (-α * x) :=
        norm_integral_le_of_norm_le (integrableOn_exp_mul_Ioi ha X)
          ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun x hx =>
            norm_f_le (by linarith [show X < x from hx]) hz))
    _ = Real.exp (-α * X) / α := by
        rw [integral_exp_mul_Ioi ha X]
        field_simp

/-- The cell endpoints `a_j = (9/8)^j`. -/
noncomputable def aj (j : ℕ) : ℝ := (((9 / 8 : ℚ) ^ j : ℚ) : ℝ)

lemma one_le_aj (j : ℕ) : 1 ≤ aj j := by
  simp only [aj]; push_cast; exact one_le_pow₀ (by norm_num)

/-- **Cells plus tail.** -/
theorem split_cells {α : ℝ} (hα : 0 < α) (hz : z.re ≤ 0) (J : ℕ) :
    ∫ x in Ioi (1 : ℝ), f z α x =
      ∑ j ∈ Finset.range J, (∫ x in aj j..aj (j + 1), f z α x) + ∫ x in Ioi (aj J), f z α x := by
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (f := f z α) (μ := volume)
    (a := aj) (n := J) (fun k _ => intervalIntegrable_f (one_le_aj k) (one_le_aj (k + 1)))
  have h0 : aj 0 = 1 := by simp [aj]
  rw [hsum, h0]
  exact (intervalIntegral.integral_interval_add_Ioi (integrableOn_f hα le_rfl hz)
    (integrableOn_f hα (one_le_aj J) hz)).symm

end AEGIS.RHCellSplitV1

#print axioms AEGIS.RHCellSplitV1.split_cells
#print axioms AEGIS.RHCellSplitV1.tail_le
