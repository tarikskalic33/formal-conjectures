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

import RHCellBinomialV1

/-!
# One cell: `∫_a^b x^z e^{−αx} dx` by moments

`I_k = ∫_a^b e^{−αx} (x − a)^k dx` satisfies

  `α I_0 = e^{−αa} − e^{−αb}`,   `α I_{k+1} = (k + 1) I_k − e^{−αb} (b − a)^{k+1}`,

and for `1 ≤ a ≤ b`, `re z ≤ 0`, `(b − a)/a ≤ U`,

  `‖∫_a^b x^z e^{−αx} dx − a^z Σ_{k≤d} choose(z, k) a^{−k} I_k‖ ≤ R · I_0`,

with `R` the binomial remainder of `RHCellBinomialV1`.  AUTHORITY_EFFECT = NONE.
-/

open Complex Set MeasureTheory Real

namespace AEGIS.RHCellMomentsV1

open AEGIS.RHCellBinomialV1

/-- `I_k = ∫_a^b e^{−αx} (x − a)^k dx`. -/
noncomputable def mom (α a b : ℝ) (k : ℕ) : ℝ := ∫ x in a..b, rexp (-α * x) * (x - a) ^ k

theorem mom_zero (α a b : ℝ) : α * mom α a b 0 = rexp (-α * a) - rexp (-α * b) := by
  have hd : ∀ x ∈ uIcc a b, HasDerivAt (fun x => rexp (-α * x)) (-α * rexp (-α * x)) x := by
    intro x _
    refine (((hasDerivAt_id' x).const_mul (-α)).exp).congr_deriv ?_
    ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((continuous_const.mul (by fun_prop)).intervalIntegrable _ _)
  rw [intervalIntegral.integral_const_mul] at h
  simp only [mom, pow_zero, mul_one]
  linear_combination -h

theorem mom_succ (α a b : ℝ) (k : ℕ) :
    α * mom α a b (k + 1) = (k + 1) * mom α a b k - rexp (-α * b) * (b - a) ^ (k + 1) := by
  have hd : ∀ x ∈ uIcc a b, HasDerivAt (fun x => rexp (-α * x) * (x - a) ^ (k + 1))
      (-α * (rexp (-α * x) * (x - a) ^ (k + 1)) + (k + 1) * (rexp (-α * x) * (x - a) ^ k)) x := by
    intro x _
    have h1 : HasDerivAt (fun x => rexp (-α * x)) (rexp (-α * x) * (-α * 1)) x :=
      ((hasDerivAt_id' x).const_mul (-α)).exp
    have h2 : HasDerivAt (fun x => (x - a) ^ (k + 1)) (((k + 1 : ℕ) : ℝ) * (x - a) ^ k) x := by
      simpa using ((hasDerivAt_id' x).sub_const a).fun_pow (k + 1)
    refine (h1.mul h2).congr_deriv ?_
    push_cast; ring
  have hc1 : Continuous fun x => rexp (-α * x) * (x - a) ^ (k + 1) := by fun_prop
  have hc0 : Continuous fun x => rexp (-α * x) * (x - a) ^ k := by fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (((hc1.const_mul _).add (hc0.const_mul _)).intervalIntegrable _ _)
  rw [intervalIntegral.integral_add ((hc1.const_mul _).intervalIntegrable _ _)
    ((hc0.const_mul _).intervalIntegrable _ _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at h
  have h0 : (a - a) ^ (k + 1) = 0 := by simp
  rw [h0, mul_zero, sub_zero] at h
  simp only [mom]
  linear_combination -h

lemma continuousOn_cpow (z : ℂ) : ContinuousOn (fun x : ℝ => (x : ℂ) ^ z) (Ioi 0) := by
  intro x hx
  exact ((continuousAt_cpow_const (ofReal_mem_slitPlane.mpr hx)).comp
    continuous_ofReal.continuousAt).continuousWithinAt

/-- **One cell.** -/
theorem cell_approx {α a b M U : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) {z : ℂ} (hz : z.re ≤ 0) (d : ℕ)
    (hzM : ‖z‖ ≤ M) (hM : 1 ≤ M) (hU : (b - a) / a ≤ U) (hq : U * (M + d + 1) / (d + 2) < 1) :
    ‖(∫ x in a..b, (x : ℂ) ^ z * (rexp (-α * x) : ℂ)) -
        (a : ℂ) ^ z * ∑ k ∈ Finset.range (d + 1),
          Ring.choose z k * ((a⁻¹ ^ k : ℝ) : ℂ) * (mom α a b k : ℂ)‖ ≤
      beta M (d + 1) * U ^ (d + 1) / (1 - U * (M + d + 1) / (d + 2)) * mom α a b 0 := by
  set R := beta M (d + 1) * U ^ (d + 1) / (1 - U * (M + d + 1) / (d + 2)) with hR
  have ha0 : 0 < a := by linarith
  set g : ℝ → ℂ := fun x => (a : ℂ) ^ z * ∑ k ∈ Finset.range (d + 1),
      Ring.choose z k * ((a⁻¹ ^ k : ℝ) : ℂ) * ((rexp (-α * x) * (x - a) ^ k : ℝ) : ℂ) with hg
  have hgc : Continuous g := by
    refine continuous_const.mul (continuous_finsetSum _ fun k _ => ?_)
    exact continuous_const.mul (continuous_ofReal.comp (by fun_prop))
  have hgi : ∫ x in a..b, g x = (a : ℂ) ^ z * ∑ k ∈ Finset.range (d + 1),
      Ring.choose z k * ((a⁻¹ ^ k : ℝ) : ℂ) * (mom α a b k : ℂ) := by
    rw [hg, intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum]
    · congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal, mom]
    · intro k _
      exact (continuous_const.mul (continuous_ofReal.comp (by fun_prop))).intervalIntegrable _ _
  have hfi : IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ z * (rexp (-α * x) : ℂ)) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ((continuousOn_cpow z).mono ?_).mul (continuous_ofReal.comp (by fun_prop)).continuousOn
    intro x hx
    rw [uIcc_of_le hab] at hx
    exact lt_of_lt_of_le ha0 hx.1
  have hm0 : R * mom α a b 0 = ∫ x in a..b, R * (rexp (-α * x) * (x - a) ^ 0) := by
    rw [intervalIntegral.integral_const_mul, mom]
  rw [← hgi, ← intervalIntegral.integral_sub hfi (hgc.intervalIntegrable _ _), hm0]
  refine intervalIntegral.norm_integral_le_of_norm_le hab
    (Filter.Eventually.of_forall fun x hx => ?_)
    ((continuous_const.mul (by fun_prop)).intervalIntegrable _ _)
  have hx0 : a ≤ x := hx.1.le
  set u := (x - a) / a with hu
  have hu0 : 0 ≤ u := div_nonneg (by linarith) ha0.le
  have huU : u ≤ U := le_trans (div_le_div_of_nonneg_right (by linarith [hx.2]) ha0.le) hU
  have hrem := binom_rem_le z d hzM hM hu0 huU hq
  have hs : ∑ k ∈ Finset.range (d + 1),
      Ring.choose z k * ((a⁻¹ ^ k : ℝ) : ℂ) * ((rexp (-α * x) * (x - a) ^ k : ℝ) : ℂ) =
      (∑ k ∈ Finset.range (d + 1), Ring.choose z k * (u : ℂ) ^ k) * (rexp (-α * x) : ℂ) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hu]; push_cast
    rw [div_pow, inv_pow]; ring
  have hpt : (x : ℂ) ^ z * (rexp (-α * x) : ℂ) - g x =
      (a : ℂ) ^ z * ((1 + (u : ℂ)) ^ z - ∑ k ∈ Finset.range (d + 1), Ring.choose z k * (u : ℂ) ^ k) *
        (rexp (-α * x) : ℂ) := by
    rw [hg]; dsimp only
    rw [hs, cpow_cell ha0 hx0 z, ← hu]; ring
  have haz : ‖(a : ℂ) ^ z‖ ≤ 1 := by
    rw [norm_cpow_eq_rpow_re_of_pos ha0]
    exact Real.rpow_le_one_of_one_le_of_nonpos ha hz
  rw [hpt, norm_mul, norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), pow_zero,
    mul_one]
  have hR0 : 0 ≤ ‖(1 + (u : ℂ)) ^ z - ∑ k ∈ Finset.range (d + 1), Ring.choose z k * (u : ℂ) ^ k‖ :=
    norm_nonneg _
  calc ‖(a : ℂ) ^ z‖ * ‖(1 + (u : ℂ)) ^ z - ∑ k ∈ Finset.range (d + 1), Ring.choose z k * (u : ℂ) ^ k‖
        * rexp (-α * x)
      ≤ 1 * R * rexp (-α * x) := by gcongr
    _ = R * rexp (-α * x) := by ring

end AEGIS.RHCellMomentsV1

#print axioms AEGIS.RHCellMomentsV1.mom_succ
#print axioms AEGIS.RHCellMomentsV1.cell_approx
