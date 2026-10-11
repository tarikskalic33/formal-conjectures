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

import Mathlib

/-!
# `x^z` on a geometric cell, by the binomial series

For `a > 0` and `x ≥ a`, `x^z = a^z (1 + u)^z` with `u = (x − a)/a`, and for `0 ≤ u ≤ U < 1`

  `‖(1 + u)^z − Σ_{k≤d} choose(z, k) u^k‖ ≤ β_{d+1} U^{d+1} / (1 − q)`,
  `β_k = Π_{j<k} (M + j)/(j + 1)`,  `q = U (M + d + 1)/(d + 2) < 1`,  `‖z‖ ≤ M`,  `1 ≤ M`.

The coefficients satisfy `choose(z, k+1) = choose(z, k)(z − k)/(k + 1)`, and on cells `[r^j, r^{j+1}]`
the base power repeats: `(r^j)^z = (r^z)^j`.  AUTHORITY_EFFECT = NONE.
-/

open Complex

namespace AEGIS.RHCellBinomialV1

/-- `choose(z, k+1) = choose(z, k) (z − k)/(k + 1)`. -/
theorem choose_succ (z : ℂ) (k : ℕ) :
    Ring.choose z (k + 1) = Ring.choose z k * (z - k) / (k + 1) := by
  rw [Ring.choose_eq_smul, Ring.choose_eq_smul, descPochhammer_succ_right, Polynomial.smeval_mul,
    Polynomial.smeval_sub, Polynomial.smeval_X, Polynomial.smeval_natCast]
  simp only [Nat.factorial_succ, Nat.cast_mul, pow_one, pow_zero, nsmul_eq_mul, mul_one,
    smul_eq_mul, Nat.cast_add, Nat.cast_one]
  have h1 : ((k.factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have h2 : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  field_simp

/-- The binomial series at a real point `|u| < 1`. -/
theorem binom_hasSum (z : ℂ) {u : ℝ} (hu : |u| < 1) :
    HasSum (fun k => Ring.choose z k * (u : ℂ) ^ k) ((1 + (u : ℂ)) ^ z) := by
  have hmem : (u : ℂ) ∈ Metric.eball (0 : ℂ) 1 := by
    rw [mem_eball_zero_iff, ← ofReal_norm, ENNReal.ofReal_lt_one]
    simpa using hu
  have h := (one_add_cpow_hasFPowerSeriesOnBall_zero (a := z)).hasSum hmem
  simpa [binomialSeries, FormalMultilinearSeries.coeff_ofScalars, mul_comm] using h

/-- `β_k = Π_{j<k} (M + j)/(j + 1)`. -/
noncomputable def beta (M : ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => beta M k * (M + k) / (k + 1)

lemma beta_nonneg {M : ℝ} (hM : 0 ≤ M) : ∀ k, 0 ≤ beta M k
  | 0 => by simp [beta]
  | k + 1 => by
    simp only [beta]
    have := beta_nonneg hM k
    positivity

theorem norm_choose_le {z : ℂ} {M : ℝ} (hz : ‖z‖ ≤ M) : ∀ k, ‖Ring.choose z k‖ ≤ beta M k
  | 0 => by simp [beta]
  | k + 1 => by
    have hM : 0 ≤ M := (norm_nonneg z).trans hz
    rw [choose_succ, beta, norm_div, norm_mul]
    have h1 : ‖z - k‖ ≤ M + k := (norm_sub_le _ _).trans (by simp; linarith)
    have h2 : ‖((k : ℂ) + 1)‖ = k + 1 := by
      rw [show ((k : ℂ) + 1) = ((k + 1 : ℝ) : ℂ) by push_cast; ring, norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
    rw [h2]
    gcongr
    · exact beta_nonneg hM k
    · exact norm_choose_le hz k

/-- Ratio step of the majorant: for `k ≥ d + 1`, `β_{k+1} U^{k+1} ≤ q β_k U^k`. -/
lemma beta_step {M U : ℝ} (d : ℕ) (hM : 1 ≤ M) (hU : 0 ≤ U) {k : ℕ} (hk : d + 1 ≤ k) :
    beta M (k + 1) * U ^ (k + 1) ≤ U * (M + d + 1) / (d + 2) * (beta M k * U ^ k) := by
  have hb := beta_nonneg (by linarith) k (M := M)
  have hkr : (d : ℝ) + 1 ≤ k := by exact_mod_cast hk
  have hr : (M + k) / (k + 1) ≤ (M + d + 1) / (d + 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  simp only [beta, pow_succ]
  have hBU : 0 ≤ beta M k * U ^ k := mul_nonneg hb (pow_nonneg hU k)
  calc beta M k * (M + k) / (k + 1) * (U ^ k * U)
      = (M + k) / (k + 1) * U * (beta M k * U ^ k) := by ring
    _ ≤ (M + d + 1) / (d + 2) * U * (beta M k * U ^ k) := by gcongr
    _ = U * (M + d + 1) / (d + 2) * (beta M k * U ^ k) := by ring

/-- **Binomial remainder.** -/
theorem binom_rem_le (z : ℂ) {M U u : ℝ} (d : ℕ) (hz : ‖z‖ ≤ M) (hM : 1 ≤ M) (hu0 : 0 ≤ u)
    (huU : u ≤ U) (hq : U * (M + d + 1) / (d + 2) < 1) :
    ‖(1 + (u : ℂ)) ^ z - ∑ k ∈ Finset.range (d + 1), Ring.choose z k * (u : ℂ) ^ k‖ ≤
      beta M (d + 1) * U ^ (d + 1) / (1 - U * (M + d + 1) / (d + 2)) := by
  set q := U * (M + d + 1) / (d + 2) with hqdef
  have hU0 : 0 ≤ U := hu0.trans huU
  have hq0 : 0 ≤ q := by positivity
  have hU1 : U < 1 := by
    refine lt_of_le_of_lt ?_ hq
    rw [hqdef, le_div_iff₀ (by positivity)]
    nlinarith
  have hu1 : |u| < 1 := by rw [abs_of_nonneg hu0]; linarith
  have h := (hasSum_nat_add_iff' (d + 1)).mpr (binom_hasSum z hu1)
  have hg : HasSum (fun m : ℕ => beta M (d + 1) * U ^ (d + 1) * q ^ m)
      (beta M (d + 1) * U ^ (d + 1) / (1 - q)) := by
    have := (hasSum_geometric_of_lt_one hq0 hq).mul_left (beta M (d + 1) * U ^ (d + 1))
    rwa [← div_eq_mul_inv] at this
  refine h.norm_le_of_bounded hg fun m => ?_
  have hmaj : ∀ m : ℕ, beta M (d + 1 + m) * U ^ (d + 1 + m) ≤ beta M (d + 1) * U ^ (d + 1) * q ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      calc beta M (d + 1 + (m + 1)) * U ^ (d + 1 + (m + 1))
          ≤ q * (beta M (d + 1 + m) * U ^ (d + 1 + m)) :=
            beta_step d hM hU0 (k := d + 1 + m) (Nat.le_add_right _ _)
        _ ≤ q * (beta M (d + 1) * U ^ (d + 1) * q ^ m) := by gcongr
        _ = beta M (d + 1) * U ^ (d + 1) * q ^ (m + 1) := by ring
  rw [norm_mul, norm_pow, norm_real, Real.norm_eq_abs, abs_of_nonneg hu0, add_comm m]
  calc ‖Ring.choose z (d + 1 + m)‖ * u ^ (d + 1 + m)
      ≤ beta M (d + 1 + m) * U ^ (d + 1 + m) :=
        mul_le_mul (norm_choose_le hz _) (pow_le_pow_left₀ hu0 huU _) (by positivity)
          (beta_nonneg (by linarith) _)
    _ ≤ _ := hmaj m

/-- The cell factorisation `x^z = a^z (1 + (x − a)/a)^z`. -/
theorem cpow_cell {a x : ℝ} (ha : 0 < a) (hx : a ≤ x) (z : ℂ) :
    (x : ℂ) ^ z = (a : ℂ) ^ z * (1 + (((x - a) / a : ℝ) : ℂ)) ^ z := by
  have h1 : 0 ≤ 1 + (x - a) / a := by
    have : 0 ≤ (x - a) / a := div_nonneg (by linarith) ha.le
    linarith
  have hx' : (x : ℂ) = (a : ℂ) * ((1 + (x - a) / a : ℝ) : ℂ) := by
    rw [← ofReal_mul]; congr 1; field_simp; ring
  rw [hx', mul_cpow_ofReal_nonneg ha.le h1]
  push_cast; ring

/-- The repeat on geometric cells: `(r^j)^z = (r^z)^j`. -/
theorem cpow_geom {r : ℝ} (hr : 0 ≤ r) (z : ℂ) : ∀ j : ℕ,
    ((r ^ j : ℝ) : ℂ) ^ z = ((r : ℂ) ^ z) ^ j
  | 0 => by simp
  | j + 1 => by
    rw [pow_succ, ofReal_mul, mul_cpow_ofReal_nonneg (pow_nonneg hr j) hr, cpow_geom hr z j,
      pow_succ]

end AEGIS.RHCellBinomialV1

#print axioms AEGIS.RHCellBinomialV1.binom_rem_le
#print axioms AEGIS.RHCellBinomialV1.cpow_cell
#print axioms AEGIS.RHCellBinomialV1.cpow_geom
