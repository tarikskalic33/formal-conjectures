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
/- Source-independent interval encoding of the CvS L=6/5 frequency factor.
Uses Mathlib's proved decimal pi bounds and the existing outward interval primitives. -/
import CvSRationalIntervalV1
import Mathlib.Analysis.Real.Pi.Bounds

namespace AEGIS.CvSFrequencyIntervalV1
open AEGIS.RHFixIntervalV1 AEGIS.CvSRationalIntervalV1

def piLo : ℚ := 314159265358979323846 / 100000000000000000000
def piHi : ℚ := 314159265358979323847 / 100000000000000000000

theorem pi_bounds : (piLo : ℝ) ≤ Real.pi ∧ Real.pi ≤ piHi := by
  constructor
  · have h := Real.pi_gt_d20
    norm_num [piLo] at h ⊢
    exact h.le
  · have h := Real.pi_lt_d20
    norm_num [piHi] at h ⊢
    exact h.le

def frequencyLo (n : ℤ) : ℚ := -(25 / 9) * piHi ^ 2 * (n : ℚ) ^ 2 - 1 / 4
def frequencyHi (n : ℤ) : ℚ := -(25 / 9) * piLo ^ 2 * (n : ℚ) ^ 2 - 1 / 4

theorem frequency_bounds (n : ℤ) :
    (frequencyLo n : ℝ) ≤ -(2 * Real.pi * (n : ℝ) / (6 / 5 : ℝ)) ^ 2 - 1 / 4 ∧
    -(2 * Real.pi * (n : ℝ) / (6 / 5 : ℝ)) ^ 2 - 1 / 4 ≤ (frequencyHi n : ℝ) := by
  obtain ⟨hl, hh⟩ := pi_bounds
  have hlo : (0 : ℝ) ≤ piLo := by norm_num [piLo]
  have hslo : (piLo : ℝ) ^ 2 ≤ Real.pi ^ 2 := pow_le_pow_left₀ hlo hl 2
  have hshi : Real.pi ^ 2 ≤ (piHi : ℝ) ^ 2 := pow_le_pow_left₀ Real.pi_pos.le hh 2
  have hn := sq_nonneg (n : ℝ)
  have ha := mul_le_mul_of_nonneg_right hslo hn
  have hb := mul_le_mul_of_nonneg_right hshi hn
  simp only [frequencyLo, frequencyHi]
  push_cast
  constructor <;> nlinarith

/-- Matches the generator's two outward multiplications: the frequency factor
and the exact second-difference coefficient w/2^42. -/
def coefficientInterval (p : ℕ) (n w : ℤ) : Iv :=
  (rationalRange p (frequencyLo n) (frequencyHi n)).mul p
    (rationalRange p ((w : ℚ) / 2 ^ 42) ((w : ℚ) / 2 ^ 42))

theorem coefficient_mem (p : ℕ) (n w : ℤ) :
    (coefficientInterval p n w).Mem p
      ((-(2 * Real.pi * (n : ℝ) / (6 / 5 : ℝ)) ^ 2 - 1 / 4) * (w : ℝ) / 2 ^ 42) := by
  have hf := rationalRange_mem p _ _ (frequency_bounds n).1 (frequency_bounds n).2
  have hw : (rationalRange p ((w : ℚ) / 2 ^ 42) ((w : ℚ) / 2 ^ 42)).Mem p
      ((w : ℝ) / 2 ^ 42) := by
    apply rationalRange_mem <;> push_cast <;> exact le_rfl
  simpa only [mul_div_assoc, coefficientInterval] using Iv.mem_mul p hf hw

def lpInterval (p : ℕ) : Iv := rationalRange p ((6 / 5) / piHi) ((6 / 5) / piLo)

theorem lp_mem (p : ℕ) : (lpInterval p).Mem p ((6 / 5 : ℝ) / Real.pi) := by
  obtain ⟨hl, hh⟩ := pi_bounds
  have hlo : (0 : ℝ) < piLo := by norm_num [piLo]
  apply rationalRange_mem <;> push_cast
  · exact div_le_div_of_nonneg_left (by norm_num) Real.pi_pos hh
  · exact div_le_div_of_nonneg_left (by norm_num) hlo hl

def lpSquaredInterval (p : ℕ) : Iv := (lpInterval p).mul p (lpInterval p)

theorem lp_squared_mem (p : ℕ) :
    (lpSquaredInterval p).Mem p (((6 / 5 : ℝ) / Real.pi) ^ 2) := by
  simpa only [pow_two, lpSquaredInterval] using Iv.mem_mul p (lp_mem p) (lp_mem p)

end AEGIS.CvSFrequencyIntervalV1
#print axioms AEGIS.CvSFrequencyIntervalV1.pi_bounds
#print axioms AEGIS.CvSFrequencyIntervalV1.frequency_bounds
#print axioms AEGIS.CvSFrequencyIntervalV1.coefficient_mem
#print axioms AEGIS.CvSFrequencyIntervalV1.lp_mem
#print axioms AEGIS.CvSFrequencyIntervalV1.lp_squared_mem
#check @AEGIS.CvSFrequencyIntervalV1.pi_bounds
#check @AEGIS.CvSFrequencyIntervalV1.frequency_bounds
#check @AEGIS.CvSFrequencyIntervalV1.coefficient_mem
#check @AEGIS.CvSFrequencyIntervalV1.lp_mem
#check @AEGIS.CvSFrequencyIntervalV1.lp_squared_mem
