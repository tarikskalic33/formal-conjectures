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
/- The actual cross kernel is 2*pi times the projected low kernel. -/
import CvSFrequencyIntervalV1
namespace AEGIS.CvSSourceQNormalizeV1
open AEGIS.RHFixIntervalV1 AEGIS.CvSRationalIntervalV1 AEGIS.CvSFrequencyIntervalV1

def inverseTwoPi : Iv := (lpInterval 96).mul 96 (rationalRange 96 (5/12) (5/12))

theorem inverseTwoPi_mem : inverseTwoPi.Mem 96 (1 / (2 * Real.pi)) := by
  have hrat : (rationalRange 96 (5/12) (5/12)).Mem 96 (5/12 : ℝ) := by
    apply rationalRange_mem <;> norm_num
  have h := Iv.mem_mul 96 (lp_mem 96) hrat
  have he : ((6/5 : ℝ) / Real.pi) * (5/12) = 1 / (2 * Real.pi) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [he] at h
  exact h

def normalize (I : Iv) : Iv := inverseTwoPi.mul 96 I

theorem normalize_mem (I : Iv) (q : ℝ) (hI : I.Mem 96 (2 * Real.pi * q)) :
    (normalize I).Mem 96 q := by
  have h := Iv.mem_mul 96 inverseTwoPi_mem hI
  have he : (1 / (2 * Real.pi)) * (2 * Real.pi * q) = q := by
    field_simp [Real.pi_ne_zero]
  rw [he] at h
  exact h
end AEGIS.CvSSourceQNormalizeV1
#print axioms AEGIS.CvSSourceQNormalizeV1.inverseTwoPi_mem
#print axioms AEGIS.CvSSourceQNormalizeV1.normalize_mem
