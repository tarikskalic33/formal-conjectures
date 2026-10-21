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
/- Encode source rational boxes at arbitrary fixed-point precision with outward rounding. -/
import RHFixIntervalV1
import Mathlib.Data.Rat.Floor

namespace AEGIS.CvSRationalIntervalV1
open AEGIS.RHFixIntervalV1

def rationalRange (p : ℕ) (lo hi : ℚ) : Iv :=
  ⟨⌊lo * (2 : ℚ) ^ p⌋, ⌈hi * (2 : ℚ) ^ p⌉⟩

/-- Source rational bounds imply the outward fixed-point interval contract. -/
theorem rationalRange_mem (p : ℕ) (lo hi : ℚ) {x : ℝ}
    (hl : (lo : ℝ) ≤ x) (hh : x ≤ (hi : ℝ)) :
    (rationalRange p lo hi).Mem p x := by
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have hfloor : ((⌊lo * (2 : ℚ) ^ p⌋ : ℤ) : ℝ) ≤ (lo : ℝ) * 2 ^ p := by
    exact_mod_cast (Int.floor_le (lo * (2 : ℚ) ^ p))
  have hceil : (hi : ℝ) * 2 ^ p ≤ ((⌈hi * (2 : ℚ) ^ p⌉ : ℤ) : ℝ) := by
    exact_mod_cast (Int.le_ceil (hi * (2 : ℚ) ^ p))
  constructor
  · exact (div_le_iff₀ hp).2 (hfloor.trans (mul_le_mul_of_nonneg_right hl hp.le))
  · exact (le_div_iff₀ hp).2 ((mul_le_mul_of_nonneg_right hh hp.le).trans hceil)

end AEGIS.CvSRationalIntervalV1
#print axioms AEGIS.CvSRationalIntervalV1.rationalRange_mem
