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
/- Exact scale transport for the Q96 to Q64 source enclosure check. -/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace AEGIS.CvSDyadicEnclosureV1

/-- Multiplying an integer endpoint by `2^d` preserves its dyadic real value. -/
theorem rescale_endpoint (p d : ℕ) (m : ℤ) :
    ((m * 2 ^ d : ℤ) : ℝ) / 2 ^ (p + d) = (m : ℝ) / 2 ^ p := by
  push_cast
  rw [pow_add]
  field_simp

/-- Integer containment at the finer scale implies the original real enclosure. -/
theorem enclosure_transport (p d : ℕ) (lo hi fineLo fineHi : ℤ) (x : ℝ)
    (hl : lo * 2 ^ d ≤ fineLo) (hh : fineHi ≤ hi * 2 ^ d)
    (hx : (fineLo : ℝ) / 2 ^ (p + d) ≤ x ∧ x ≤ (fineHi : ℝ) / 2 ^ (p + d)) :
    (lo : ℝ) / 2 ^ p ≤ x ∧ x ≤ (hi : ℝ) / 2 ^ p := by
  have hp : (0 : ℝ) < 2 ^ (p + d) := pow_pos (by norm_num) _
  constructor
  · calc
      (lo : ℝ) / 2 ^ p = ((lo * 2 ^ d : ℤ) : ℝ) / 2 ^ (p + d) :=
        (rescale_endpoint p d lo).symm
      _ ≤ (fineLo : ℝ) / 2 ^ (p + d) :=
        div_le_div_of_nonneg_right (by exact_mod_cast hl) hp.le
      _ ≤ x := hx.1
  · calc
      x ≤ (fineHi : ℝ) / 2 ^ (p + d) := hx.2
      _ ≤ ((hi * 2 ^ d : ℤ) : ℝ) / 2 ^ (p + d) :=
        div_le_div_of_nonneg_right (by exact_mod_cast hh) hp.le
      _ = (hi : ℝ) / 2 ^ p := rescale_endpoint p d hi

end AEGIS.CvSDyadicEnclosureV1

#print axioms AEGIS.CvSDyadicEnclosureV1.rescale_endpoint
#print axioms AEGIS.CvSDyadicEnclosureV1.enclosure_transport
