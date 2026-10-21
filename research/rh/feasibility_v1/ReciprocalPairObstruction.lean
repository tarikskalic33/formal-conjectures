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

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
A source-independent countertest for a proposed Li-pairing argument.
Positive reciprocal pairing alone gives the opposite sign off the unit circle.
This does not assert the existence of any off-critical zeta zero.
-/
namespace AEGIS.RouteD

theorem reciprocal_pair_strict_negative (w : ℝ) (hw : 0 < w) (hunit : w ≠ 1) :
    2 - (w + w⁻¹) < 0 := by
  have hprod : w * w⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hw)
  have hsquare : 0 < (w - 1) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hunit)
  have hgap : 0 < w * (w + w⁻¹ - 2) := by nlinarith
  have : 0 < w + w⁻¹ - 2 := (mul_pos_iff_of_pos_left hw).mp hgap
  linarith

theorem reciprocal_pair_nonnegative_iff_unit (w : ℝ) (hw : 0 < w) :
    0 ≤ 2 - (w + w⁻¹) ↔ w = 1 := by
  constructor
  · intro h
    by_contra hn
    exact (not_lt_of_ge h) (reciprocal_pair_strict_negative w hw hn)
  · intro h
    subst w
    simp only [inv_one]
    linarith

#check reciprocal_pair_strict_negative
#check reciprocal_pair_nonnegative_iff_unit
#print axioms reciprocal_pair_strict_negative
#print axioms reciprocal_pair_nonnegative_iff_unit

end AEGIS.RouteD
