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
/- Exact midpoint-radius control for the row-budget interval products. -/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Complex.BigOperators

open scoped BigOperators
namespace AEGIS.CvSMidpointRadiusV1

/-- Error propagation for an actual real product, with explicit midpoint radii. -/
theorem product_error {x y x₀ y₀ rx ry : ℝ}
    (hx : |x - x₀| ≤ rx) (hy : |y - y₀| ≤ ry) :
    |x * y - x₀ * y₀| ≤ |x₀| * ry + rx * |y₀| + rx * ry := by
  have hrx : 0 ≤ rx := (abs_nonneg _).trans hx
  calc
    |x * y - x₀ * y₀| =
        |(x₀ * (y - y₀) + (x - x₀) * y₀) + (x - x₀) * (y - y₀)| := by
      congr 1
      ring
    _ ≤ |x₀ * (y - y₀) + (x - x₀) * y₀| + |(x - x₀) * (y - y₀)| :=
      abs_add_le _ _
    _ ≤ (|x₀ * (y - y₀)| + |(x - x₀) * y₀|) + |(x - x₀) * (y - y₀)| :=
      add_le_add (abs_add_le _ _) le_rfl
    _ = (|x₀| * |y - y₀| + |x - x₀| * |y₀|) + |x - x₀| * |y - y₀| := by
      simp only [abs_mul]
    _ ≤ |x₀| * ry + rx * |y₀| + rx * ry :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left hy (abs_nonneg _))
        (mul_le_mul_of_nonneg_right hx (abs_nonneg _)))
        (mul_le_mul hx hy (abs_nonneg _) hrx)

/-- Dimension-independent enclosure for every real matrix-product entry. -/
theorem sum_product_error {ι : Type*} [Fintype ι] (x y x₀ y₀ rx ry : ι → ℝ)
    (hx : ∀ k, |x k - x₀ k| ≤ rx k) (hy : ∀ k, |y k - y₀ k| ≤ ry k) :
    |(∑ k, x k * y k) - ∑ k, x₀ k * y₀ k| ≤
      ∑ k, (|x₀ k| * ry k + rx k * |y₀ k| + rx k * ry k) := by
  rw [← Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun k _ => product_error (hx k) (hy k))

end AEGIS.CvSMidpointRadiusV1
#print axioms AEGIS.CvSMidpointRadiusV1.product_error
#print axioms AEGIS.CvSMidpointRadiusV1.sum_product_error
