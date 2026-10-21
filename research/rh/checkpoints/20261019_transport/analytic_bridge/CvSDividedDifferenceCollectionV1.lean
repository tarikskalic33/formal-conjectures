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
/- Exact finite divided-difference collection for source interval transport. -/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace AEGIS.CvSDividedDifferenceCollectionV1

/-- Collect the shared tau variables before applying interval bounds.
No positivity, symmetry, or distinct-node hypothesis is used in this identity. -/
theorem divided_difference_collection {ι : Type*} [Fintype ι]
    (x y tau nu : ι → ℝ) (C : ℝ) :
    (∑ k, ∑ l, x k * y l * (C * ((tau k - tau l) / (nu k - nu l)))) =
      ∑ k, C * tau k *
        (x k * (∑ l, y l / (nu k - nu l)) +
         y k * (∑ l, x l / (nu k - nu l))) := by
  have hterm (k l : ι) :
      x k * y l * (C * ((tau k - tau l) / (nu k - nu l))) =
        C * tau k * x k * (y l / (nu k - nu l)) -
        C * tau l * y l * (x k / (nu k - nu l)) := by ring
  simp_rw [hterm, Finset.sum_sub_distrib]
  have hswap : (∑ k, ∑ l, C * tau l * y l * (x k / (nu k - nu l))) =
      -(∑ k, ∑ l, C * tau k * y k * (x l / (nu k - nu l))) := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    rw [show nu l - nu k = -(nu k - nu l) by ring, div_neg]
    ring
  rw [hswap, sub_neg_eq_add, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  simp only [mul_add, Finset.mul_sum]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  ring


/-- Diagonal entries and collected source tau variables give the full finite form. -/
theorem diagonal_divided_difference_collection {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x y tau nu D : ι → ℝ) (C : ℝ) :
    (∑ k, ∑ l, x k * y l *
      (if k = l then D k else C * ((tau k - tau l) / (nu k - nu l)))) =
      (∑ k, x k * y k * D k) +
      ∑ k, C * tau k *
        (x k * (∑ l, y l / (nu k - nu l)) +
         y k * (∑ l, x l / (nu k - nu l))) := by
  classical
  have hdecomp (k l : ι) :
      (if k = l then D k else C * ((tau k - tau l) / (nu k - nu l))) =
        (if k = l then D k else 0) + C * ((tau k - tau l) / (nu k - nu l)) := by
    by_cases h : k = l
    · simp [h]
    · simp [h]
  have hdiag : (∑ k, ∑ l, x k * y l * (if k = l then D k else 0)) =
      ∑ k, x k * y k * D k := by
    apply Finset.sum_congr rfl
    intro k _
    simp [mul_ite]
  calc
    _ = (∑ k, ∑ l, x k * y l * (if k = l then D k else 0)) +
        ∑ k, ∑ l, x k * y l * (C * ((tau k - tau l) / (nu k - nu l))) := by
      simp_rw [hdecomp, mul_add, Finset.sum_add_distrib]
    _ = _ := by rw [hdiag, divided_difference_collection]

end AEGIS.CvSDividedDifferenceCollectionV1

#check @AEGIS.CvSDividedDifferenceCollectionV1.divided_difference_collection
#print axioms AEGIS.CvSDividedDifferenceCollectionV1.divided_difference_collection

#print axioms AEGIS.CvSDividedDifferenceCollectionV1.diagonal_divided_difference_collection
