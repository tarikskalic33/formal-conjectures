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

import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Fintype.BigOperators

open scoped BigOperators

namespace AEGIS.CvSRealBasisBoundV1

/-- Cauchy-Schwarz for one real coefficient row and arbitrary complex amplitudes. -/
theorem real_row_normSq_le {ι : Type*} [Fintype ι] (r : ι → ℝ) (v : ι → ℂ) :
    Complex.normSq (∑ j, (r j : ℂ) * v j) ≤
      (∑ j, r j ^ 2) * ∑ j, Complex.normSq (v j) := by
  have hre := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ r (fun j => (v j).re)
  have him := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ r (fun j => (v j).im)
  have heq : Complex.normSq (∑ j, (r j : ℂ) * v j) =
      (∑ j, r j * (v j).re) ^ 2 + (∑ j, r j * (v j).im) ^ 2 := by
    simp only [Complex.normSq_apply, Complex.re_sum, Complex.im_sum,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, add_zero, ← sq]
  calc
    _ = _ := heq
    _ ≤ (∑ j, r j ^ 2) * (∑ j, (v j).re ^ 2) +
        (∑ j, r j ^ 2) * (∑ j, (v j).im ^ 2) := add_le_add hre him
    _ = _ := by
      simp only [Complex.normSq_apply, ← sq, Finset.sum_add_distrib]
      ring

/-- A dimension-explicit Frobenius squared bound for a real matrix on complex vectors. -/
theorem real_matrix_normSq_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (R : ι → κ → ℝ) (v : κ → ℂ) :
    (∑ i, Complex.normSq (∑ j, (R i j : ℂ) * v j)) ≤
      (∑ i, ∑ j, R i j ^ 2) * ∑ j, Complex.normSq (v j) := by
  calc
    _ ≤ ∑ i, (∑ j, R i j ^ 2) * ∑ j, Complex.normSq (v j) :=
      Finset.sum_le_sum fun i _ => real_row_normSq_le (R i) v
    _ = _ := (Finset.sum_mul ..).symm

/-- One nonzero entry gives a strictly positive Frobenius budget. -/
theorem frobenius_pos_of_entry {ι κ : Type*} [Fintype ι] [Fintype κ]
    (R : ι → κ → ℝ) (i : ι) (j : κ) (h : R i j ≠ 0) :
    0 < ∑ a, ∑ b, R a b ^ 2 := by
  have hrow : R i j ^ 2 ≤ ∑ b, R i b ^ 2 :=
    Finset.single_le_sum (fun b _ => sq_nonneg (R i b)) (Finset.mem_univ j)
  have htotal : (∑ b, R i b ^ 2) ≤ ∑ a, ∑ b, R a b ^ 2 :=
    Finset.single_le_sum (fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg (R a b))
      (Finset.mem_univ i)
  exact (sq_pos_of_ne_zero h).trans_le (hrow.trans htotal)

end AEGIS.CvSRealBasisBoundV1

#print axioms AEGIS.CvSRealBasisBoundV1.real_row_normSq_le
#print axioms AEGIS.CvSRealBasisBoundV1.real_matrix_normSq_le
#print axioms AEGIS.CvSRealBasisBoundV1.frobenius_pos_of_entry
