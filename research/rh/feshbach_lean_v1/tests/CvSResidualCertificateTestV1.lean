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

import CvSResidualCertificateV1
open scoped BigOperators ComplexConjugate
open AEGIS.CvSResidualCertificateV1

-- Sharp residual boundary: centre 2I, all-one majorant, row sum 2.
-- The resulting all-one matrix is PSD but singular. No strict margin is inferred.
example (z : Fin 2 → ℂ) :
    0 ≤ (∑ i : Fin 2, ∑ j : Fin 2, conj (z i) * z j * (1 : ℂ)).re := by
  apply actual_hermitian_nonneg (fun _ _ => 1)
    (fun i j => if i = j then 2 else 0) (fun _ _ => 1) 2
  · intro i j
    split_ifs <;> norm_num
  · intro i j
    rfl
  · intro i
    norm_num
  · intro x
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    nlinarith

-- Without the symmetry of the error majorant, a row bound is insufficient.
-- E = [[0,1],[0,1]] has each absolute row sum at most 1.
-- At x=(1,2), xᵀEx=6 > ||x||²=5.
example : (0 : ℚ) + 1 ≤ 1 ∧ (0 : ℚ) + 1 ≤ 1 ∧
    (1 : ℚ) * 2 + 2 * 2 > 1 ^ 2 + 2 ^ 2 := by
  norm_num

-- An underestimated symmetric row budget must fail the input check.
example : ¬ ((∑ _j : Fin 2, (1 : ℚ)) ≤ 1) := by
  norm_num

-- Inward rounding is not a valid enclosure for a positive sub-ulp entry.
example : ¬ ((1 : ℚ) / 2 ^ 41 ≤ 0 / 2 ^ 40) := by norm_num
