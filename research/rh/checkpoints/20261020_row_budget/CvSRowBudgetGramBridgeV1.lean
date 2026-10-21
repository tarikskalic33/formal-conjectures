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
/-
AEGIS Omega: native composition of finite residual Gram energy, a tail
Hermitian form and the already kernel-proved Q80 row-budget certificate.

No analytic enclosure is assumed to be kernel-proved here: the explicit
hI hypothesis is the remaining source-to-Q80 obligation.
-/
import CvSRowBudgetAlgebraV1
import CvSRelativeRowCertificateL12V1

open scoped BigOperators ComplexConjugate

namespace AEGIS.CvSRowBudgetGramBridgeV1

open AEGIS.CvSPackedGramV1
open AEGIS.CvSRowBudgetAlgebraV1
open AEGIS.CvSRelativeRowCertificateL12V1

/-- Residual-row Gram matrix plus the upper matrix for the tail. -/
noncomputable def budgetMatrix {κ : Type*} [Fintype κ]
    (Z : κ → Fin 139 → ℝ) (G : Fin 139 → Fin 139 → ℝ)
    (i j : Fin 139) : ℝ :=
  (∑ k, Z k i * Z k j) + G i j

/-- Actual real row energy plus the Hermitian Gram tail form. -/
noncomputable def budgetEnergy {κ : Type*} [Fintype κ]
    (Z : κ → Fin 139 → ℝ) (G : Fin 139 → Fin 139 → ℝ)
    (v : Fin 139 → ℂ) : ℝ :=
  (∑ k, ‖∑ i, (Z k i : ℂ) * v i‖ ^ 2) +
    (∑ i, ∑ j, v i * conj (v j) * (G i j : ℂ)).re

/-- The finite row energy is exactly the quadratic form of Zᵀ Z + G. -/
theorem budgetEnergy_eq_matrix {κ : Type*} [Fintype κ]
    (Z : κ → Fin 139 → ℝ) (G : Fin 139 → Fin 139 → ℝ)
    (v : Fin 139 → ℂ) :
    budgetEnergy Z G v =
      (∑ i, ∑ j, v i * conj (v j) * (budgetMatrix Z G i j : ℂ)).re := by
  rw [budgetEnergy, AEGIS.CvSRowBudgetAlgebraV1.row_energy_eq]
  simp only [budgetMatrix, Complex.ofReal_add, mul_add,
    Finset.sum_add_distrib, Complex.add_re]

theorem budgetMatrix_symm {κ : Type*} [Fintype κ]
    (Z : κ → Fin 139 → ℝ) (G : Fin 139 → Fin 139 → ℝ)
    (hG : ∀ i j, G i j = G j i) :
    ∀ i j, budgetMatrix Z G i j = budgetMatrix Z G j i := by
  intro i j
  simp only [budgetMatrix]
  rw [hG i j]
  congr 1
  exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)

/-- Composition of the original Q80 integer certificate with the actual
residual-energy Gram identity. The unproved analytic task is precisely hI,
not the positivity or the complex-vector algebra. -/
theorem budgetEnergy_le_of_Iv {κ : Type*} [Fintype κ]
    (A : Fin 139 → Fin 139 → ℝ)
    (Z : κ → Fin 139 → ℝ) (G : Fin 139 → Fin 139 → ℝ)
    (hA : ∀ i j, A i j = A j i)
    (hG : ∀ i j, G i j = G j i)
    (hI : ∀ i j : Fin 139,
      (Im intervals i.val j.val).Mem 80
        (40 * A i j - budgetMatrix Z G i j)) :
    ∀ v : Fin 139 → ℂ,
      budgetEnergy Z G v ≤ 40 *
        (∑ i, ∑ j, v i * conj (v j) * (A i j : ℂ)).re := by
  have hC : ∀ i j, 40 * A i j - budgetMatrix Z G i j =
      40 * A j i - budgetMatrix Z G j i := by
    intro i j
    rw [hA i j, budgetMatrix_symm Z G hG i j]
  have hPositive : ∀ v : Fin 139 → ℂ,
      0 ≤ (∑ i, ∑ j, v i * conj (v j) *
        ((40 * A i j - budgetMatrix Z G i j : ℝ) : ℂ)).re := by
    intro v
    have hc := quad_lower_complex 80 base B eps eta factor intervals
      row_budget_check_true
      (fun i j => 40 * A i j - budgetMatrix Z G i j) hC hI v
    have hm : (0 : ℝ) ≤ ((eps - eta : ℤ) : ℝ) := by
      exact_mod_cast row_budget_margin_positive.le
    have hn : 0 ≤ ∑ i, ‖v i‖ ^ 2 :=
      Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have hzero : 0 ≤ ((eps - eta : ℤ) : ℝ) * ∑ i, ‖v i‖ ^ 2 :=
      mul_nonneg hm hn
    have hpow : (0 : ℝ) < 2 ^ 80 := by positivity
    have hscaled := le_trans hzero hc
    by_contra hneg
    have hh : (∑ i, ∑ j, v i * conj (v j) *
        ((40 * A i j - budgetMatrix Z G i j : ℝ) : ℂ)).re < 0 :=
      lt_of_not_ge hneg
    exact (not_lt_of_ge hscaled) (mul_neg_of_pos_of_neg hpow hh)
  intro v
  rw [budgetEnergy_eq_matrix]
  exact (AEGIS.CvSRowBudgetAlgebraV1.relative_budget_of_matrix_nonneg
    A (budgetMatrix Z G) 40 hPositive) v

end AEGIS.CvSRowBudgetGramBridgeV1

#print axioms AEGIS.CvSRowBudgetGramBridgeV1.budgetEnergy_eq_matrix
#print axioms AEGIS.CvSRowBudgetGramBridgeV1.budgetMatrix_symm
#print axioms AEGIS.CvSRowBudgetGramBridgeV1.budgetEnergy_le_of_Iv
