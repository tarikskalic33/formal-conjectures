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
/- Preserve the strictly positive original certificate margin in the complex row budget. -/
import CvSRowBudgetGramBridgeV1
open scoped BigOperators ComplexConjugate
namespace AEGIS.CvSStrictRowBudgetV1
open AEGIS.RHFixIntervalV1 AEGIS.CvSPackedGramV1
open AEGIS.CvSRelativeRowCertificateL12V1 AEGIS.CvSRowBudgetGramBridgeV1

noncomputable def margin : ℝ := ((eps - eta : ℤ) : ℝ) / 2^80

theorem margin_exact : margin = 167597168023440173239 / (604462909807314587353088 : ℝ) := by
  norm_num [margin, eps, eta]

theorem margin_positive : 0 < margin := by
  rw [margin_exact]
  positivity

/-- The original signed matrix bound retains a quantitative gap for every vector. -/
theorem budgetEnergy_margin_of_Iv {κ : Type*} [Fintype κ]
    (A : Fin 139 → Fin 139 → ℝ) (Z : κ → Fin 139 → ℝ)
    (G : Fin 139 → Fin 139 → ℝ)
    (hA : ∀ i j, A i j = A j i) (hG : ∀ i j, G i j = G j i)
    (hI : ∀ i j : Fin 139, (Im intervals i.val j.val).Mem 80
      (40 * A i j - budgetMatrix Z G i j)) (v : Fin 139 → ℂ) :
    margin * (∑ i, ‖v i‖ ^ 2) + budgetEnergy Z G v ≤
      40 * (∑ i, ∑ j, v i * conj (v j) * (A i j : ℂ)).re := by
  have hs : ∀ i j, 40 * A i j - budgetMatrix Z G i j =
      40 * A j i - budgetMatrix Z G j i := by
    intro i j
    rw [hA i j, budgetMatrix_symm Z G hG i j]
  have hp := quad_lower_complex 80 base B eps eta factor intervals row_budget_check_true
    (fun i j => 40 * A i j - budgetMatrix Z G i j) hs hI v
  have he : (∑ i, ∑ j, v i * conj (v j) *
      ((40 * A i j - budgetMatrix Z G i j : ℝ) : ℂ)) =
      (40 : ℂ) * (∑ i, ∑ j, v i * conj (v j) * (A i j : ℂ)) -
        ∑ i, ∑ j, v i * conj (v j) * (budgetMatrix Z G i j : ℂ) := by
    simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_ofNat,
      mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he, Complex.sub_re, ← budgetEnergy_eq_matrix] at hp
  have h40 : ((40 : ℂ) * (∑ i, ∑ j, v i * conj (v j) * (A i j : ℂ))).re =
      40 * (∑ i, ∑ j, v i * conj (v j) * (A i j : ℂ)).re := by
    norm_num [Complex.mul_re]
  rw [h40] at hp
  rw [mul_comm (2^80 : ℝ)] at hp
  have hdiv := (div_le_iff₀ (by positivity : (0 : ℝ) < 2^80)).mpr hp
  have hh : margin * (∑ i, ‖v i‖ ^ 2) ≤
      40 * (∑ i, ∑ j, v i * conj (v j) * (A i j : ℂ)).re - budgetEnergy Z G v := by
    simpa only [margin, div_mul_eq_mul_div] using hdiv
  linarith
end AEGIS.CvSStrictRowBudgetV1
#check @AEGIS.CvSStrictRowBudgetV1.budgetEnergy_margin_of_Iv
#print axioms AEGIS.CvSStrictRowBudgetV1.budgetEnergy_margin_of_Iv
#print axioms AEGIS.CvSStrictRowBudgetV1.margin_exact
#print axioms AEGIS.CvSStrictRowBudgetV1.margin_positive
