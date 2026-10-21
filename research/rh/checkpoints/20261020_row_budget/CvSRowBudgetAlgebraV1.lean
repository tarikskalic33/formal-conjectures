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
/- Finite Gram identities for the signed relative CvS row budget. -/
import CvSFiniteCongruenceV1
import Mathlib.Analysis.Complex.Norm

open scoped BigOperators ComplexConjugate
namespace AEGIS.CvSRowBudgetAlgebraV1

/-- A real finite residual matrix has exactly its Gram quadratic energy. -/
theorem row_energy_eq {ι κ : Type*} [Fintype ι] [Fintype κ]
    (R : κ → ι → ℝ) (v : ι → ℂ) :
    (∑ k, ‖∑ i, (R k i : ℂ) * v i‖ ^ 2) =
      (∑ i, ∑ j, v i * conj (v j) * ((∑ k, R k i * R k j : ℝ) : ℂ)).re := by
  classical
  have h := AEGIS.CvSFiniteCongruenceV1.quadratic_form_real_congruence
    (fun k l : κ => if k = l then (1 : ℝ) else 0) R v
  simpa [mul_ite, Complex.re_sum, Complex.mul_conj, Complex.sq_norm, Complex.normSq_apply] using
    (congrArg Complex.re h).symm

/-- A signed matrix certificate supplies the relative budget for every complex vector.
No absolute bounds on individual mixed Gram terms are required. -/
theorem relative_budget_of_matrix_nonneg {ι : Type*} [Fintype ι]
    (A B : ι → ι → ℝ) (kappa : ℝ)
    (h : ∀ v : ι → ℂ, 0 ≤
      (∑ i, ∑ j, v i * conj (v j) * ((kappa * A i j - B i j : ℝ) : ℂ)).re) :
    ∀ v : ι → ℂ,
      (∑ i, ∑ j, v i * conj (v j) * (B i j : ℂ)).re ≤
        kappa * (∑ i, ∑ j, v i * conj (v j) * (A i j : ℂ)).re := by
  intro v
  have hc : (∑ i, ∑ j, v i * conj (v j) * ((kappa * A i j - B i j : ℝ) : ℂ)) =
      (kappa : ℂ) * (∑ i, ∑ j, v i * conj (v j) * (A i j : ℂ)) -
        ∑ i, ∑ j, v i * conj (v j) * (B i j : ℂ) := by
    simp only [Complex.ofReal_sub, Complex.ofReal_mul, mul_sub,
      Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hp := h v
  rw [hc, Complex.sub_re, Complex.re_ofReal_mul] at hp
  exact sub_nonneg.mp hp

end AEGIS.CvSRowBudgetAlgebraV1
#print axioms AEGIS.CvSRowBudgetAlgebraV1.row_energy_eq

#print axioms AEGIS.CvSRowBudgetAlgebraV1.relative_budget_of_matrix_nonneg
