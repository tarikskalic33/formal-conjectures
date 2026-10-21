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

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.BigOperators

/-! Exact finite congruence transport. No positivity or symmetry is assumed. -/

open scoped BigOperators ComplexConjugate

namespace AEGIS.CvSFiniteCongruenceV1

/-- Exchange the coefficient indices and the matrix indices of a finite sum. -/
theorem rotate_four_sums {ι κ ν μ V : Type*}
    [Fintype ι] [Fintype κ] [Fintype ν] [Fintype μ] [AddCommMonoid V]
    (f : ι → κ → ν → μ → V) :
    (∑ i, ∑ j, ∑ k, ∑ l, f i j k l) = ∑ k, ∑ l, ∑ i, ∑ j, f i j k l := by
  calc
    _ = ∑ i, ∑ k, ∑ j, ∑ l, f i j k l := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ j, ∑ l, f i j k l := Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ l, ∑ j, f i j k l := by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      exact Finset.sum_comm

/-- Congruence for arbitrary complex matrices, with conjugation on the second coordinate. -/
theorem quadratic_form_finite_congruence {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : κ → κ → ℂ) (X : κ → ι → ℂ) (v : ι → ℂ) :
    (∑ i, ∑ j, v i * conj (v j) * (∑ k, ∑ l, X k i * conj (X l j) * A k l)) =
      ∑ k, ∑ l, (∑ i, X k i * v i) * conj (∑ j, X l j * v j) * A k l := by
  simp_rw [map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [rotate_four_sums]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Applying a composed finite coefficient matrix equals composing the coefficient maps. -/
theorem transformed_coeff_linear {ι κ ν : Type*}
    [Fintype ι] [Fintype κ] [Fintype ν]
    (P : κ → ν → ℂ) (R : ν → ι → ℂ) (v : ι → ℂ) (k : κ) :
    (∑ i, (∑ j, P k j * R j i) * v i) = ∑ j, P k j * (∑ i, R j i * v i) := by
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Real coefficient matrices give the same congruence after complexification. -/
theorem quadratic_form_real_congruence {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : κ → κ → ℝ) (X : κ → ι → ℝ) (v : ι → ℂ) :
    (∑ i, ∑ j, v i * conj (v j) *
      ((∑ k, ∑ l, X k i * X l j * A k l : ℝ) : ℂ)) =
      ∑ k, ∑ l, (∑ i, (X k i : ℂ) * v i) *
        conj (∑ j, (X l j : ℂ) * v j) * (A k l : ℂ) := by
  simpa only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.conj_ofReal] using
    quadratic_form_finite_congruence (fun k l => (A k l : ℂ))
      (fun k i => (X k i : ℂ)) v

end AEGIS.CvSFiniteCongruenceV1

#check @AEGIS.CvSFiniteCongruenceV1.quadratic_form_finite_congruence
#print axioms AEGIS.CvSFiniteCongruenceV1.rotate_four_sums
#print axioms AEGIS.CvSFiniteCongruenceV1.quadratic_form_finite_congruence
#print axioms AEGIS.CvSFiniteCongruenceV1.transformed_coeff_linear
#print axioms AEGIS.CvSFiniteCongruenceV1.quadratic_form_real_congruence
