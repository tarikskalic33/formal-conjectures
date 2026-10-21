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

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Complex.Basic

open scoped BigOperators

namespace AEGIS.CvSTriangularTransportV1

/-- An upper triangular finite coefficient map with nonzero diagonal is onto.
This uses algebraic back substitution, with no analytic or positivity premise. -/
theorem upper_triangular_surjective {K : Type*} [Field K] (n : ℕ)
    (A : Fin n → Fin n → K)
    (hupper : ∀ i j, j < i → A i j = 0)
    (hdiag : ∀ i, A i i ≠ 0) :
    Function.Surjective (fun (v : Fin n → K) (i : Fin n) => ∑ j, A i j * v j) := by
  induction n with
  | zero =>
    intro c
    refine ⟨Fin.elim0, ?_⟩
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    intro c
    let z : K := c (Fin.last n) / A (Fin.last n) (Fin.last n)
    let B : Fin n → Fin n → K := fun i j => A i.castSucc j.castSucc
    have hBu : ∀ i j, j < i → B i j = 0 := by
      intro i j h
      exact hupper i.castSucc j.castSucc h
    have hBd : ∀ i, B i i ≠ 0 := fun i => hdiag i.castSucc
    obtain ⟨v, hv⟩ := ih B hBu hBd
      (fun i => c i.castSucc - A i.castSucc (Fin.last n) * z)
    refine ⟨Fin.lastCases z v, ?_⟩
    funext i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · change (∑ j, A (Fin.last n) j * Fin.lastCases z v j) = c (Fin.last n)
      rw [Fin.sum_univ_castSucc]
      have hz : ∑ j : Fin n, A (Fin.last n) j.castSucc *
          Fin.lastCases z v j.castSucc = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        rw [hupper _ _ (Fin.castSucc_lt_last j), zero_mul]
      rw [hz, zero_add, Fin.lastCases_last]
      exact mul_div_cancel₀ _ (hdiag (Fin.last n))
    · change (∑ j, A i.castSucc j * Fin.lastCases z v j) = c i.castSucc
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.lastCases_castSucc, Fin.lastCases_last]
      have h := congrFun hv i
      change (∑ j, A i.castSucc j.castSucc * v j) =
        c i.castSucc - A i.castSucc (Fin.last n) * z at h
      rw [h, sub_add_cancel]

end AEGIS.CvSTriangularTransportV1

#check @AEGIS.CvSTriangularTransportV1.upper_triangular_surjective
#print axioms AEGIS.CvSTriangularTransportV1.upper_triangular_surjective
