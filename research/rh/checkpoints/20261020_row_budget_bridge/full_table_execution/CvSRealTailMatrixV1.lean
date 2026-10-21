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
/- Real congruence form of the existing epsilon=1, T=13 Gram-tail majorant. -/
import CvSRowBudgetGramBridgeV1
namespace AEGIS.CvSRealTailMatrixV1
open scoped BigOperators
noncomputable def realCongruence {n r : ℕ} (x : Fin r → Fin n → ℝ)
    (g : Fin r → Fin r → ℝ) (i j : Fin n) : ℝ :=
  ∑ k, ∑ l, x k i * x l j * g k l

theorem realCongruence_symm {n r : ℕ} (x : Fin r → Fin n → ℝ)
    (g : Fin r → Fin r → ℝ) (hg : ∀ k l, g k l = g l k) (i j : Fin n) :
    realCongruence x g i j = realCongruence x g j i := by
  unfold realCongruence
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  rw [hg l k]
  ring

noncomputable def tailMatrix (x : Fin 141 → Fin 139 → ℝ)
    (g : Fin 141 → Fin 141 → ℝ) (t : Fin 141 → ℝ) (lp2 : ℝ)
    (i j : Fin 139) : ℝ :=
  lp2 * (2 * realCongruence (fun k i => t k * x k i) g i j +
    338 * realCongruence x g i j)

theorem tailMatrix_symm (x : Fin 141 → Fin 139 → ℝ)
    (g : Fin 141 → Fin 141 → ℝ) (t : Fin 141 → ℝ) (lp2 : ℝ)
    (hg : ∀ k l, g k l = g l k) (i j : Fin 139) :
    tailMatrix x g t lp2 i j = tailMatrix x g t lp2 j i := by
  unfold tailMatrix
  rw [realCongruence_symm _ g hg i j, realCongruence_symm x g hg i j]
end AEGIS.CvSRealTailMatrixV1
#print axioms AEGIS.CvSRealTailMatrixV1.realCongruence_symm
#print axioms AEGIS.CvSRealTailMatrixV1.tailMatrix_symm
