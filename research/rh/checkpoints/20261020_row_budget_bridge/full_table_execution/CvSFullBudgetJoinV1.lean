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
/- Complete finite table and original positive interval certificate, composed without an output-check premise. -/
import CvSFullTableClosureV1
import CvSRealTailMatrixV1
import CvSStrictRowBudgetV1
open scoped BigOperators ComplexConjugate
namespace AEGIS.CvSFullBudgetJoinV1
open AEGIS.RHFixIntervalV1 AEGIS.CvSFullTableClosureV1
open AEGIS.CvSCachedEnvelopeJoinV1 AEGIS.CvSRealTailMatrixV1
open AEGIS.CvSRowBudgetGramBridgeV1
open AEGIS.RowBudgetListCell0Pilot AEGIS.RowBudgetStagedDotPilot

/-- Full finite arithmetic has been discharged. The six remaining memberships
state exactly which real matrix is certified; they are not numerical assumptions. -/
theorem budgetEnergy_le_of_inputs
    (q : Fin 139 → Fin 139 → ℝ) (x : Fin 141 → Fin 139 → ℝ)
    (g : Fin 141 → Fin 141 → ℝ) (t : Fin 141 → ℝ)
    (z : Fin 301 → Fin 139 → ℝ) (lp2 : ℝ)
    (hq : ∀ i j, q i j = q j i) (hg : ∀ k l, g k l = g l k)
    (hQ : ∀ i j, (Q i j).Mem 96 (q i j))
    (hX : ∀ k i, (coeff columns k i).Mem 96 (x k i))
    (hG : ∀ k l : Fin 141, ((G.getD k.val []).getD l.val ⟨0, 0⟩).Mem 96 (g k l))
    (hT : ∀ k : Fin 141, (T.getD k.val ⟨0, 0⟩).Mem 96 (t k))
    (hZ : ∀ r i, (residual columns r i).Mem 96 (z r i))
    (hLP : LP2.Mem 96 lp2) :
    ∀ v : Fin 139 → ℂ, budgetEnergy z (tailMatrix x g t lp2) v ≤
      40 * (∑ i, ∑ j, v i * conj (v j) * (q i j : ℂ)).re := by
  apply budgetEnergy_le_of_Iv q z (tailMatrix x g t lp2) hq
    (tailMatrix_symm x g t lp2 hg)
  intro i j
  have h := real_envelope_mem q x g t z lp2 hQ hX hG hT hZ hLP i j
  simpa only [AEGIS.CvSFullTableClosureV1.target, budgetMatrix, tailMatrix, realCongruence,
    sub_add_eq_sub_sub] using h
/-- Full finite arithmetic has been discharged. The six remaining memberships
state exactly which real matrix is certified; they are not numerical assumptions. -/
theorem budgetEnergy_margin_le_of_inputs
    (q : Fin 139 → Fin 139 → ℝ) (x : Fin 141 → Fin 139 → ℝ)
    (g : Fin 141 → Fin 141 → ℝ) (t : Fin 141 → ℝ)
    (z : Fin 301 → Fin 139 → ℝ) (lp2 : ℝ)
    (hq : ∀ i j, q i j = q j i) (hg : ∀ k l, g k l = g l k)
    (hQ : ∀ i j, (Q i j).Mem 96 (q i j))
    (hX : ∀ k i, (coeff columns k i).Mem 96 (x k i))
    (hG : ∀ k l : Fin 141, ((G.getD k.val []).getD l.val ⟨0, 0⟩).Mem 96 (g k l))
    (hT : ∀ k : Fin 141, (T.getD k.val ⟨0, 0⟩).Mem 96 (t k))
    (hZ : ∀ r i, (residual columns r i).Mem 96 (z r i))
    (hLP : LP2.Mem 96 lp2) :
    ∀ v : Fin 139 → ℂ, AEGIS.CvSStrictRowBudgetV1.margin * (∑ i, ‖v i‖ ^ 2) + budgetEnergy z (tailMatrix x g t lp2) v ≤
      40 * (∑ i, ∑ j, v i * conj (v j) * (q i j : ℂ)).re := by
  intro v
  apply AEGIS.CvSStrictRowBudgetV1.budgetEnergy_margin_of_Iv q z (tailMatrix x g t lp2) hq
    (tailMatrix_symm x g t lp2 hg) ?_ v
  intro i j
  have h := real_envelope_mem q x g t z lp2 hQ hX hG hT hZ hLP i j
  simpa only [AEGIS.CvSFullTableClosureV1.target, budgetMatrix, tailMatrix, realCongruence,
    sub_add_eq_sub_sub] using h
end AEGIS.CvSFullBudgetJoinV1
#check @AEGIS.CvSFullBudgetJoinV1.budgetEnergy_le_of_inputs
#print axioms AEGIS.CvSFullBudgetJoinV1.budgetEnergy_le_of_inputs
#check @AEGIS.CvSFullBudgetJoinV1.budgetEnergy_margin_le_of_inputs
#print axioms AEGIS.CvSFullBudgetJoinV1.budgetEnergy_margin_le_of_inputs
