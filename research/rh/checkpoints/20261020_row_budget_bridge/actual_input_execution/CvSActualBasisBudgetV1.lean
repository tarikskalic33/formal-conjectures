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
/- Consumer-facing actual budget in the existing transformed and original atom coordinates.
Candidate until its original-import replay succeeds. -/
import CvSActualLiteralInputsV1
open scoped BigOperators ComplexConjugate
namespace AEGIS.CvSActualBasisBudgetV1
open AEGIS.CvSProjectedPackedCertificateL12V1 AEGIS.CvSProjectedSchurBridgeL12V1
open AEGIS.CvSSchurClosureFromBoundsV1 AEGIS.CvSSourceProductAllV1

noncomputable def actualBudget (M : ℕ) (v : Fin 139 → ℂ) : ℝ :=
  AEGIS.CvSRowBudgetGramBridgeV1.budgetEnergy (AEGIS.CvSActualRowInputL12V1.sourceZ M lambdaReal)
    (AEGIS.CvSRealTailMatrixV1.tailMatrix transformedCoeff
      (fun k l => AEGIS.CvSGramTailV1.gramUp 150 (signedFreq k) (signedFreq l))
      (fun k => AEGIS.CvSRowTailV1.tau M (6/5) (signedFreq k)) (((6/5 : ℝ)/Real.pi)^2)) v

theorem actualBudget_le_projected (M : ℕ) (hM : 3 ≤ M) (v : Fin 139 → ℂ) :
    actualBudget M v ≤ 40 * projectedQ M v := by
  have h := AEGIS.CvSActualLiteralInputsV1.actual_budgetEnergy_margin M hM v
  have hn : 0 ≤ AEGIS.CvSStrictRowBudgetV1.margin * (∑ i, ‖v i‖^2) :=
    mul_nonneg AEGIS.CvSStrictRowBudgetV1.margin_positive.le
      (Finset.sum_nonneg (fun i _ => sq_nonneg ‖v i‖))
  change AEGIS.CvSStrictRowBudgetV1.margin * (∑ i, ‖v i‖^2) + actualBudget M v ≤
    40 * projectedQ M v at h
  linarith

/-- The actual finite row budget composed with the already-proved exact transport. -/
theorem actualBudget_le_original (M : ℕ) (hM : 3 ≤ M) (v : Fin 139 → ℂ) :
    actualBudget M v ≤ 40 * Q_CvS M (6/5) atomCenter (R_basis v) := by
  have h := actualBudget_le_projected M hM v
  rw [AEGIS.CvSProjectedTransportL12V1.hTransport M v] at h
  exact h
end AEGIS.CvSActualBasisBudgetV1
#check @AEGIS.CvSActualBasisBudgetV1.actualBudget_le_projected
#print axioms AEGIS.CvSActualBasisBudgetV1.actualBudget_le_projected
#check @AEGIS.CvSActualBasisBudgetV1.actualBudget_le_original
#print axioms AEGIS.CvSActualBasisBudgetV1.actualBudget_le_original
