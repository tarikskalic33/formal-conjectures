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

import RHKreinThirdCellCompositionV1

/-!
# Compose the existing zero jet into the fourth serialized cell

The positive-endpoint digamma certificate proved for the third cell exposes a
symbol floor valid at every later nonnegative frequency.  This module reuses
that theorem, the eight zero-jet enclosures, and the original M8 bound.  Exact
rational arithmetic leaves a small but strictly positive combined budget.
-/

open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

namespace AEGIS.RHKreinFourthCellCompositionV1

open AEGIS.RHKreinFirstCellV1
open AEGIS.RHKreinSecondCellCompositionV1
open AEGIS.RHKreinThirdCellCompositionV1
open AEGIS.RHKreinCellAnalyticBridgeV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1
open AEGIS.RHKreinFiniteCertificateDataV1
open AEGIS.RHKreinM8AnalyticV1
open AEGIS.RHKreinM8CertificateV1
open AEGIS.RHKreinPrimeSymbolV1

/-- The literal fourth entry of the unchanged committed payload. -/
def fourthCell : FiniteCellV1 :=
  ⟨525 / 16384, 75 / 2048, 253868912037845735⟩

private def reuseRadius : ℝ := 75 / 2048
private def symbolFloor : ℝ := -1269 / 200
private def weightedCoefficient : ℝ :=
  symbolFloor - 1 / 16 - (lowerValue fourthCell : ℝ)
private def reuseError : ℝ :=
  (serializedM8Q : ℝ) * reuseRadius ^ 8 / 40320 +
    ∑ k ∈ Finset.range 8, firstJetError k * reuseRadius ^ k
private def weightedFloor (t : ℝ) : ℝ :=
  (t ^ 2 + 1 / 4) ^ 2 * weightedCoefficient +
    jetPolynomial7 firstJet firstCenter t - reuseError

private theorem weightedFloor_expansion (t : ℝ) :
    weightedFloor t =
      (firstJet 0 + weightedCoefficient / 16 - reuseError) +
      (firstJet 2 + weightedCoefficient / 2) * t ^ 2 +
      (firstJet 4 + weightedCoefficient) * t ^ 4 + firstJet 6 * t ^ 6 := by
  norm_num [weightedFloor, jetPolynomial7, firstCenter,
    Finset.sum_range_succ, firstJet]
  ring

private theorem endpoint_budget : (1 / 100000 : ℝ) < weightedFloor reuseRadius := by
  norm_num [weightedFloor, reuseRadius, weightedCoefficient, symbolFloor,
    fourthCell, lowerValue, jetPolynomial7, firstJet, firstCenter,
    reuseError, firstJetError, serializedM8Q, Finset.sum_range_succ]

private theorem weightedFloor_lower (t : ℝ) (ht0 : 0 ≤ t)
    (htr : t ≤ reuseRadius) : weightedFloor reuseRadius ≤ weightedFloor t := by
  have h2 := mul_le_mul_of_nonpos_left (pow_le_pow_left₀ ht0 htr 2)
    (show firstJet 2 + weightedCoefficient / 2 ≤ 0 by
      norm_num [firstJet, weightedCoefficient, symbolFloor, fourthCell, lowerValue])
  have h4 := mul_le_mul_of_nonpos_left (pow_le_pow_left₀ ht0 htr 4)
    (show firstJet 4 + weightedCoefficient ≤ 0 by
      norm_num [firstJet, weightedCoefficient, symbolFloor, fourthCell, lowerValue])
  have h6 := mul_le_mul_of_nonpos_left (pow_le_pow_left₀ ht0 htr 6)
    (show firstJet 6 ≤ 0 by norm_num [firstJet])
  simp only [weightedFloor_expansion]
  linarith only [h2, h4, h6]

/-- The unchanged fourth serialized lower bound follows entirely by composing
the existing zero jet, M8 bound, and third-endpoint symbol certificate. -/
theorem fourthCell_sound_from_existing_zero_jet : CellAnalyticSoundV1 fourthCell := by
  apply cellAnalyticSound_of_correction_lower fourthCell
    (fun t => jetPolynomial7 firstJet firstCenter t - reuseError)
  · intro t hlo hhi
    have ht0 : 0 ≤ t := by norm_num [fourthCell] at hlo; linarith
    have htr : t ≤ reuseRadius := by simpa [fourthCell, reuseRadius] using hhi
    have hcover : |t - firstCenter| ≤ reuseRadius := by
      rw [firstCenter, sub_zero, abs_of_nonneg ht0]
      exact htr
    exact correction_lower_of_jet_enclosures firstCenter t reuseRadius
      (jetPolynomial7 firstJet firstCenter t) firstJet firstJetError
      (by norm_num [reuseRadius]) hcover existing_zero_jet_enclosures le_rfl
  · intro t hlo hhi
    have ht0 : 0 ≤ t := by norm_num [fourthCell] at hlo; linarith
    have htr : t ≤ reuseRadius := by simpa [fourthCell, reuseRadius] using hhi
    have hgap : 0 ≤ weightedFloor t :=
      ((by norm_num : (0 : ℝ) ≤ 1 / 100000).trans endpoint_budget.le).trans
        (weightedFloor_lower t ht0 htr)
    have hs : symbolFloor ≤ symbol t := by
      apply symbol_lower_of_thirdLeft_le
      norm_num [fourthCell] at hlo ⊢
      linarith
    have hsmul := mul_le_mul_of_nonneg_left
      (sub_le_sub_right hs (1 / 16)) (sq_nonneg (t ^ 2 + 1 / 4))
    calc
      (t ^ 2 + 1 / 4) ^ 2 * (lowerValue fourthCell : ℝ) ≤
          (t ^ 2 + 1 / 4) ^ 2 * (symbolFloor - 1 / 16) +
            (jetPolynomial7 firstJet firstCenter t - reuseError) := by
        dsimp only [weightedFloor, weightedCoefficient] at hgap
        nlinarith only [hgap]
      _ ≤ (t ^ 2 + 1 / 4) ^ 2 * (symbol t - 1 / 16) +
          (jetPolynomial7 firstJet firstCenter t - reuseError) := by
        simpa only [add_comm] using
          add_le_add_right hsmul (jetPolynomial7 firstJet firstCenter t - reuseError)

/-- The first four unchanged serialized cell results compose as a tuple. -/
theorem first_four_cells_sound :
    CellAnalyticSoundV1 firstCell ∧
      CellAnalyticSoundV1 AEGIS.RHKreinSecondCellReductionV1.secondCell ∧
      CellAnalyticSoundV1 thirdCell ∧ CellAnalyticSoundV1 fourthCell :=
  ⟨firstCell_sound_of_jet_enclosures,
    secondCell_sound_from_existing_zero_jet,
    thirdCell_sound_from_existing_zero_jet,
    fourthCell_sound_from_existing_zero_jet⟩

end AEGIS.RHKreinFourthCellCompositionV1

#print axioms AEGIS.RHKreinFourthCellCompositionV1.fourthCell_sound_from_existing_zero_jet
#print axioms AEGIS.RHKreinFourthCellCompositionV1.first_four_cells_sound
