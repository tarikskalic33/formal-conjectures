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

import RHKreinSixthCellCompositionV1

/-!
# Compose the existing zero jet into the seventh serialized cell

The sixth-left symbol floor is valid at every later nonnegative frequency.
Together with the existing zero jet and the exact PR54 finite-window M8 bound,
it closes serialized cell index 6 without new analytic assumptions.
-/

open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section

namespace AEGIS.RHKreinSeventhCellCompositionV1

open AEGIS.RHKreinCellAnalyticBridgeV1
open AEGIS.RHKreinExplicitCorrectionV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1
open AEGIS.RHKreinFiniteCertificateDataV1
open AEGIS.RHKreinFiniteIntervalKernelV1
open AEGIS.RHKreinFirstCellV1
open AEGIS.RHKreinM8AnalyticV1
open AEGIS.RHKreinPrimeSymbolV1
open AEGIS.RHKreinSecondCellCompositionV1
open AEGIS.RHKreinSixthCellCompositionV1
open AEGIS.RHKreinSixthCellReductionV1

/-- The literal seventh entry of the unchanged committed payload. -/
def seventhCell : FiniteCellV1 :=
  ⟨375 / 8192, 825 / 16384, 152314342263794501⟩

private def finiteM8Q : ℝ :=
  138411104278141883145249511099127907904956837 /
    5000000000000000000000000000000000

private def reuseRadius : ℝ := 825 / 16384
private def symbolFloor : ℝ := sixthSymbolLower
private def weightedCoefficient : ℝ :=
  symbolFloor - 1 / 16 - (lowerValue seventhCell : ℝ)
private def reuseError : ℝ :=
  finiteM8Q * reuseRadius ^ 8 / 40320 +
    ∑ k ∈ Finset.range 8, firstJetError k * reuseRadius ^ k
private def weightedFloor (t : ℝ) : ℝ :=
  (t ^ 2 + 1 / 4) ^ 2 * weightedCoefficient +
    jetPolynomial7 firstJet firstCenter t - reuseError

private theorem correction_lower_from_existing_zero_jet (t : ℝ)
    (ht0 : 0 ≤ t) (htr : t ≤ reuseRadius) :
    jetPolynomial7 firstJet firstCenter t - reuseError ≤ correctionSymbol t := by
  have ht300 : t ≤ (300 : ℝ) := htr.trans (by norm_num [reuseRadius])
  have hbase := correction_taylor7_remainder_window300 t ht0 ht300
  have hM0 : 0 ≤ finiteM8Q := by norm_num [finiteM8Q]
  have hpow : |t| ^ 8 ≤ reuseRadius ^ 8 := by
    rw [abs_of_nonneg ht0]
    exact pow_le_pow_left₀ ht0 htr 8
  have hrem :
      |correctionSymbol t - centeredTaylorEval correctionSymbol 7 firstCenter t| ≤
        finiteM8Q * reuseRadius ^ 8 / 40320 := by
    rw [firstCenter]
    refine hbase.trans ?_
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow hM0) (by norm_num)
  have hcover : |t - firstCenter| ≤ reuseRadius := by
    rw [firstCenter, sub_zero, abs_of_nonneg ht0]
    exact htr
  have hjet := jetPolynomial7_error firstCenter t reuseRadius
    firstJet firstJetError hcover existing_zero_jet_enclosures
  rw [centeredTaylor_eq_exactJet] at hrem
  rw [abs_le] at hrem hjet
  dsimp only [reuseError]
  linarith only [hrem.1, hjet.1]

private theorem weightedFloor_expansion (t : ℝ) :
    weightedFloor t =
      (firstJet 0 + weightedCoefficient / 16 - reuseError) +
      (firstJet 2 + weightedCoefficient / 2) * t ^ 2 +
      (firstJet 4 + weightedCoefficient) * t ^ 4 + firstJet 6 * t ^ 6 := by
  norm_num [weightedFloor, jetPolynomial7, firstCenter,
    Finset.sum_range_succ, firstJet]
  ring

private theorem endpoint_budget : (1 / 2000 : ℝ) < weightedFloor reuseRadius := by
  norm_num [weightedFloor, reuseRadius, weightedCoefficient, symbolFloor,
    seventhCell, sixthSymbolLower, lowerValue, jetPolynomial7, firstJet, firstCenter,
    reuseError, finiteM8Q, firstJetError, Finset.sum_range_succ]

private theorem weightedFloor_lower (t : ℝ) (ht0 : 0 ≤ t)
    (htr : t ≤ reuseRadius) : weightedFloor reuseRadius ≤ weightedFloor t := by
  have h2 := mul_le_mul_of_nonpos_left (pow_le_pow_left₀ ht0 htr 2)
    (show firstJet 2 + weightedCoefficient / 2 ≤ 0 by
      norm_num [firstJet, weightedCoefficient, symbolFloor, seventhCell,
        sixthSymbolLower, lowerValue])
  have h4 := mul_le_mul_of_nonpos_left (pow_le_pow_left₀ ht0 htr 4)
    (show firstJet 4 + weightedCoefficient ≤ 0 by
      norm_num [firstJet, weightedCoefficient, symbolFloor, seventhCell,
        sixthSymbolLower, lowerValue])
  have h6 := mul_le_mul_of_nonpos_left (pow_le_pow_left₀ ht0 htr 6)
    (show firstJet 6 ≤ 0 by norm_num [firstJet])
  simp only [weightedFloor_expansion]
  linarith only [h2, h4, h6]

/-- The seventh serialized lower bound follows from the already proved zero jet,
finite-window M8 theorem, and sixth-left symbol floor. -/
theorem seventhCell_sound_from_existing_zero_jet : CellAnalyticSoundV1 seventhCell := by
  apply cellAnalyticSound_of_correction_lower seventhCell
    (fun t => jetPolynomial7 firstJet firstCenter t - reuseError)
  · intro t hlo hhi
    have ht0 : 0 ≤ t := by norm_num [seventhCell] at hlo; linarith
    have htr : t ≤ reuseRadius := by simpa [seventhCell, reuseRadius] using hhi
    exact correction_lower_from_existing_zero_jet t ht0 htr
  · intro t hlo hhi
    have ht0 : 0 ≤ t := by norm_num [seventhCell] at hlo; linarith
    have htr : t ≤ reuseRadius := by simpa [seventhCell, reuseRadius] using hhi
    have hgap : 0 ≤ weightedFloor t :=
      ((by norm_num : (0 : ℝ) ≤ 1 / 2000).trans endpoint_budget.le).trans
        (weightedFloor_lower t ht0 htr)
    have hs : symbolFloor ≤ symbol t := by
      dsimp only [symbolFloor]
      apply symbol_lower_of_sixthLeft_le
      norm_num [seventhCell] at hlo ⊢
      linarith
    have hsmul := mul_le_mul_of_nonneg_left
      (sub_le_sub_right hs (1 / 16)) (sq_nonneg (t ^ 2 + 1 / 4))
    calc
      (t ^ 2 + 1 / 4) ^ 2 * (lowerValue seventhCell : ℝ) ≤
          (t ^ 2 + 1 / 4) ^ 2 * (symbolFloor - 1 / 16) +
            (jetPolynomial7 firstJet firstCenter t - reuseError) := by
        dsimp only [weightedFloor, weightedCoefficient] at hgap
        nlinarith only [hgap]
      _ ≤ (t ^ 2 + 1 / 4) ^ 2 * (symbol t - 1 / 16) +
          (jetPolynomial7 firstJet firstCenter t - reuseError) := by
        simpa only [add_comm] using
          add_le_add_right hsmul (jetPolynomial7 firstJet firstCenter t - reuseError)

/-- The first seven unchanged serialized cell results compose as a tuple. -/
theorem first_seven_cells_sound :
    CellAnalyticSoundV1 AEGIS.RHKreinFirstCellV1.firstCell ∧
      CellAnalyticSoundV1 AEGIS.RHKreinSecondCellReductionV1.secondCell ∧
      CellAnalyticSoundV1 AEGIS.RHKreinThirdCellCompositionV1.thirdCell ∧
      CellAnalyticSoundV1 AEGIS.RHKreinFourthCellCompositionV1.fourthCell ∧
      CellAnalyticSoundV1 AEGIS.RHKreinFifthCellCompositionV1.fifthCell ∧
      CellAnalyticSoundV1 sixthCell ∧ CellAnalyticSoundV1 seventhCell :=
  ⟨first_six_cells_sound.1, first_six_cells_sound.2.1,
    first_six_cells_sound.2.2.1, first_six_cells_sound.2.2.2.1,
    first_six_cells_sound.2.2.2.2.1, first_six_cells_sound.2.2.2.2.2,
    seventhCell_sound_from_existing_zero_jet⟩

end AEGIS.RHKreinSeventhCellCompositionV1

#print axioms AEGIS.RHKreinSeventhCellCompositionV1.seventhCell_sound_from_existing_zero_jet
#print axioms AEGIS.RHKreinSeventhCellCompositionV1.first_seven_cells_sound
