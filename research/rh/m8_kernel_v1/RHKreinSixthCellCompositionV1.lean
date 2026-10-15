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

import RHKreinFifthCellCompositionV1
import RHKreinSixthCellReductionV1
import research.rh.finite_m8_v1.RHKreinM8FiniteWindowV1

/-!
# Compose the existing zero jet into the sixth serialized cell

The finite-window eighth-derivative theorem from PR54 is stated for the same
`correctionSymbol` and uses the same Lean and Mathlib pins as PR53.  Its exact
bound on `|t| ≤ 300` is strong enough to reuse the already proved zero-centered
jet through the sixth cell.  Thus no new midpoint-jet assumptions are needed.
-/

open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section

namespace AEGIS.RHKreinSixthCellCompositionV1

open AEGIS.RHKreinCellAnalyticBridgeV1
open AEGIS.RHKreinCorrectionM8BoundV1
open AEGIS.RHKreinExplicitCorrectionV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1
open AEGIS.RHKreinFiniteCertificateDataV1
open AEGIS.RHKreinFiniteIntervalKernelV1
open AEGIS.RHKreinFirstCellV1
open AEGIS.RHKreinFifthCellCompositionV1
open AEGIS.RHKreinM8AnalyticV1
open AEGIS.RHKreinM8FiniteWindowV1
open AEGIS.RHKreinPrimeSymbolV1
open AEGIS.RHKreinSecondCellCompositionV1
open AEGIS.RHKreinSixthCellReductionV1

private def finiteM8Q : ℝ :=
  138411104278141883145249511099127907904956837 /
    5000000000000000000000000000000000

private def reuseRadius : ℝ := 375 / 8192
private def symbolFloor : ℝ := sixthSymbolLower
private def weightedCoefficient : ℝ :=
  symbolFloor - 1 / 16 - (lowerValue sixthCell : ℝ)
private def reuseError : ℝ :=
  finiteM8Q * reuseRadius ^ 8 / 40320 +
    ∑ k ∈ Finset.range 8, firstJetError k * reuseRadius ^ k
private def weightedFloor (t : ℝ) : ℝ :=
  (t ^ 2 + 1 / 4) ^ 2 * weightedCoefficient +
    jetPolynomial7 firstJet firstCenter t - reuseError

/-- The PR54 finite-window bound gives a local Taylor remainder on `[0, x]`.
The proof consumes the actual intermediate point returned by Lagrange's theorem,
so it does not strengthen the finite-window theorem to a global claim. -/
theorem correction_taylor7_remainder_window300 (x : ℝ)
    (hx0 : 0 ≤ x) (hx300 : x ≤ 300) :
    |correctionSymbol x - centeredTaylorEval correctionSymbol 7 0 x| ≤
      finiteM8Q * |x| ^ 8 / 40320 := by
  by_cases h0x : (0 : ℝ) = x
  · subst x
    rw [centeredTaylorEval_self correctionSymbol 7 0
      (correctionSymbol_contDiff_eight.contDiffAt.of_le (by norm_num))]
    simp
  · obtain ⟨y, hy, hrem⟩ :=
      taylor_mean_remainder_lagrange_iteratedDeriv
        (f := correctionSymbol) (x := x) (x₀ := 0) (n := 7)
        h0x correctionSymbol_contDiff_eight.contDiffOn
    have htaylor :
        taylorWithinEval correctionSymbol 7 (Set.uIcc 0 x) 0 x =
          centeredTaylorEval correctionSymbol 7 0 x := by
      apply taylorWithinEval_eq_centeredTaylor
      · exact uniqueDiffOn_uIcc h0x
      · exact Set.left_mem_uIcc
      · exact correctionSymbol_contDiff_eight.contDiffAt.of_le (by norm_num)
    have hyIoo : y ∈ Set.Ioo (0 : ℝ) x := by
      simpa only [Set.uIoo_of_le hx0] using hy
    have hyIcc : y ∈ Set.Icc (0 : ℝ) x := ⟨hyIoo.1.le, hyIoo.2.le⟩
    have hy300 : |y| ≤ (300 : ℝ) := by
      rw [abs_of_nonneg hyIcc.1]
      exact hyIcc.2.trans hx300
    have hMy : |iteratedDeriv 8 correctionSymbol y| ≤ finiteM8Q := by
      simpa only [finiteM8Q] using correctionSymbol_eighth_le_window300 y hy300
    rw [← htaylor, hrem, abs_div, abs_mul, abs_pow]
    have hM0 : 0 ≤ finiteM8Q := by norm_num [finiteM8Q]
    have hpow : 0 ≤ |x| ^ 8 := pow_nonneg (abs_nonneg _) _
    norm_num
    exact div_le_div_of_nonneg_right
      (mul_le_mul hMy le_rfl hpow hM0) (by norm_num)

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

private theorem endpoint_budget : (9 / 10000 : ℝ) < weightedFloor reuseRadius := by
  norm_num [weightedFloor, reuseRadius, weightedCoefficient, symbolFloor,
    sixthCell, sixthSymbolLower, lowerValue, jetPolynomial7, firstJet, firstCenter,
    reuseError, finiteM8Q, firstJetError, Finset.sum_range_succ]

private theorem weightedFloor_lower (t : ℝ) (ht0 : 0 ≤ t)
    (htr : t ≤ reuseRadius) : weightedFloor reuseRadius ≤ weightedFloor t := by
  have h2 := mul_le_mul_of_nonpos_left (pow_le_pow_left₀ ht0 htr 2)
    (show firstJet 2 + weightedCoefficient / 2 ≤ 0 by
      norm_num [firstJet, weightedCoefficient, symbolFloor, sixthCell,
        sixthSymbolLower, lowerValue])
  have h4 := mul_le_mul_of_nonpos_left (pow_le_pow_left₀ ht0 htr 4)
    (show firstJet 4 + weightedCoefficient ≤ 0 by
      norm_num [firstJet, weightedCoefficient, symbolFloor, sixthCell,
        sixthSymbolLower, lowerValue])
  have h6 := mul_le_mul_of_nonpos_left (pow_le_pow_left₀ ht0 htr 6)
    (show firstJet 6 ≤ 0 by norm_num [firstJet])
  simp only [weightedFloor_expansion]
  linarith only [h2, h4, h6]

/-- The sixth serialized lower bound follows from the existing zero jet and the
PR54 finite-window M8 theorem, with no new jet enclosure assumptions. -/
theorem sixthCell_sound_from_existing_zero_jet : CellAnalyticSoundV1 sixthCell := by
  apply cellAnalyticSound_of_correction_lower sixthCell
    (fun t => jetPolynomial7 firstJet firstCenter t - reuseError)
  · intro t hlo hhi
    have ht0 : 0 ≤ t := by norm_num [sixthCell] at hlo; linarith
    have htr : t ≤ reuseRadius := by simpa [sixthCell, reuseRadius] using hhi
    exact correction_lower_from_existing_zero_jet t ht0 htr
  · intro t hlo hhi
    have ht0 : 0 ≤ t := by norm_num [sixthCell] at hlo; linarith
    have htr : t ≤ reuseRadius := by simpa [sixthCell, reuseRadius] using hhi
    have hgap : 0 ≤ weightedFloor t :=
      ((by norm_num : (0 : ℝ) ≤ 9 / 10000).trans endpoint_budget.le).trans
        (weightedFloor_lower t ht0 htr)
    have hs : symbolFloor ≤ symbol t := sixthCell_symbol_lower t hlo hhi
    have hsmul := mul_le_mul_of_nonneg_left
      (sub_le_sub_right hs (1 / 16)) (sq_nonneg (t ^ 2 + 1 / 4))
    calc
      (t ^ 2 + 1 / 4) ^ 2 * (lowerValue sixthCell : ℝ) ≤
          (t ^ 2 + 1 / 4) ^ 2 * (symbolFloor - 1 / 16) +
            (jetPolynomial7 firstJet firstCenter t - reuseError) := by
        dsimp only [weightedFloor, weightedCoefficient] at hgap
        nlinarith only [hgap]
      _ ≤ (t ^ 2 + 1 / 4) ^ 2 * (symbol t - 1 / 16) +
          (jetPolynomial7 firstJet firstCenter t - reuseError) := by
        simpa only [add_comm] using
          add_le_add_right hsmul (jetPolynomial7 firstJet firstCenter t - reuseError)

/-- The first six unchanged serialized cell results compose as a tuple. -/
theorem first_six_cells_sound :
    CellAnalyticSoundV1 firstCell ∧
      CellAnalyticSoundV1 AEGIS.RHKreinSecondCellReductionV1.secondCell ∧
      CellAnalyticSoundV1 AEGIS.RHKreinThirdCellCompositionV1.thirdCell ∧
      CellAnalyticSoundV1 AEGIS.RHKreinFourthCellCompositionV1.fourthCell ∧
      CellAnalyticSoundV1 AEGIS.RHKreinFifthCellCompositionV1.fifthCell ∧
      CellAnalyticSoundV1 sixthCell :=
  ⟨first_five_cells_sound.1, first_five_cells_sound.2.1,
    first_five_cells_sound.2.2.1, first_five_cells_sound.2.2.2.1,
    first_five_cells_sound.2.2.2.2, sixthCell_sound_from_existing_zero_jet⟩

end AEGIS.RHKreinSixthCellCompositionV1

#print axioms AEGIS.RHKreinSixthCellCompositionV1.sixthCell_sound_from_existing_zero_jet
#print axioms AEGIS.RHKreinSixthCellCompositionV1.first_six_cells_sound
