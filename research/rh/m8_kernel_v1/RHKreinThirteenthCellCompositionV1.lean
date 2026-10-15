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

import RHKreinTwelfthCellCompositionV1

/-!
# Compose existing analytic components into the thirteenth serialized cell

The inherited twelfth-left symbol floor is too coarse for serialized cell index
12.  Re-anchoring the existing exact digamma producer at the new left endpoint
gives the stronger floor `-3137/500`.  The existing zero jet and exact PR54
finite-window M8 bound then close the cell without new analytic assumptions.
-/

open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section

namespace AEGIS.RHKreinThirteenthCellCompositionV1

open AEGIS.RHEulerGammaSharpV1
open AEGIS.RHKreinCellAnalyticBridgeV1
open AEGIS.RHKreinDigammaLowerBoundV1
open AEGIS.RHKreinDigammaMonotonicityV1
open AEGIS.RHKreinExplicitCorrectionV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1
open AEGIS.RHKreinFiniteCertificateDataV1
open AEGIS.RHKreinFiniteIntervalKernelV1
open AEGIS.RHKreinFirstCellV1
open AEGIS.RHKreinM8AnalyticV1
open AEGIS.RHKreinPrimeSymbolV1
open AEGIS.RHKreinSecondCellCompositionV1
open AEGIS.RHKreinSixthCellCompositionV1
open AEGIS.RHKreinSymbolIntegrationV1
open AEGIS.RHKreinEleventhCellCompositionV1
open AEGIS.RHKreinTenthCellCompositionV1
open AEGIS.RHKreinTwelfthCellCompositionV1

/-- The literal thirteenth entry of the unchanged committed payload. -/
def thirteenthCell : FiniteCellV1 :=
  ⟨2325 / 32768, 75 / 1024, 302493041933652027⟩

private def thirteenthLeft : ℝ := 2325 / 32768
private def thirteenthSymbolLower : ℝ := -3137 / 500

private theorem digamma_sharp_lower_of_sq_le (s t : ℝ) (N : ℕ)
    (hst : s ^ 2 ≤ t ^ 2) :
    -(5773 / 10000 : ℝ) + (∑ n ∈ Finset.range N, quarterTerm s n) -
        (3 / 4 : ℝ) * (1 / ((N : ℝ) + 1 / 4) +
          1 / ((N : ℝ) + 1 / 4) ^ 2) ≤
      (Complex.digamma ((1 / 4 : ℂ) + (t : ℂ) * Complex.I / 2)).re := by
  have hs := digamma_quarter_finite_lower s N
  have hm := digamma_quarter_mono_of_sq_le s t hst
  have hg := gamma_lt_5773
  dsimp [quarterPoint] at hs
  linarith only [hs, hm, hg]

private theorem thirteenthDigammaPartialLower :
    (-3539357825991139 / 1000000000000000 : ℝ) ≤
      ∑ n ∈ Finset.range 24, quarterTerm thirteenthLeft n := by
  have h0 : (-3478196364706334 / 1000000000000000 : ℝ) ≤
      ∑ n ∈ Finset.range 8, quarterTerm thirteenthLeft n := by
    norm_num [thirteenthLeft, quarterTerm]
  have h1 : (-45743903927213 / 1000000000000000 : ℝ) ≤
      ∑ n ∈ Finset.Ico 8 16, quarterTerm thirteenthLeft n := by
    rw [Finset.sum_Ico_eq_sum_range]
    norm_num [thirteenthLeft, quarterTerm]
  have h2 : (-15417557357592 / 1000000000000000 : ℝ) ≤
      ∑ n ∈ Finset.Ico 16 24, quarterTerm thirteenthLeft n := by
    rw [Finset.sum_Ico_eq_sum_range]
    norm_num [thirteenthLeft, quarterTerm]
  rw [← Finset.sum_range_add_sum_Ico (quarterTerm thirteenthLeft)
      (show 16 ≤ 24 by norm_num),
    ← Finset.sum_range_add_sum_Ico (quarterTerm thirteenthLeft)
      (show 8 ≤ 16 by norm_num)]
  linarith only [h0, h1, h2]

private theorem thirteenthDigammaLower (t : ℝ) (hst : thirteenthLeft ^ 2 ≤ t ^ 2) :
    (-4149 / 1000 : ℝ) ≤
      (Complex.digamma ((1 / 4 : ℂ) + (t : ℂ) * Complex.I / 2)).re := by
  have hcert := digamma_sharp_lower_of_sq_le thirteenthLeft t 24 hst
  have hpartial := thirteenthDigammaPartialLower
  norm_num [thirteenthLeft] at hcert ⊢
  have hpartial' : (-3539357825991139 / 1000000000000000 : ℝ) ≤
      ∑ n ∈ Finset.range 24, quarterTerm (2325 / 32768) n := by
    simpa [thirteenthLeft] using hpartial
  linarith only [hcert, hpartial']

private theorem thirteenthLogPiUpper :
    Real.log Real.pi ≤ (1144729886 / 1000000000 : ℝ) := by
  let x : ℝ := (1144729886 / 2000000000 : ℝ)
  let p : ℝ := ∑ m ∈ Finset.range 16, x ^ m / m.factorial
  let e : ℝ := |x| ^ 16 * ((17 : ℝ) / (Nat.factorial 16 * 16))
  have hb := Real.exp_bound (x := x) (n := 16) (by norm_num [x]) (by norm_num)
  have hlo : p - e ≤ Real.exp x := by
    rw [abs_sub_le_iff] at hb
    dsimp [p, e]
    linarith [hb.1]
  have hp : 0 ≤ p - e := by
    norm_num [p, e, x, Finset.sum_range_succ, abs_of_nonneg]
  have hexp : 0 < Real.exp x := Real.exp_pos x
  have hsquare : (p - e) ^ 2 ≤ (Real.exp x) ^ 2 := by nlinarith
  have hpi : Real.pi ≤ (p - e) ^ 2 := by
    have h := Real.pi_lt_d20
    norm_num [p, e, x, Finset.sum_range_succ, abs_of_nonneg] at h ⊢
    linarith
  have hq : Real.exp (1144729886 / 1000000000 : ℝ) = (Real.exp x) ^ 2 := by
    rw [show (1144729886 / 1000000000 : ℝ) = x + x by norm_num [x], Real.exp_add]
    ring
  apply (Real.log_le_iff_le_exp Real.pi_pos).2
  rw [hq]
  exact hpi.trans hsquare

private theorem thirteenthPrimeAmplitudeUpper :
    Real.sqrt 2 * Real.log 2 ≤
      (1414213563 / 1000000000 : ℝ) * (6931471808 / 10000000000 : ℝ) := by
  have hs : Real.sqrt 2 ≤ (1414213563 / 1000000000 : ℝ) := by
    have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hs0 := Real.sqrt_nonneg (2 : ℝ)
    nlinarith
  have hl0 := (log_two_enclosure).2
  have hl : Real.log 2 ≤ (6931471808 / 10000000000 : ℝ) := by
    norm_num at hl0 ⊢
    exact hl0.le
  exact mul_le_mul hs hl (Real.log_nonneg (by norm_num)) (by norm_num)

/-- The new left-endpoint symbol floor remains valid at every later
nonnegative frequency. -/
theorem symbol_lower_of_thirteenthLeft_le (t : ℝ) (hleft : (2325 / 32768 : ℝ) ≤ t) :
    thirteenthSymbolLower ≤ symbol t := by
  have hleft' : thirteenthLeft ≤ t := by simpa [thirteenthLeft] using hleft
  have ht0 : 0 ≤ t := by
    have hleft0 : 0 ≤ thirteenthLeft := by norm_num [thirteenthLeft]
    linarith
  have hst : thirteenthLeft ^ 2 ≤ t ^ 2 := by
    have hleft0 : 0 ≤ thirteenthLeft := by norm_num [thirteenthLeft]
    nlinarith [mul_nonneg (sub_nonneg.mpr hleft') (add_nonneg ht0 hleft0)]
  have hd := thirteenthDigammaLower t hst
  have hlp := thirteenthLogPiUpper
  have hamp := thirteenthPrimeAmplitudeUpper
  have hamp0 : 0 ≤ Real.sqrt 2 * Real.log 2 :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg (by norm_num))
  have hcos := mul_le_mul_of_nonneg_left (Real.cos_le_one (t * Real.log 2)) hamp0
  unfold symbol archSymbol
  norm_num [thirteenthSymbolLower] at hd hlp hamp ⊢
  linarith only [hd, hlp, hamp, hcos]

private def finiteM8Q : ℝ :=
  138411104278141883145249511099127907904956837 /
    5000000000000000000000000000000000

private def reuseRadius : ℝ := 75 / 1024
private def weightedCoefficient : ℝ :=
  thirteenthSymbolLower - 1 / 16 - (lowerValue thirteenthCell : ℝ)
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

private theorem endpoint_budget : (1 / 10000 : ℝ) < weightedFloor reuseRadius := by
  norm_num [weightedFloor, reuseRadius, weightedCoefficient, thirteenthSymbolLower,
    thirteenthCell, lowerValue, jetPolynomial7, firstJet, firstCenter,
    reuseError, finiteM8Q, firstJetError, Finset.sum_range_succ]

private theorem weightedFloor_lower (t : ℝ) (ht0 : 0 ≤ t)
    (htr : t ≤ reuseRadius) : weightedFloor reuseRadius ≤ weightedFloor t := by
  have h2 := mul_le_mul_of_nonpos_left (pow_le_pow_left₀ ht0 htr 2)
    (show firstJet 2 + weightedCoefficient / 2 ≤ 0 by
      norm_num [firstJet, weightedCoefficient, thirteenthSymbolLower,
        thirteenthCell, lowerValue])
  have h4 := mul_le_mul_of_nonpos_left (pow_le_pow_left₀ ht0 htr 4)
    (show firstJet 4 + weightedCoefficient ≤ 0 by
      norm_num [firstJet, weightedCoefficient, thirteenthSymbolLower,
        thirteenthCell, lowerValue])
  have h6 := mul_le_mul_of_nonpos_left (pow_le_pow_left₀ ht0 htr 6)
    (show firstJet 6 ≤ 0 by norm_num [firstJet])
  simp only [weightedFloor_expansion]
  linarith only [h2, h4, h6]

/-- The thirteenth serialized lower bound follows from existing analytic producers. -/
theorem thirteenthCell_sound_from_existing_zero_jet : CellAnalyticSoundV1 thirteenthCell := by
  apply cellAnalyticSound_of_correction_lower thirteenthCell
    (fun t => jetPolynomial7 firstJet firstCenter t - reuseError)
  · intro t hlo hhi
    have ht0 : 0 ≤ t := by norm_num [thirteenthCell] at hlo; linarith
    have htr : t ≤ reuseRadius := by simpa [thirteenthCell, reuseRadius] using hhi
    exact correction_lower_from_existing_zero_jet t ht0 htr
  · intro t hlo hhi
    have ht0 : 0 ≤ t := by norm_num [thirteenthCell] at hlo; linarith
    have htr : t ≤ reuseRadius := by simpa [thirteenthCell, reuseRadius] using hhi
    have hgap : 0 ≤ weightedFloor t :=
      ((by norm_num : (0 : ℝ) ≤ 1 / 10000).trans endpoint_budget.le).trans
        (weightedFloor_lower t ht0 htr)
    have hs : thirteenthSymbolLower ≤ symbol t := by
      apply symbol_lower_of_thirteenthLeft_le
      simpa [thirteenthCell] using hlo
    have hsmul := mul_le_mul_of_nonneg_left
      (sub_le_sub_right hs (1 / 16)) (sq_nonneg (t ^ 2 + 1 / 4))
    calc
      (t ^ 2 + 1 / 4) ^ 2 * (lowerValue thirteenthCell : ℝ) ≤
          (t ^ 2 + 1 / 4) ^ 2 * (thirteenthSymbolLower - 1 / 16) +
            (jetPolynomial7 firstJet firstCenter t - reuseError) := by
        dsimp only [weightedFloor, weightedCoefficient] at hgap
        nlinarith only [hgap]
      _ ≤ (t ^ 2 + 1 / 4) ^ 2 * (symbol t - 1 / 16) +
          (jetPolynomial7 firstJet firstCenter t - reuseError) := by
        simpa only [add_comm] using
          add_le_add_right hsmul (jetPolynomial7 firstJet firstCenter t - reuseError)

/-- The first thirteen unchanged serialized cell results compose as a tuple. -/
theorem first_thirteen_cells_sound :
    CellAnalyticSoundV1 AEGIS.RHKreinFirstCellV1.firstCell ∧
      CellAnalyticSoundV1 AEGIS.RHKreinSecondCellReductionV1.secondCell ∧
      CellAnalyticSoundV1 AEGIS.RHKreinThirdCellCompositionV1.thirdCell ∧
      CellAnalyticSoundV1 AEGIS.RHKreinFourthCellCompositionV1.fourthCell ∧
      CellAnalyticSoundV1 AEGIS.RHKreinFifthCellCompositionV1.fifthCell ∧
      CellAnalyticSoundV1 AEGIS.RHKreinSixthCellReductionV1.sixthCell ∧
      CellAnalyticSoundV1 AEGIS.RHKreinSeventhCellCompositionV1.seventhCell ∧
      CellAnalyticSoundV1 AEGIS.RHKreinEighthCellCompositionV1.eighthCell ∧
      CellAnalyticSoundV1 AEGIS.RHKreinNinthCellCompositionV1.ninthCell ∧
      CellAnalyticSoundV1 AEGIS.RHKreinTenthCellCompositionV1.tenthCell ∧
      CellAnalyticSoundV1 eleventhCell ∧ CellAnalyticSoundV1 twelfthCell ∧
      CellAnalyticSoundV1 thirteenthCell :=
  ⟨first_twelve_cells_sound.1, first_twelve_cells_sound.2.1,
    first_twelve_cells_sound.2.2.1, first_twelve_cells_sound.2.2.2.1,
    first_twelve_cells_sound.2.2.2.2.1, first_twelve_cells_sound.2.2.2.2.2.1,
    first_twelve_cells_sound.2.2.2.2.2.2.1,
    first_twelve_cells_sound.2.2.2.2.2.2.2.1,
    first_twelve_cells_sound.2.2.2.2.2.2.2.2.1,
    first_twelve_cells_sound.2.2.2.2.2.2.2.2.2.1,
    first_twelve_cells_sound.2.2.2.2.2.2.2.2.2.2.1,
    first_twelve_cells_sound.2.2.2.2.2.2.2.2.2.2.2,
    thirteenthCell_sound_from_existing_zero_jet⟩

end AEGIS.RHKreinThirteenthCellCompositionV1

#print axioms AEGIS.RHKreinThirteenthCellCompositionV1.symbol_lower_of_thirteenthLeft_le
#print axioms AEGIS.RHKreinThirteenthCellCompositionV1.thirteenthCell_sound_from_existing_zero_jet
#print axioms AEGIS.RHKreinThirteenthCellCompositionV1.first_thirteen_cells_sound
