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

import RHKreinFourthCellCompositionV1

/-!
# Compose the existing zero jet into the fifth serialized cell

The symbol floor inherited from the third endpoint is a measured negative
control here.  Re-anchoring the already proved digamma certificate at
`75/2048` and extending the finite sum from 16 to 24 terms gives the stronger
uniform symbol floor `-1267/200`.  The zero jet and M8 bound are unchanged.
-/

open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace AEGIS.RHKreinFifthCellCompositionV1

open AEGIS.RHKreinDigammaLowerBoundV1
open AEGIS.RHKreinDigammaMonotonicityV1
open AEGIS.RHKreinFirstCellV1
open AEGIS.RHKreinSecondCellCompositionV1
open AEGIS.RHKreinThirdCellCompositionV1
open AEGIS.RHKreinFourthCellCompositionV1
open AEGIS.RHKreinCellAnalyticBridgeV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1
open AEGIS.RHKreinFiniteCertificateDataV1
open AEGIS.RHKreinFiniteIntervalKernelV1
open AEGIS.RHKreinM8AnalyticV1
open AEGIS.RHKreinM8CertificateV1
open AEGIS.RHKreinPrimeSymbolV1
open AEGIS.RHKreinSymbolIntegrationV1

/-- The literal fifth entry of the unchanged committed payload. -/
def fifthCell : FiniteCellV1 :=
  ⟨75 / 2048, 675 / 16384, 219222047756099148⟩

private def fifthLeft : ℝ := 75 / 2048

private theorem fifthDigammaPartialLower :
    (-719517262047183 / 200000000000000 : ℝ) ≤
      ∑ n ∈ Finset.range 24, quarterTerm fifthLeft n := by
  have h0 : (-3536418012511957 / 1000000000000000 : ℝ) ≤
      ∑ n ∈ Finset.range 8, quarterTerm fifthLeft n := by
    norm_num [fifthLeft, quarterTerm]
  have h1 : (-45749699273267 / 1000000000000000 : ℝ) ≤
      ∑ n ∈ Finset.Ico 8 16, quarterTerm fifthLeft n := by
    rw [Finset.sum_Ico_eq_sum_range]
    norm_num [fifthLeft, quarterTerm]
  have h2 : (-15418598450691 / 1000000000000000 : ℝ) ≤
      ∑ n ∈ Finset.Ico 16 24, quarterTerm fifthLeft n := by
    rw [Finset.sum_Ico_eq_sum_range]
    norm_num [fifthLeft, quarterTerm]
  rw [← Finset.sum_range_add_sum_Ico (quarterTerm fifthLeft)
      (show 16 ≤ 24 by norm_num),
    ← Finset.sum_range_add_sum_Ico (quarterTerm fifthLeft)
      (show 8 ≤ 16 by norm_num)]
  linarith only [h0, h1, h2]

private theorem fifthDigammaLower (t : ℝ) (hst : fifthLeft ^ 2 ≤ t ^ 2) :
    (-421 / 100 : ℝ) ≤
      (Complex.digamma ((1 / 4 : ℂ) + (t : ℂ) * Complex.I / 2)).re := by
  have hcert := digamma_quarter_certificate_lower_of_sq_le fifthLeft t 24 hst
  have hpartial := fifthDigammaPartialLower
  norm_num [fifthLeft] at hcert ⊢
  have hpartial' : (-719517262047183 / 200000000000000 : ℝ) ≤
      ∑ n ∈ Finset.range 24, quarterTerm (75 / 2048) n := by
    simpa [fifthLeft] using hpartial
  linarith only [hcert, hpartial']

private theorem fifthLogPiUpper :
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
  have hsquare : (p - e) ^ 2 ≤ (Real.exp x) ^ 2 := by
    nlinarith
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

private theorem fifthPrimeAmplitudeUpper :
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

/-- The stronger exact symbol floor needed by the fifth cell. -/
theorem fifthCell_symbol_lower (t : ℝ)
    (hlo : (fifthCell.lo : ℝ) ≤ t) (_hhi : t ≤ (fifthCell.hi : ℝ)) :
    (-1267 / 200 : ℝ) ≤ symbol t := by
  have ht0 : 0 ≤ t := by norm_num [fifthCell] at hlo; linarith
  have hst : fifthLeft ^ 2 ≤ t ^ 2 := by
    have hleft : fifthLeft ≤ t := by simpa [fifthCell, fifthLeft] using hlo
    have hleft0 : 0 ≤ fifthLeft := by norm_num [fifthLeft]
    nlinarith [mul_nonneg (sub_nonneg.mpr hleft) (add_nonneg ht0 hleft0)]
  have hd := fifthDigammaLower t hst
  have hlp := fifthLogPiUpper
  have hamp := fifthPrimeAmplitudeUpper
  have hamp0 : 0 ≤ Real.sqrt 2 * Real.log 2 :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg (by norm_num))
  have hcos := mul_le_mul_of_nonneg_left (Real.cos_le_one (t * Real.log 2)) hamp0
  unfold symbol archSymbol
  norm_num at hd hlp hamp ⊢
  linarith only [hd, hlp, hamp, hcos]

private def reuseRadius : ℝ := 675 / 16384
private def symbolFloor : ℝ := -1267 / 200
private def weightedCoefficient : ℝ :=
  symbolFloor - 1 / 16 - (lowerValue fifthCell : ℝ)
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

private theorem endpoint_budget : (1 / 1000000 : ℝ) < weightedFloor reuseRadius := by
  norm_num [weightedFloor, reuseRadius, weightedCoefficient, symbolFloor,
    fifthCell, lowerValue, jetPolynomial7, firstJet, firstCenter,
    reuseError, firstJetError, serializedM8Q, Finset.sum_range_succ]

private theorem weightedFloor_lower (t : ℝ) (ht0 : 0 ≤ t)
    (htr : t ≤ reuseRadius) : weightedFloor reuseRadius ≤ weightedFloor t := by
  have h2 := mul_le_mul_of_nonpos_left (pow_le_pow_left₀ ht0 htr 2)
    (show firstJet 2 + weightedCoefficient / 2 ≤ 0 by
      norm_num [firstJet, weightedCoefficient, symbolFloor, fifthCell, lowerValue])
  have h4 := mul_le_mul_of_nonpos_left (pow_le_pow_left₀ ht0 htr 4)
    (show firstJet 4 + weightedCoefficient ≤ 0 by
      norm_num [firstJet, weightedCoefficient, symbolFloor, fifthCell, lowerValue])
  have h6 := mul_le_mul_of_nonpos_left (pow_le_pow_left₀ ht0 htr 6)
    (show firstJet 6 ≤ 0 by norm_num [firstJet])
  simp only [weightedFloor_expansion]
  linarith only [h2, h4, h6]

/-- The fifth serialized lower bound follows from the existing zero jet, M8
bound, and the positive-left-endpoint symbol certificate above. -/
theorem fifthCell_sound_from_existing_zero_jet : CellAnalyticSoundV1 fifthCell := by
  apply cellAnalyticSound_of_correction_lower fifthCell
    (fun t => jetPolynomial7 firstJet firstCenter t - reuseError)
  · intro t hlo hhi
    have ht0 : 0 ≤ t := by norm_num [fifthCell] at hlo; linarith
    have htr : t ≤ reuseRadius := by simpa [fifthCell, reuseRadius] using hhi
    have hcover : |t - firstCenter| ≤ reuseRadius := by
      rw [firstCenter, sub_zero, abs_of_nonneg ht0]
      exact htr
    exact correction_lower_of_jet_enclosures firstCenter t reuseRadius
      (jetPolynomial7 firstJet firstCenter t) firstJet firstJetError
      (by norm_num [reuseRadius]) hcover existing_zero_jet_enclosures le_rfl
  · intro t hlo hhi
    have ht0 : 0 ≤ t := by norm_num [fifthCell] at hlo; linarith
    have htr : t ≤ reuseRadius := by simpa [fifthCell, reuseRadius] using hhi
    have hgap : 0 ≤ weightedFloor t :=
      ((by norm_num : (0 : ℝ) ≤ 1 / 1000000).trans endpoint_budget.le).trans
        (weightedFloor_lower t ht0 htr)
    have hs : symbolFloor ≤ symbol t := fifthCell_symbol_lower t hlo hhi
    have hsmul := mul_le_mul_of_nonneg_left
      (sub_le_sub_right hs (1 / 16)) (sq_nonneg (t ^ 2 + 1 / 4))
    calc
      (t ^ 2 + 1 / 4) ^ 2 * (lowerValue fifthCell : ℝ) ≤
          (t ^ 2 + 1 / 4) ^ 2 * (symbolFloor - 1 / 16) +
            (jetPolynomial7 firstJet firstCenter t - reuseError) := by
        dsimp only [weightedFloor, weightedCoefficient] at hgap
        nlinarith only [hgap]
      _ ≤ (t ^ 2 + 1 / 4) ^ 2 * (symbol t - 1 / 16) +
          (jetPolynomial7 firstJet firstCenter t - reuseError) := by
        simpa only [add_comm] using
          add_le_add_right hsmul (jetPolynomial7 firstJet firstCenter t - reuseError)

/-- The first five unchanged serialized cell results compose as a tuple. -/
theorem first_five_cells_sound :
    CellAnalyticSoundV1 firstCell ∧
      CellAnalyticSoundV1 AEGIS.RHKreinSecondCellReductionV1.secondCell ∧
      CellAnalyticSoundV1 thirdCell ∧ CellAnalyticSoundV1 fourthCell ∧
      CellAnalyticSoundV1 fifthCell :=
  ⟨firstCell_sound_of_jet_enclosures,
    secondCell_sound_from_existing_zero_jet,
    thirdCell_sound_from_existing_zero_jet,
    fourthCell_sound_from_existing_zero_jet,
    fifthCell_sound_from_existing_zero_jet⟩

end AEGIS.RHKreinFifthCellCompositionV1

#print axioms AEGIS.RHKreinFifthCellCompositionV1.fifthCell_symbol_lower
#print axioms AEGIS.RHKreinFifthCellCompositionV1.fifthCell_sound_from_existing_zero_jet
#print axioms AEGIS.RHKreinFifthCellCompositionV1.first_five_cells_sound
