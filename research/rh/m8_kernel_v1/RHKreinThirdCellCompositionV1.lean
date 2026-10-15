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

import RHKreinSecondCellCompositionV1

/-!
# Compose the existing zero jet into the third serialized cell

The global zero-frequency symbol floor is just too weak on this cell.  The
proved digamma monotonicity theorem is instead anchored at the cell's positive
left endpoint.  A 16-term exact rational certificate then yields the uniform
symbol floor `-1269/200`.  Together with the existing eight zero-jet
enclosures and original-definition M8 bound, the combined endpoint budget is
strictly positive.
-/

open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace AEGIS.RHKreinThirdCellCompositionV1

open AEGIS.RHKreinDigammaLowerBoundV1
open AEGIS.RHKreinDigammaMonotonicityV1
open AEGIS.RHKreinFirstCellV1
open AEGIS.RHKreinSecondCellCompositionV1
open AEGIS.RHKreinCellAnalyticBridgeV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1
open AEGIS.RHKreinFiniteCertificateDataV1
open AEGIS.RHKreinFiniteIntervalKernelV1
open AEGIS.RHKreinM8AnalyticV1
open AEGIS.RHKreinM8CertificateV1
open AEGIS.RHKreinPrimeSymbolV1
open AEGIS.RHKreinSymbolIntegrationV1

/-- The literal third entry of the unchanged committed payload. -/
def thirdCell : FiniteCellV1 :=
  ⟨225 / 8192, 525 / 16384, 289287866131689861⟩

private def thirdLeft : ℝ := 225 / 8192

private theorem thirdDigammaPartialLower :
    (-3591574317375397 / 1000000000000000 : ℝ) ≤
      ∑ n ∈ Finset.range 16, quarterTerm thirdLeft n := by
  have h0 : (-3545823697412947 / 1000000000000000 : ℝ) ≤
      ∑ n ∈ Finset.range 8, quarterTerm thirdLeft n := by
    norm_num [thirdLeft, quarterTerm]
  have h1 : (-915012399249 / 20000000000000 : ℝ) ≤
      ∑ n ∈ Finset.Ico 8 16, quarterTerm thirdLeft n := by
    rw [Finset.sum_Ico_eq_sum_range]
    norm_num [thirdLeft, quarterTerm]
  rw [← Finset.sum_range_add_sum_Ico (quarterTerm thirdLeft)
    (show 8 ≤ 16 by norm_num)]
  linarith only [h0, h1]

private theorem thirdDigammaLower (t : ℝ) (hst : thirdLeft ^ 2 ≤ t ^ 2) :
    (-211 / 50 : ℝ) ≤
      (Complex.digamma ((1 / 4 : ℂ) + (t : ℂ) * Complex.I / 2)).re := by
  have hcert := digamma_quarter_certificate_lower_of_sq_le thirdLeft t 16 hst
  have hpartial := thirdDigammaPartialLower
  norm_num [thirdLeft] at hcert ⊢
  have hpartial' : (-3591574317375397 / 1000000000000000 : ℝ) ≤
      ∑ n ∈ Finset.range 16, quarterTerm (225 / 8192) n := by
    simpa [thirdLeft] using hpartial
  linarith only [hcert, hpartial']

private theorem thirdLogPiUpper :
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

private theorem thirdPrimeAmplitudeUpper :
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

/-- The third-cell endpoint certificate actually supplies the same symbol
floor at every later nonnegative frequency.  Exposing that stronger type lets
later cells reuse the proof without regenerating the digamma certificate. -/
theorem symbol_lower_of_thirdLeft_le (t : ℝ)
    (hlo : (225 / 8192 : ℝ) ≤ t) :
    (-1269 / 200 : ℝ) ≤ symbol t := by
  have ht0 : 0 ≤ t := by linarith
  have hst : thirdLeft ^ 2 ≤ t ^ 2 := by
    have hleft : thirdLeft ≤ t := by simpa [thirdLeft] using hlo
    have hleft0 : 0 ≤ thirdLeft := by norm_num [thirdLeft]
    nlinarith [mul_nonneg (sub_nonneg.mpr hleft) (add_nonneg ht0 hleft0)]
  have hd := thirdDigammaLower t hst
  have hlp := thirdLogPiUpper
  have hamp := thirdPrimeAmplitudeUpper
  have hamp0 : 0 ≤ Real.sqrt 2 * Real.log 2 :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg (by norm_num))
  have hcos := mul_le_mul_of_nonneg_left (Real.cos_le_one (t * Real.log 2)) hamp0
  unfold symbol archSymbol
  norm_num at hd hlp hamp ⊢
  linarith only [hd, hlp, hamp, hcos]

/-- A uniform symbol floor on the third cell, produced by exact kernel
arithmetic and the positive-left-endpoint digamma certificate. -/
theorem thirdCell_symbol_lower (t : ℝ)
    (hlo : (thirdCell.lo : ℝ) ≤ t) (_hhi : t ≤ (thirdCell.hi : ℝ)) :
    (-1269 / 200 : ℝ) ≤ symbol t :=
  symbol_lower_of_thirdLeft_le t (by simpa [thirdCell] using hlo)

private def reuseRadius : ℝ := 525 / 16384
private def symbolFloor : ℝ := -1269 / 200
private def weightedCoefficient : ℝ :=
  symbolFloor - 1 / 16 - (lowerValue thirdCell : ℝ)
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

private theorem endpoint_budget : (1 / 4000 : ℝ) < weightedFloor reuseRadius := by
  norm_num [weightedFloor, reuseRadius, weightedCoefficient, symbolFloor,
    thirdCell, lowerValue, jetPolynomial7, firstJet, firstCenter,
    reuseError, firstJetError, serializedM8Q, Finset.sum_range_succ]

private theorem weightedFloor_lower (t : ℝ) (ht0 : 0 ≤ t)
    (htr : t ≤ reuseRadius) : weightedFloor reuseRadius ≤ weightedFloor t := by
  have h2 := mul_le_mul_of_nonpos_left (pow_le_pow_left₀ ht0 htr 2)
    (show firstJet 2 + weightedCoefficient / 2 ≤ 0 by
      norm_num [firstJet, weightedCoefficient, symbolFloor, thirdCell, lowerValue])
  have h4 := mul_le_mul_of_nonpos_left (pow_le_pow_left₀ ht0 htr 4)
    (show firstJet 4 + weightedCoefficient ≤ 0 by
      norm_num [firstJet, weightedCoefficient, symbolFloor, thirdCell, lowerValue])
  have h6 := mul_le_mul_of_nonpos_left (pow_le_pow_left₀ ht0 htr 6)
    (show firstJet 6 ≤ 0 by norm_num [firstJet])
  simp only [weightedFloor_expansion]
  linarith only [h2, h4, h6]

/-- The unchanged third serialized lower bound follows from the already proved
zero jet, M8 bound, and the positive-endpoint symbol certificate above. -/
theorem thirdCell_sound_from_existing_zero_jet : CellAnalyticSoundV1 thirdCell := by
  apply cellAnalyticSound_of_correction_lower thirdCell
    (fun t => jetPolynomial7 firstJet firstCenter t - reuseError)
  · intro t hlo hhi
    have ht0 : 0 ≤ t := by norm_num [thirdCell] at hlo; linarith
    have htr : t ≤ reuseRadius := by simpa [thirdCell, reuseRadius] using hhi
    have hcover : |t - firstCenter| ≤ reuseRadius := by
      rw [firstCenter, sub_zero, abs_of_nonneg ht0]
      exact htr
    exact correction_lower_of_jet_enclosures firstCenter t reuseRadius
      (jetPolynomial7 firstJet firstCenter t) firstJet firstJetError
      (by norm_num [reuseRadius]) hcover existing_zero_jet_enclosures le_rfl
  · intro t hlo hhi
    have ht0 : 0 ≤ t := by norm_num [thirdCell] at hlo; linarith
    have htr : t ≤ reuseRadius := by simpa [thirdCell, reuseRadius] using hhi
    have hgap : 0 ≤ weightedFloor t :=
      ((by norm_num : (0 : ℝ) ≤ 1 / 4000).trans endpoint_budget.le).trans
        (weightedFloor_lower t ht0 htr)
    have hs : symbolFloor ≤ symbol t := thirdCell_symbol_lower t hlo hhi
    have hsmul := mul_le_mul_of_nonneg_left
      (sub_le_sub_right hs (1 / 16)) (sq_nonneg (t ^ 2 + 1 / 4))
    calc
      (t ^ 2 + 1 / 4) ^ 2 * (lowerValue thirdCell : ℝ) ≤
          (t ^ 2 + 1 / 4) ^ 2 * (symbolFloor - 1 / 16) +
            (jetPolynomial7 firstJet firstCenter t - reuseError) := by
        dsimp only [weightedFloor, weightedCoefficient] at hgap
        nlinarith only [hgap]
      _ ≤ (t ^ 2 + 1 / 4) ^ 2 * (symbol t - 1 / 16) +
          (jetPolynomial7 firstJet firstCenter t - reuseError) := by
        simpa only [add_comm] using
          add_le_add_right hsmul (jetPolynomial7 firstJet firstCenter t - reuseError)

/-- The first three unchanged serialized cell results compose as a triple. -/
theorem first_three_cells_sound :
    CellAnalyticSoundV1 firstCell ∧
      CellAnalyticSoundV1 AEGIS.RHKreinSecondCellReductionV1.secondCell ∧
      CellAnalyticSoundV1 thirdCell :=
  ⟨firstCell_sound_of_jet_enclosures,
    secondCell_sound_from_existing_zero_jet,
    thirdCell_sound_from_existing_zero_jet⟩

end AEGIS.RHKreinThirdCellCompositionV1

#print axioms AEGIS.RHKreinThirdCellCompositionV1.thirdCell_symbol_lower
#print axioms AEGIS.RHKreinThirdCellCompositionV1.symbol_lower_of_thirdLeft_le
#print axioms AEGIS.RHKreinThirdCellCompositionV1.thirdCell_sound_from_existing_zero_jet
#print axioms AEGIS.RHKreinThirdCellCompositionV1.first_three_cells_sound
