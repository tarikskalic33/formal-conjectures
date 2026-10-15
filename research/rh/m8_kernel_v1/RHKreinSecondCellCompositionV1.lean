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

import RHKreinFirstCellV1
import RHKreinSecondCellReductionV1

/-!
# Compose the existing zero jet into the second serialized cell

Uses the eight normalized zero-jet enclosures and global symbol lower bound
from `RHKreinFirstCellV1`, the original-definition M8 Taylor bound, and the
unchanged `secondCell` definition. The combined weighted polynomial has
nonpositive coefficients of t^2, t^4 and t^6. Its lower bound is its value
at 225/8192; exact rational arithmetic closes that budget.
-/

open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace AEGIS.RHKreinSecondCellCompositionV1

open AEGIS.RHKreinFirstCellV1
open AEGIS.RHKreinSecondCellReductionV1
open AEGIS.RHKreinCellAnalyticBridgeV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1
open AEGIS.RHKreinFiniteCertificateDataV1
open AEGIS.RHKreinM8AnalyticV1
open AEGIS.RHKreinM8CertificateV1
open AEGIS.RHKreinPrimeSymbolV1

/-- Package the eight already proved zero-jet results without new enclosures. -/
theorem existing_zero_jet_enclosures :
    ∀ k ∈ Finset.range 8,
      |exactJetCoefficient firstCenter k - firstJet k| ≤ firstJetError k := by
  intro k hk
  have hklt : k < 8 := Finset.mem_range.mp hk
  interval_cases k
  · rw [firstJet_zero_exact]
    norm_num [firstJetError]
  · rw [firstJet_one_exact]
    norm_num [firstJetError]
  · exact firstJet_two_enclosure
  · rw [firstJet_three_exact]
    norm_num [firstJetError]
  · exact firstJet_four_enclosure
  · rw [firstJet_five_exact]
    norm_num [firstJetError]
  · exact firstJet_six_enclosure
  · rw [firstJet_seven_exact]
    norm_num [firstJetError]

private def reuseRadius : ℝ := 225 / 8192
private def symbolFloor : ℝ := -3177232903 / 500000000
private def weightedCoefficient : ℝ :=
  symbolFloor - 1 / 16 - (lowerValue secondCell : ℝ)
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

private theorem endpoint_budget : (1 / 2000 : ℝ) < weightedFloor reuseRadius := by
  norm_num [weightedFloor, reuseRadius, weightedCoefficient, symbolFloor,
    secondCell, lowerValue, jetPolynomial7, firstJet, firstCenter,
    reuseError, firstJetError, serializedM8Q, Finset.sum_range_succ]

private theorem weightedFloor_lower (t : ℝ) (ht0 : 0 ≤ t)
    (htr : t ≤ reuseRadius) : weightedFloor reuseRadius ≤ weightedFloor t := by
  have h2 := mul_le_mul_of_nonpos_left (pow_le_pow_left₀ ht0 htr 2)
    (show firstJet 2 + weightedCoefficient / 2 ≤ 0 by
      norm_num [firstJet, weightedCoefficient, symbolFloor, secondCell, lowerValue])
  have h4 := mul_le_mul_of_nonpos_left (pow_le_pow_left₀ ht0 htr 4)
    (show firstJet 4 + weightedCoefficient ≤ 0 by
      norm_num [firstJet, weightedCoefficient, symbolFloor, secondCell, lowerValue])
  have h6 := mul_le_mul_of_nonpos_left (pow_le_pow_left₀ ht0 htr 6)
    (show firstJet 6 ≤ 0 by norm_num [firstJet])
  simp only [weightedFloor_expansion]
  linarith only [h2, h4, h6]

/-- The unchanged second serialized lower bound follows from existing zero-jet
and global symbol theorems. No second-center analytic hypothesis is required. -/
theorem secondCell_sound_from_existing_zero_jet : CellAnalyticSoundV1 secondCell := by
  apply cellAnalyticSound_of_correction_lower secondCell
    (fun t => jetPolynomial7 firstJet firstCenter t - reuseError)
  · intro t hlo hhi
    have ht0 : 0 ≤ t := by norm_num [secondCell] at hlo; linarith
    have htr : t ≤ reuseRadius := by simpa [secondCell, reuseRadius] using hhi
    have hcover : |t - firstCenter| ≤ reuseRadius := by
      rw [firstCenter, sub_zero, abs_of_nonneg ht0]
      exact htr
    exact correction_lower_of_jet_enclosures firstCenter t reuseRadius
      (jetPolynomial7 firstJet firstCenter t) firstJet firstJetError
      (by norm_num [reuseRadius]) hcover existing_zero_jet_enclosures le_rfl
  · intro t hlo hhi
    have ht0 : 0 ≤ t := by norm_num [secondCell] at hlo; linarith
    have htr : t ≤ reuseRadius := by simpa [secondCell, reuseRadius] using hhi
    have hgap : 0 ≤ weightedFloor t :=
      ((by norm_num : (0 : ℝ) ≤ 1 / 2000).trans endpoint_budget.le).trans
        (weightedFloor_lower t ht0 htr)
    have hs : symbolFloor ≤ symbol t := firstCell_symbol_lower t
    have hsmul := mul_le_mul_of_nonneg_left
      (sub_le_sub_right hs (1 / 16)) (sq_nonneg (t ^ 2 + 1 / 4))
    calc
      (t ^ 2 + 1 / 4) ^ 2 * (lowerValue secondCell : ℝ) ≤
          (t ^ 2 + 1 / 4) ^ 2 * (symbolFloor - 1 / 16) +
            (jetPolynomial7 firstJet firstCenter t - reuseError) := by
        dsimp only [weightedFloor, weightedCoefficient] at hgap
        nlinarith only [hgap]
      _ ≤ (t ^ 2 + 1 / 4) ^ 2 * (symbol t - 1 / 16) +
          (jetPolynomial7 firstJet firstCenter t - reuseError) := by
        simpa only [add_comm] using
          add_le_add_right hsmul (jetPolynomial7 firstJet firstCenter t - reuseError)

/-- The first and second unchanged serialized cell results compose as a pair. -/
theorem first_two_cells_sound :
    CellAnalyticSoundV1 firstCell ∧ CellAnalyticSoundV1 secondCell :=
  ⟨firstCell_sound_of_jet_enclosures, secondCell_sound_from_existing_zero_jet⟩

end AEGIS.RHKreinSecondCellCompositionV1

#print axioms AEGIS.RHKreinSecondCellCompositionV1.existing_zero_jet_enclosures
#print axioms AEGIS.RHKreinSecondCellCompositionV1.secondCell_sound_from_existing_zero_jet
#print axioms AEGIS.RHKreinSecondCellCompositionV1.first_two_cells_sound
