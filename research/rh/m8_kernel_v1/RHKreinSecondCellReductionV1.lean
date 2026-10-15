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

import RHKreinSymmetricCellProducerV1

/-!
# Generated reduction for serialized cell 1 (zero-based)

This is the first concrete consumer of the generic symmetric-cell producer.
Exact arithmetic closes the geometry, polynomial floor, M8 error, weight, and
ground budget.  Only the eight jet enclosures and uniform symbol enclosure are
retained as explicit analytic premises.

AUTHORITY_EFFECT = NONE.
-/

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section

namespace AEGIS.RHKreinSecondCellReductionV1

open AEGIS.RHKreinFiniteCertificateAssemblyV1
open AEGIS.RHKreinFiniteCertificateDataV1
open AEGIS.RHKreinM8AnalyticV1
open AEGIS.RHKreinSymmetricCellProducerV1

def secondCell : FiniteCellV1 :=
  ⟨75 / 4096, 225 / 8192, 123598475210567660⟩

def secondCenter : ℝ := 375 / 16384
def secondRadius : ℝ := 75 / 16384

def secondJet : ℕ → ℝ
  | 0 => 80815639731 / 200000000000
  | 1 => 102811909419 / 1000000000000
  | 2 => 2250352788951 / 1000000000000
  | 3 => 191886691311 / 1000000000000
  | 4 => 2094913562929 / 1000000000000
  | 5 => -26262597593 / 1000000000000
  | 6 => -6007036577 / 31250000000
  | 7 => -18448316629 / 1000000000000
  | _ => 0

def secondJetError (_ : ℕ) : ℝ := 1 / 1000000000000
def secondSymbolLower : ℝ := -793621747503 / 125000000000
def secondWeightUpper : ℝ := 283176232721281 / 4503599627370496

/-- Exact second-cell reduction.  The hypotheses say precisely what the
remaining kernel enclosure generator must prove. -/
theorem secondCell_sound_of_enclosures
    (hjet : ∀ k ∈ Finset.range 8,
      |exactJetCoefficient secondCenter k - secondJet k| ≤ secondJetError k)
    (hsymbol : ∀ t : ℝ, (secondCell.lo : ℝ) ≤ t → t ≤ (secondCell.hi : ℝ) →
      secondSymbolLower ≤ AEGIS.RHKreinPrimeSymbolV1.symbol t) :
    CellAnalyticSoundV1 secondCell := by
  apply cellAnalyticSound_of_symmetric_jet_box secondCell secondCenter secondRadius
    secondJet secondJetError secondSymbolLower secondWeightUpper
  · norm_num [secondRadius]
  · intro t hlo hhi
    norm_num [secondCell, secondCenter, secondRadius] at hlo hhi ⊢
    rw [abs_le]
    constructor <;> linarith
  · exact hjet
  · exact hsymbol
  · intro t hlo hhi
    norm_num [secondCell, secondWeightUpper] at hlo hhi ⊢
    have ht0 : 0 ≤ t := by linarith
    nlinarith [sq_nonneg t,
      mul_nonneg (sub_nonneg.mpr hhi)
        (add_nonneg ht0 (by norm_num : (0 : ℝ) ≤ 225 / 8192))]
  · norm_num [secondCell, lowerValue]
  · norm_num [secondSymbolLower]
  · norm_num [secondCell, secondRadius, secondJet, secondJetError,
      secondSymbolLower, secondWeightUpper, lowerValue,
      symmetricPolynomialFloor, symmetricTaylorError,
      AEGIS.RHKreinM8CertificateV1.serializedM8Q,
      Finset.sum_range_succ]

end AEGIS.RHKreinSecondCellReductionV1

#print axioms AEGIS.RHKreinSecondCellReductionV1.secondCell_sound_of_enclosures
