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

import AEGISOverlay.RHKreinM8AnalyticV1
import AEGISOverlay.RHKreinFiniteCertificateAssemblyV1

/-!
# M8 Taylor bounds to analytic cell soundness

This file removes the division from the remaining cell obligation and then
connects the canonical degree-seven Taylor/jet bound to that weighted target.
It deliberately retains the actual symbol lower bound, jet enclosures, and
polynomial lower bound as premises. No serialized cell or RH claim is proved.

AUTHORITY_EFFECT = NONE.
-/

open scoped BigOperators

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHKreinCellAnalyticBridgeV1

open AEGIS.RHKreinCorrectionM8BoundV1
open AEGIS.RHKreinExplicitCorrectionV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1
open AEGIS.RHKreinFiniteCertificateDataV1
open AEGIS.RHKreinM8AnalyticV1
open AEGIS.RHKreinM8CertificateV1
open AEGIS.RHKreinPrimeSymbolV1

/-- Cell soundness is exactly the division-free weighted inequality. -/
theorem cellAnalyticSound_iff_weighted (c : FiniteCellV1) :
    CellAnalyticSoundV1 c ↔
      ∀ t : ℝ, (c.lo : ℝ) ≤ t → t ≤ (c.hi : ℝ) →
        (t ^ 2 + 1 / 4) ^ 2 * (lowerValue c : ℝ) ≤ correctedExpression t := by
  constructor
  · intro hcell t hlo hhi
    rw [correctedExpression_eq_weight_mul_normalizedExcess_v1]
    exact mul_le_mul_of_nonneg_left (hcell t hlo hhi) (weight_pos_v1 t).le
  · intro hweighted t hlo hhi
    have h := hweighted t hlo hhi
    rw [correctedExpression_eq_weight_mul_normalizedExcess_v1] at h
    exact le_of_mul_le_mul_left h (weight_pos_v1 t)

/-- A lower bound for the correction plus an exact weighted budget closes one cell. -/
theorem cellAnalyticSound_of_correction_lower
    (c : FiniteCellV1) (correctionLower : ℝ → ℝ)
    (hcorrection : ∀ t : ℝ, (c.lo : ℝ) ≤ t → t ≤ (c.hi : ℝ) →
      correctionLower t ≤ correctionSymbol t)
    (hbudget : ∀ t : ℝ, (c.lo : ℝ) ≤ t → t ≤ (c.hi : ℝ) →
      (t ^ 2 + 1 / 4) ^ 2 * (lowerValue c : ℝ) ≤
        (t ^ 2 + 1 / 4) ^ 2 * (symbol t - 1 / 16) + correctionLower t) :
    CellAnalyticSoundV1 c := by
  rw [cellAnalyticSound_iff_weighted]
  intro t hlo hhi
  apply (hbudget t hlo hhi).trans
  unfold correctedExpression
  exact add_le_add_right (hcorrection t hlo hhi) _

/-- The canonical M8 remainder and jet enclosure imply cell soundness once
the symbol and approximating polynomial satisfy the displayed exact budget. -/
theorem cellAnalyticSound_of_jet_enclosures
    (c : FiniteCellV1) (center radius polynomialLower : ℝ) (q e : ℕ → ℝ)
    (hradius : 0 ≤ radius)
    (hcover : ∀ t : ℝ, (c.lo : ℝ) ≤ t → t ≤ (c.hi : ℝ) →
      |t - center| ≤ radius)
    (hjet : ∀ k ∈ Finset.range 8, |exactJetCoefficient center k - q k| ≤ e k)
    (hpolynomial : ∀ t : ℝ, (c.lo : ℝ) ≤ t → t ≤ (c.hi : ℝ) →
      polynomialLower ≤ jetPolynomial7 q center t)
    (hbudget : ∀ t : ℝ, (c.lo : ℝ) ≤ t → t ≤ (c.hi : ℝ) →
      (t ^ 2 + 1 / 4) ^ 2 * (lowerValue c : ℝ) ≤
        (t ^ 2 + 1 / 4) ^ 2 * (symbol t - 1 / 16) +
          (polynomialLower - ((serializedM8Q : ℝ) * radius ^ 8 / 40320 +
            ∑ k ∈ Finset.range 8, e k * radius ^ k))) :
    CellAnalyticSoundV1 c := by
  apply cellAnalyticSound_of_correction_lower c
    (fun _ => polynomialLower - ((serializedM8Q : ℝ) * radius ^ 8 / 40320 +
      ∑ k ∈ Finset.range 8, e k * radius ^ k))
  · intro t hlo hhi
    exact correction_lower_of_jet_enclosures center t radius polynomialLower q e
      hradius (hcover t hlo hhi) hjet (hpolynomial t hlo hhi)
  · exact hbudget

end AEGIS.RHKreinCellAnalyticBridgeV1

#print axioms AEGIS.RHKreinCellAnalyticBridgeV1.cellAnalyticSound_iff_weighted
#print axioms AEGIS.RHKreinCellAnalyticBridgeV1.cellAnalyticSound_of_correction_lower
#print axioms AEGIS.RHKreinCellAnalyticBridgeV1.cellAnalyticSound_of_jet_enclosures
