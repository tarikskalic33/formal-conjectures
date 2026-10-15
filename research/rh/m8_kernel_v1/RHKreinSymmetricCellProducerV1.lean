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

import RHKreinCellAnalyticBridgeV1

/-!
# Generic symmetric-cell producer for the M8 certificate

This file packages the reusable exact part of the per-cell proof.  Given a
centered radius enclosure, eight jet enclosures, a uniform symbol lower bound,
and one rational ground-budget inequality, the kernel proves
`CellAnalyticSoundV1 c`.

The deliberately conservative polynomial floor

`q 0 - sum k=1..7 |q k| * radius^k`

works without sign analysis.  It is intended as a code-generation target for
the remaining serialized cells.  This theorem does not manufacture the
transcendental jet or symbol enclosures and does not assert all-cell or RH
closure.

AUTHORITY_EFFECT = NONE.
-/

open scoped BigOperators

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHKreinSymmetricCellProducerV1

open AEGIS.RHKreinCellAnalyticBridgeV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1
open AEGIS.RHKreinFiniteCertificateDataV1
open AEGIS.RHKreinM8AnalyticV1
open AEGIS.RHKreinM8CertificateV1
open AEGIS.RHKreinPrimeSymbolV1

/-- A sign-independent rational floor for a degree-seven centered jet. -/
def symmetricPolynomialFloor (q : ℕ → ℝ) (radius : ℝ) : ℝ :=
  q 0 - ∑ k ∈ Finset.range 7, |q (k + 1)| * radius ^ (k + 1)

/-- The complete M8-plus-jet error attached to a symmetric cell. -/
def symmetricTaylorError (radius : ℝ) (e : ℕ → ℝ) : ℝ :=
  (serializedM8Q : ℝ) * radius ^ 8 / 40320 +
    ∑ k ∈ Finset.range 8, e k * radius ^ k

private theorem symmetricPolynomialFloor_le
    (q : ℕ → ℝ) (center radius t : ℝ)
    (ht : |t - center| ≤ radius) :
    symmetricPolynomialFloor q radius ≤ jetPolynomial7 q center t := by
  unfold symmetricPolynomialFloor jetPolynomial7
  conv_rhs => rw [Finset.sum_range_succ']
  simp only [pow_zero, mul_one]
  apply sub_le_iff_le_add.mp
  have hterm : ∀ k ∈ Finset.range 7,
      -(q (k + 1) * (t - center) ^ (k + 1)) ≤
        |q (k + 1)| * radius ^ (k + 1) := by
    intro k hk
    have hpow : |t - center| ^ (k + 1) ≤ radius ^ (k + 1) :=
      pow_le_pow_left₀ (abs_nonneg _) ht _
    have habs : |q (k + 1) * (t - center) ^ (k + 1)| ≤
        |q (k + 1)| * radius ^ (k + 1) := by
      rw [abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left hpow (abs_nonneg _)
    apply le_of_abs_le
    simpa only [abs_neg] using habs
  have hsum := Finset.sum_le_sum hterm
  have hsum' :
      -(∑ k ∈ Finset.range 7, q (k + 1) * (t - center) ^ (k + 1)) ≤
        ∑ k ∈ Finset.range 7, |q (k + 1)| * radius ^ (k + 1) := by
    simpa only [Finset.sum_neg_distrib] using hsum
  linarith

/-- Generic kernel producer for a cell centered in a symmetric radius box.

Only `hjet` and `hsymbol` contain cell-specific analytic content.  The other
premises are exact rational geometry/budget checks suitable for generated
`norm_num` proofs. -/
theorem cellAnalyticSound_of_symmetric_jet_box
    (c : FiniteCellV1) (center radius : ℝ) (q e : ℕ → ℝ)
    (symbolLower weightUpper : ℝ)
    (hradius : 0 ≤ radius)
    (hcover : ∀ t : ℝ, (c.lo : ℝ) ≤ t → t ≤ (c.hi : ℝ) →
      |t - center| ≤ radius)
    (hjet : ∀ k ∈ Finset.range 8, |exactJetCoefficient center k - q k| ≤ e k)
    (hsymbol : ∀ t : ℝ, (c.lo : ℝ) ≤ t → t ≤ (c.hi : ℝ) →
      symbolLower ≤ symbol t)
    (hweight : ∀ t : ℝ, (c.lo : ℝ) ≤ t → t ≤ (c.hi : ℝ) →
      (t ^ 2 + 1 / 4) ^ 2 ≤ weightUpper)
    (hlower : 0 ≤ (lowerValue c : ℝ))
    (hsymbolNonpos : symbolLower - 1 / 16 ≤ 0)
    (hground : weightUpper * (lowerValue c : ℝ) ≤
      weightUpper * (symbolLower - 1 / 16) +
        (symmetricPolynomialFloor q radius - symmetricTaylorError radius e)) :
    CellAnalyticSoundV1 c := by
  apply cellAnalyticSound_of_jet_enclosures c center radius
    (symmetricPolynomialFloor q radius) q e hradius hcover hjet
  · intro t hlo hhi
    exact symmetricPolynomialFloor_le q center radius t (hcover t hlo hhi)
  · intro t hlo hhi
    have hw0 : 0 ≤ (t ^ 2 + 1 / 4) ^ 2 := sq_nonneg _
    have hlhs : (t ^ 2 + 1 / 4) ^ 2 * (lowerValue c : ℝ) ≤
        weightUpper * (lowerValue c : ℝ) :=
      mul_le_mul_of_nonneg_right (hweight t hlo hhi) hlower
    have hneg : weightUpper * (symbolLower - 1 / 16) ≤
        (t ^ 2 + 1 / 4) ^ 2 * (symbolLower - 1 / 16) :=
      mul_le_mul_of_nonpos_right (hweight t hlo hhi) hsymbolNonpos
    have hsym : (t ^ 2 + 1 / 4) ^ 2 * (symbolLower - 1 / 16) ≤
        (t ^ 2 + 1 / 4) ^ 2 * (symbol t - 1 / 16) :=
      mul_le_mul_of_nonneg_left (sub_le_sub_right (hsymbol t hlo hhi) _) hw0
    change (t ^ 2 + 1 / 4) ^ 2 * (lowerValue c : ℝ) ≤
      (t ^ 2 + 1 / 4) ^ 2 * (symbol t - 1 / 16) +
        (symmetricPolynomialFloor q radius - symmetricTaylorError radius e)
    linarith

end AEGIS.RHKreinSymmetricCellProducerV1

#print axioms AEGIS.RHKreinSymmetricCellProducerV1.cellAnalyticSound_of_symmetric_jet_box
