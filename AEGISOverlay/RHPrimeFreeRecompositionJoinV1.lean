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

import AEGISOverlay.RHScaleRowCompositionV1
import Mathlib.Tactic

/-!
# Exact universal fine partition + two prime-free windows + signed real rows

For each moment-zero smooth Weil packet, the existing unconditional constructor
provides an exact finite reconstruction, local width certificates and the actual
Weil Gram. On EVERY pair whose separation lies in one of the two source-proved
prime-log-free intervals, the genuinely arithmetic Weil B norm is bounded by
676/65536 times the sum of individual energies.

Other pairs, notably prime-log resonances, are NOT assigned an invented bound.
A separate explicitly stated signed-resonant certificate can then be combined
with the source-proved nonresonant estimates and the already verified
signed-real row consumer.

The final RH theorem remains conditional on producing the resonant certificate
for every source partition. This file adds no axiom, sorry or RH assumption.
-/

open Complex
open Finset
open scoped BigOperators

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHPrimeFreeRecompositionJoinV1

open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilDisjointEnergyV2
open AEGIS.RHActualUniversalFineGramV1
open AEGIS.RHGramExpansionV13

/-- The two genuine-prime-free separation intervals where a uniform
source-proved fine-pair Q16.16 budget is available. -/
def FineLogFreeGap (d : ℝ) : Prop :=
  (35 / 128 : ℝ) ≤ d ∧
    (d < Real.log 2 - (1 / 128 : ℝ) ∨
      (Real.log 2 + (1 / 128 : ℝ) < d ∧
        d < Real.log 3 - (1 / 128 : ℝ)))

/-- Orientation-independent true-Weil pair bound for DIFFERENT fine atoms.
The packet moments are not moved across atoms unless the roles are swapped
together with the energy terms. The cost is not rounded per prime summand. -/
theorem actual_fine_pair_q16_of_log_free_gap
    {n : ℕ} (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (center : Fin (n + 1) → ℝ)
    (hm : ∀ i, WeilMomentConditionsV1 (gs i))
    (hw : ∀ i,
      AEGIS.RHRationalNinePacketPrimeWindowV1.WidthOneOneTwentyEightAt
        (gs i) (center i))
    (i j : Fin (n + 1))
    (hfree : FineLogFreeGap |center j - center i|) :
    ‖B (gs i) (gs j)‖ ≤
      (676 / 65536 : ℝ) * (energy (gs i).1 + energy (gs j).1) := by
  obtain ⟨hsep, hinterval⟩ := hfree
  by_cases hij : center i ≤ center j
  · have habs : |center j - center i| = center j - center i :=
      abs_of_nonneg (sub_nonneg.mpr hij)
    rw [habs] at hsep hinterval
    exact AEGIS.RHActualMixedDefectV1.distinct_fine_actual_B_q16_first_two_log_free_windows
      (gs i) (gs j) (center i) (center j)
      (hw i) (hw j) (hm i) hsep hinterval
  · have hji : center j ≤ center i :=
      le_of_lt (lt_of_not_ge hij)
    have habs : |center j - center i| = center i - center j := by
      rw [abs_sub_comm]
      exact abs_of_nonneg (sub_nonneg.mpr hji)
    rw [habs] at hsep hinterval
    have hb :=
      AEGIS.RHActualMixedDefectV1.distinct_fine_actual_B_q16_first_two_log_free_windows
        (gs j) (gs i) (center j) (center i)
        (hw j) (hw i) (hm j) hsep hinterval
    calc
      ‖B (gs i) (gs j)‖ = ‖B (gs j) (gs i)‖ := by
        rw [B_hermitian, Complex.norm_conj]
      _ ≤ (676 / 65536 : ℝ) *
          (energy (gs j).1 + energy (gs i).1) := hb
      _ = (676 / 65536 : ℝ) *
          (energy (gs i).1 + energy (gs j).1) := by ring

/-- Each arbitrary moment-zero Weil packet has a FINITE source-exact
decomposition, AND ALL of its prime-free fine pairs are certified.
No global row budget is presumed. -/
theorem every_packet_actual_fine_gram_with_log_free_pairs
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g) :
    ∃ (n : ℕ) (gs : Fin (n + 1) → WeilCompactSmoothGV1)
      (center : Fin (n + 1) → ℝ),
      (∀ i, WeilMomentConditionsV1 (gs i)) ∧
      (∀ i, (5671 / 3200 : ℝ) * energy (gs i).1 ≤
        -(B (gs i) (gs i)).re) ∧
      (∀ i, AEGIS.RHRationalNinePacketPrimeWindowV1.WidthOneOneTwentyEightAt
        (gs i) (center i)) ∧
      g = packetSum (fun _ => (1 : ℂ)) gs ∧
      (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re =
        (∑ i, ∑ j, B (gs i) (gs j)).re ∧
      (∀ i j, FineLogFreeGap |center j - center i| →
        ‖B (gs i) (gs j)‖ ≤
          (676 / 65536 : ℝ) *
            (energy (gs i).1 + energy (gs j).1)) := by
  obtain ⟨n, gs, center, hmom, hdiag, hwidth, hpacket, hgram⟩ :=
    every_moment_zero_packet_actual_fine_gram_with_support g hm
  refine ⟨n, gs, center, hmom, hdiag, hwidth, hpacket, hgram, ?_⟩
  intro i j hfree
  exact actual_fine_pair_q16_of_log_free_gap gs center hmom hwidth i j hfree

/-- Unconditional multiscale receipt for every moment-zero packet. It joins:
  * an exact finite source reconstruction,
  * the genuine, signed intra/inter-block identity for ANY regrouping,
  * the proved 9/64 exact coercivity IF all centers fit a common window,
  * the genuine von Mangoldt/Arch Q16.16 pair estimate on log-free gaps.

The common-window hypothesis is NOT inferred globally; the inter-block
mixed contributions remain present in the signed split. -/
theorem every_packet_actual_fine_multiscale_receipt
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g) :
    ∃ (n : ℕ) (gs : Fin (n + 1) → WeilCompactSmoothGV1)
      (center : Fin (n + 1) → ℝ),
      (∀ i, WeilMomentConditionsV1 (gs i)) ∧
      (∀ i, (5671 / 3200 : ℝ) * energy (gs i).1 ≤
        -(B (gs i) (gs i)).re) ∧
      (∀ i, AEGIS.RHRationalNinePacketPrimeWindowV1.WidthOneOneTwentyEightAt
        (gs i) (center i)) ∧
      g = packetSum (fun _ => (1 : ℂ)) gs ∧
      (∀ block : Fin (n + 1) → ℕ,
        AEGIS.RHActualMixedDefectV1.actualMixedDefect n gs =
          AEGIS.RHScaleRowCompositionV1.actualIntraBlockSignedDefect gs block +
            AEGIS.RHScaleRowCompositionV1.actualInterBlockSignedDefect gs block) ∧
      (∀ common : ℝ,
        (∀ i, |center i - common| ≤ (35 / 256 : ℝ)) →
        (1 / 10 : ℝ) * energy g.1 ≤ -(B g g).re) ∧
      (∀ i j, FineLogFreeGap |center j - center i| →
        ‖B (gs i) (gs j)‖ ≤
          (676 / 65536 : ℝ) *
            (energy (gs i).1 + energy (gs j).1)) := by
  obtain ⟨n, gs, center, hmom, hdiag, hwidth, hpacket, _hgram, hfree⟩ :=
    every_packet_actual_fine_gram_with_log_free_pairs g hm
  refine ⟨n, gs, center, hmom, hdiag, hwidth, hpacket, ?_, ?_, hfree⟩
  · intro block
    exact AEGIS.RHScaleRowCompositionV1.actual_mixed_defect_eq_block_signed_split
      gs block
  · intro common hnear
    rw [hpacket]
    exact AEGIS.RHActualMixedDefectV1.fine_cluster_nine_exact_counterpart
      n (fun _ => (1 : ℂ)) gs center common hmom hwidth hnear

/-- The EXACT mixed row: the known nonresonant cost plus an independent
signed residual for the remaining (including prime-resonant) pairs. -/
def combinedFineCost {n : ℕ}
    (center : Fin (n + 1) → ℝ)
    (residual : Fin (n + 1) → Fin (n + 1) → ℝ)
    (i j : Fin (n + 1)) : ℝ :=
  by
    classical
    exact if FineLogFreeGap |center j - center i| then
      (676 / 65536 : ℝ)
    else residual i j

/-- Symmetry of the entire certified row including resonant residuals. -/
theorem combinedFineCost_symm {n : ℕ}
    (center : Fin (n + 1) → ℝ)
    (residual : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hsym : ∀ i j, residual i j = residual j i)
    (i j : Fin (n + 1)) :
    combinedFineCost center residual i j =
      combinedFineCost center residual j i := by
  classical
  unfold combinedFineCost
  have habs : |center j - center i| = |center i - center j| :=
    abs_sub_comm (center j) (center i)
  rw [habs]
  by_cases hf : FineLogFreeGap |center i - center j|
  · simp [hf]
  · simp [hf, hsym i j]

/-- Complete analytic composition. All log-free pair costs come from the
actual Weil explicit formula; only prime-resonant or otherwise excluded
interactions remain in the residual. The global budget is still explicit. -/
theorem actual_source_gram_coercive_of_resonance_row
    {n : ℕ} (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (center : Fin (n + 1) → ℝ)
    (hm : ∀ i, WeilMomentConditionsV1 (gs i))
    (hwidth : ∀ i,
      AEGIS.RHRationalNinePacketPrimeWindowV1.WidthOneOneTwentyEightAt
        (gs i) (center i))
    (hdiag : ∀ i, (5671 / 3200 : ℝ) * energy (gs i).1 ≤
      -(B (gs i) (gs i)).re)
    (residual : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hsym : ∀ i j, residual i j = residual j i)
    (hres : ∀ i j, i ≠ j →
      ¬ FineLogFreeGap |center j - center i| →
      (B (gs i) (gs j)).re ≤
        residual i j * (energy (gs i).1 + energy (gs j).1))
    (hrow : ∀ i, (∑ j ∈
      (Finset.univ : Finset (Fin (n + 1))).erase i,
        combinedFineCost center residual i j) ≤
          (57430 / 65536 : ℝ)) :
    (B (packetSum (fun _ => (1 : ℂ)) gs)
      (packetSum (fun _ => (1 : ℂ)) gs)).re ≤
        -(641 / 32768 : ℝ) * (∑ i, energy (gs i).1) := by
  classical
  have hcross : ∀ i j, i ≠ j →
      (B (gs i) (gs j)).re ≤
        combinedFineCost center residual i j *
          (energy (gs i).1 + energy (gs j).1) := by
    intro i j hij
    by_cases hf : FineLogFreeGap |center j - center i|
    · have hb := actual_fine_pair_q16_of_log_free_gap
        gs center hm hwidth i j hf
      calc
        (B (gs i) (gs j)).re ≤ ‖B (gs i) (gs j)‖ :=
          Complex.re_le_norm _
        _ ≤ (676 / 65536 : ℝ) *
            (energy (gs i).1 + energy (gs j).1) := hb
        _ = combinedFineCost center residual i j *
            (energy (gs i).1 + energy (gs j).1) := by
              simp only [combinedFineCost, if_pos hf]
    · simpa only [combinedFineCost, if_neg hf] using
        (hres i j hij hf)
  exact actual_fine_gram_coercive_of_signed_real_row_certificate
    gs (combinedFineCost center residual)
    (combinedFineCost_symm center residual hsym)
    hdiag hcross hrow

/-- Exact rational obstruction to a per-link Q16.16 row charge
for unboundedly refined packet partitions: just 85 log-free links
already exceed the formerly proposed universal row limit. This is
a finite-arithmetic theorem, not a statement about the true Weil form. -/
theorem eighty_five_log_free_links_exceed_fixed_row_budget :
    (57430 / 65536 : ℝ) <
      85 * (676 / 65536 : ℝ) := by
  norm_num

/-- The canonical RH handoff with the logically correct QUANTIFIERS:
the caller may choose ONE certified source-exact decomposition for
each moment-zero input packet, rather than being forced to certify
EVERY possible redundant fine decomposition.

The genuinely arithmetic prime-free pair bounds and the signed
Schur consumer are already proved; source selection and the remaining
resonant signed costs are an external analytic obligation.
This theorem makes no unconditional RH claim. -/
theorem riemannHypothesis_of_canonical_resonance_producer
    (hresidual :
      ∀ (g : WeilCompactSmoothGV1), WeilMomentConditionsV1 g →
        ∃ (n : ℕ) (gs : Fin (n + 1) → WeilCompactSmoothGV1)
          (center : Fin (n + 1) → ℝ),
          (∀ i, WeilMomentConditionsV1 (gs i)) ∧
          (∀ i, (5671 / 3200 : ℝ) * energy (gs i).1 ≤
            -(B (gs i) (gs i)).re) ∧
          (∀ i, AEGIS.RHRationalNinePacketPrimeWindowV1.WidthOneOneTwentyEightAt
            (gs i) (center i)) ∧
          g = packetSum (fun _ => (1 : ℂ)) gs ∧
          ∃ residual : Fin (n + 1) → Fin (n + 1) → ℝ,
            (∀ i j, residual i j = residual j i) ∧
            (∀ i j, i ≠ j →
              ¬ FineLogFreeGap |center j - center i| →
              (B (gs i) (gs j)).re ≤
                residual i j * (energy (gs i).1 + energy (gs j).1)) ∧
            (∀ i, (∑ j ∈
              (Finset.univ : Finset (Fin (n + 1))).erase i,
                combinedFineCost center residual i j) ≤
                  (57430 / 65536 : ℝ))) :
    RiemannHypothesis := by
  apply AEGIS.RHRestrictedWeilBridgeV13.final_sign_implies_rh_v13
  intro g hm
  obtain ⟨n, gs, center, hmom, hdiag, hwidth, hpacket,
    residual, hsym, hres, hrow⟩ := hresidual g hm
  have hfull := actual_source_gram_coercive_of_resonance_row
    gs center hmom hwidth hdiag residual hsym hres hrow
  have hE : 0 ≤ (∑ i, energy (gs i).1) :=
    Finset.sum_nonneg (fun i _ => energy_nonnegative (gs i).1)
  rw [hpacket]
  change (B (packetSum (fun _ => (1 : ℂ)) gs)
    (packetSum (fun _ => (1 : ℂ)) gs)).re ≤ 0
  linarith


/-! ## Exact two-block signed Schur certificate for the genuine Weil Gram

The two scalar diagonal reserves can represent fully composed macro blocks.
Unlike a row-by-row Gershgorin or Schur estimate, this accepts the
semidefinite boundary c*c = a*b without a strictly positive gap.
No assertion is made that every moment-zero packet has these reserves.
-/

/-- The two-block determinant condition bounds the total signed
off-diagonal contribution, even if the Schur complement is singular. -/
theorem two_block_schur_signed_scalar
    (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hdet : c * c ≤ a * b) : 2 * c ≤ a + b := by
  by_contra hc
  have hleft : 0 < 2 * c - (a + b) := by linarith
  have hright : 0 < 2 * c + (a + b) := by linarith
  have hprod : 0 < (2 * c - (a + b)) * (2 * c + (a + b)) :=
    mul_pos hleft hright
  nlinarith [sq_nonneg (a - b)]

/-- Signed two-block certificate for the ACTUAL finite Weil form.
The diagonal reserves may come from exact composed 9/64 clusters.
The only mixed hypothesis concerns the complete signed cross budget;
there is no row-wise pair cost, absolute norm, or strict coercivity.
No RH statement is assumed or asserted. -/
theorem actual_signed_two_block_schur_certificate
    {n : ℕ} (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (a b c : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hdet : c * c ≤ a * b)
    (hdiag :
      (∑ i, (B (gs i) (gs i)).re) ≤ -(a + b))
    (hmixed :
      AEGIS.RHActualMixedDefectV1.actualMixedDefect n gs ≤ 2 * c) :
    (B (packetSum (fun _ => (1 : ℂ)) gs)
      (packetSum (fun _ => (1 : ℂ)) gs)).re ≤ 0 := by
  have hcost : 2 * c ≤ a + b :=
    two_block_schur_signed_scalar a b c ha hb hdet
  have hgram :
      (B (packetSum (fun _ => (1 : ℂ)) gs)
         (packetSum (fun _ => (1 : ℂ)) gs)).re =
        (∑ i, ∑ j, B (gs i) (gs j)).re := by
    rw [B_packetSum]
    simp
  unfold AEGIS.RHActualMixedDefectV1.actualMixedDefect at hmixed
  rw [hgram]
  linarith

end AEGIS.RHPrimeFreeRecompositionJoinV1

#print axioms AEGIS.RHPrimeFreeRecompositionJoinV1.actual_fine_pair_q16_of_log_free_gap
#print axioms AEGIS.RHPrimeFreeRecompositionJoinV1.every_packet_actual_fine_gram_with_log_free_pairs
#print axioms AEGIS.RHPrimeFreeRecompositionJoinV1.every_packet_actual_fine_multiscale_receipt
#print axioms AEGIS.RHPrimeFreeRecompositionJoinV1.combinedFineCost_symm
#print axioms AEGIS.RHPrimeFreeRecompositionJoinV1.actual_source_gram_coercive_of_resonance_row
#print axioms AEGIS.RHPrimeFreeRecompositionJoinV1.riemannHypothesis_of_canonical_resonance_producer
#print axioms AEGIS.RHPrimeFreeRecompositionJoinV1.eighty_five_log_free_links_exceed_fixed_row_budget
#print axioms AEGIS.RHPrimeFreeRecompositionJoinV1.two_block_schur_signed_scalar
#print axioms AEGIS.RHPrimeFreeRecompositionJoinV1.actual_signed_two_block_schur_certificate
