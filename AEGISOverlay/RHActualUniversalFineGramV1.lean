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
import AEGISOverlay.RHFiniteFinePartitionV1
import AEGISOverlay.RHActualMixedDefectV1
import RHRestrictedWeilBridgeV13
import AEGISOverlay.RHArchGeometric145V1

/-! All compact-support moment-zero Weil packets have an actual finite
fine coercive Gram decomposition. The finite smooth partition is
constructed, not supplied by the caller. All mixed entries are retained. -/

open Set Finset Complex
open scoped BigOperators
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHActualUniversalFineGramV1

open AEGIS.WeilMixedAlgebraV2 AEGIS.WeilDisjointEnergyV2
open AEGIS.WeilMixedClosureV2
open AEGIS.RHGramExpansionV13

/-- Construct the actual finite geometry as well as the Gram identities for every packet. -/
theorem every_moment_zero_packet_actual_fine_gram_with_support
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
        (∑ i, ∑ j, B (gs i) (gs j)).re := by
  obtain ⟨L, hL, hs⟩ :=
    AEGIS.WeilWindowExhaustionV1.logLift_has_finite_window_v1 g
  obtain ⟨n, χ, center, hχ, hpart, hcut⟩ :=
    AEGIS.RHFiniteFinePartitionV1.exists_finite_smooth_local_partition
      L (1 / 256) (by norm_num)
  obtain ⟨gs, hmom, hdiag, hwidth, hpacket, hgram⟩ :=
    AEGIS.RHActualLocalGramCoercivityV1.every_packet_actual_fine_coercive_gram_with_support
      n g hm L hL.le hs χ hχ hpart center hcut
  exact ⟨n, gs, center, hmom, hdiag, hwidth, hpacket, hgram⟩


/-- Construct all real Weil Gram entries for an arbitrary compactly supported
moment-zero packet at any positive fine cutoff radius. The exact radius
passes to each localized atom; no mixed interaction is discarded. -/
theorem every_moment_zero_packet_actual_fine_gram_at_radius
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g)
    (r : ℝ) (hr : 0 < r) (hrFine : r ≤ 1 / 256) :
    ∃ (n : ℕ) (gs : Fin (n + 1) → WeilCompactSmoothGV1)
      (center : Fin (n + 1) → ℝ),
      (∀ i, WeilMomentConditionsV1 (gs i)) ∧
      (∀ i, (5671 / 3200 : ℝ) * energy (gs i).1 ≤
        -(B (gs i) (gs i)).re) ∧
      (∀ i, AEGIS.RHDyadicDiagonalV13.HalfWidthAt
        (gs i) r (center i)) ∧
      g = packetSum (fun _ => (1 : ℂ)) gs ∧
      (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re =
        (∑ i, ∑ j, B (gs i) (gs j)).re := by
  obtain ⟨L, hL, hs⟩ :=
    AEGIS.WeilWindowExhaustionV1.logLift_has_finite_window_v1 g
  obtain ⟨n, χ, center, hχ, hpart, hcut⟩ :=
    AEGIS.RHFiniteFinePartitionV1.exists_finite_smooth_local_partition
      L r hr
  obtain ⟨gs, hmom, hdiag, hwidth, hpacket, hgram⟩ :=
    AEGIS.RHActualLocalGramCoercivityV1.every_packet_actual_fine_coercive_gram_at_radius
      n g hm L hL.le hs χ hχ hpart center
      r (le_of_lt hr) hrFine hcut
  exact ⟨n, gs, center, hmom, hdiag, hwidth, hpacket, hgram⟩

/-- Original public theorem, recovered without reconstructing a second partition. -/
theorem every_moment_zero_packet_actual_fine_gram
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g) :
    ∃ (n : ℕ) (gs : Fin (n + 1) → WeilCompactSmoothGV1),
      (∀ i, WeilMomentConditionsV1 (gs i)) ∧
      (∀ i, (5671 / 3200 : ℝ) * energy (gs i).1 ≤
        -(B (gs i) (gs i)).re) ∧
      g = packetSum (fun _ => (1 : ℂ)) gs ∧
      (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re =
        (∑ i, ∑ j, B (gs i) (gs j)).re := by
  obtain ⟨n, gs, _, hmom, hd, _, hpacket, hgram⟩ :=
    every_moment_zero_packet_actual_fine_gram_with_support g hm
  exact ⟨n, gs, hmom, hd, hpacket, hgram⟩

/-- Sum the actual fine diagonal estimates without dropping mixed terms. -/
theorem fine_mixed_defect_lower_bound
    (n : ℕ) (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (hd : ∀ i, (5671 / 3200 : ℝ) * energy (gs i).1 ≤
      -(B (gs i) (gs i)).re) :
    (5671 / 3200 : ℝ) * (∑ i, energy (gs i).1) -
      AEGIS.RHActualMixedDefectV1.actualMixedDefect n gs ≤
        -(∑ i, ∑ j, B (gs i) (gs j)).re := by
  have hs :
      (∑ i, (5671 / 3200 : ℝ) * energy (gs i).1) ≤
        ∑ i, -(B (gs i) (gs i)).re :=
    Finset.sum_le_sum (fun i _ => hd i)
  have hdiag :
      (5671 / 3200 : ℝ) * (∑ i, energy (gs i).1) ≤
        -(∑ i, (B (gs i) (gs i)).re) := by
    rw [Finset.mul_sum]
    simpa only [Finset.sum_neg_distrib] using hs
  unfold AEGIS.RHActualMixedDefectV1.actualMixedDefect
  linarith

/-- An actual quantitative finite witness for every admissible packet.
There is no caller-supplied partition or mixed-term inequality. -/
theorem every_packet_actual_fine_mixed_defect_lower_bound
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g) :
    ∃ (n : ℕ) (gs : Fin (n + 1) → WeilCompactSmoothGV1),
      (∀ i, WeilMomentConditionsV1 (gs i)) ∧
      g = packetSum (fun _ => (1 : ℂ)) gs ∧
      (5671 / 3200 : ℝ) * (∑ i, energy (gs i).1) -
        AEGIS.RHActualMixedDefectV1.actualMixedDefect n gs ≤
          -(WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re := by
  obtain ⟨n, gs, hmom, hd, hpacket, hgram⟩ :=
    every_moment_zero_packet_actual_fine_gram g hm
  refine ⟨n, gs, hmom, hpacket, ?_⟩
  calc
    (5671 / 3200 : ℝ) * (∑ i, energy (gs i).1) -
        AEGIS.RHActualMixedDefectV1.actualMixedDefect n gs ≤
      -(∑ i, ∑ j, B (gs i) (gs j)).re :=
        fine_mixed_defect_lower_bound n gs hd
    _ = -(WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re := by
      rw [hgram]


/-! ## Final exact-head consumer of the universal actual mixed budget

The localization and the full arithmetic Weil Gram are constructed
unconditionally above.  Only \`hbudget\` remains as a mathematical input.
The conclusion is the canonical Mathlib RH proposition, with no renamed
theorem or weakened endpoint.  This implication does not establish
\`hbudget\` and MUST NOT be marked as an unconditional RH proof. -/

/-- Genuine mixed-defect control on the actual fine decompositions
constructed above suffices for the canonical Riemann hypothesis.  No
unproved term is suppressed, and the only remaining hypothesis is
spelled out on the original Weil pairing. -/
theorem riemannHypothesis_of_uniform_actual_fine_mixed_budget
    (hbudget :
      ∀ (g : WeilCompactSmoothGV1), WeilMomentConditionsV1 g →
        ∀ (n : ℕ) (gs : Fin (n + 1) → WeilCompactSmoothGV1),
          (∀ i, (5671 / 3200 : ℝ) * energy (gs i).1 ≤
            -(B (gs i) (gs i)).re) →
          g = packetSum (fun _ => (1 : ℂ)) gs →
          AEGIS.RHActualMixedDefectV1.actualMixedDefect n gs ≤
            (5671 / 3200 : ℝ) * (∑ i, energy (gs i).1)) :
    RiemannHypothesis := by
  apply AEGIS.RHRestrictedWeilBridgeV13.final_sign_implies_rh_v13
  intro g hm
  obtain ⟨n, gs, _hmom, hdiag, hpacket, hgram⟩ :=
    every_moment_zero_packet_actual_fine_gram g hm
  have hpaid := hbudget g hm n gs hdiag hpacket
  have hlower := fine_mixed_defect_lower_bound n gs hdiag
  rw [← hgram] at hlower
  have hnonneg :
      0 ≤ (5671 / 3200 : ℝ) * (∑ i, energy (gs i).1) -
        AEGIS.RHActualMixedDefectV1.actualMixedDefect n gs :=
    sub_nonneg.mpr hpaid
  linarith


/-! ## Q16.16 admission of all actual mixed entries, arbitrary finite dimension

A matrix of *integer* outward upper bounds is checked on every row.
The matrix need not be Toeplitz and each genuine Weil atom may have a
different energy.  Numerical rounding does NOT supply the analytic
pairwise estimates: \`hcross\` is an explicit hypothesis.  No global
claim is made until a producer constructs these certificates for every
admissible packet. -/

def actualQ16PairCost {n : ℕ}
    (cost : Fin (n + 1) → Fin (n + 1) → ℕ)
    (i j : Fin (n + 1)) : ℝ :=
  (cost i j : ℝ) / 65536

/-- Every entry of the actual Hermitian Gram, including arbitrarily
distant pairs, is charged to the integer Q16.16 budget of its row.
The row budget is checked before any sign is concluded. -/
theorem actual_mixed_defect_le_of_q16_matrix
    {n : ℕ} (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (cost : Fin (n + 1) → Fin (n + 1) → ℕ)
    (hsym : ∀ i j, cost i j = cost j i)
    (hcross : ∀ i j, i ≠ j →
      ‖B (gs i) (gs j)‖ ≤
        actualQ16PairCost cost i j *
          (energy (gs i).1 + energy (gs j).1))
    (hrow : ∀ i, (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
       cost i j) ≤ 57430) :
    AEGIS.RHActualMixedDefectV1.actualMixedDefect n gs ≤
       (114860 / 65536 : ℝ) * (∑ i, energy (gs i).1) := by
  let E : Fin (n + 1) → ℝ := fun i => energy (gs i).1
  let c : Fin (n + 1) → Fin (n + 1) → ℝ := actualQ16PairCost cost
  have hsplit (i : Fin (n + 1)) :
      (∑ j, (B (gs i) (gs j)).re) =
        (B (gs i) (gs i)).re +
          ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
            (B (gs i) (gs j)).re := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have hdef :
      AEGIS.RHActualMixedDefectV1.actualMixedDefect n gs =
        ∑ i, ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
          (B (gs i) (gs j)).re := by
    unfold AEGIS.RHActualMixedDefectV1.actualMixedDefect
    rw [Complex.re_sum]
    simp_rw [Complex.re_sum]
    simp_rw [hsplit]
    rw [Finset.sum_add_distrib]
    ring
  have hrows (i : Fin (n + 1)) :
      (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i, c i j) ≤
        (57430 / 65536 : ℝ) := by
    change (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
      (cost i j : ℝ) / 65536) ≤ _
    calc
      (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        (cost i j : ℝ) / 65536) =
        ((∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
          cost i j : ℕ) : ℝ) / 65536 := by
          simp only [Finset.sum_div, Nat.cast_sum]
      _ ≤ (57430 / 65536 : ℝ) :=
        div_le_div_of_nonneg_right (by exact_mod_cast hrow i) (by norm_num)
  have hoff :
      (∑ i, ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        (B (gs i) (gs j)).re) ≤
      ∑ i, ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        c i j * (E i + E j) := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j hj
    have hij : i ≠ j := by
      intro h
      exact (Finset.mem_erase.mp hj).1 h.symm
    calc
      (B (gs i) (gs j)).re ≤ ‖B (gs i) (gs j)‖ :=
        Complex.re_le_norm _
      _ ≤ c i j * (E i + E j) := hcross i j hij
  have hswap :
      (∑ i, ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        c i j * E j) =
      (∑ i, ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        c i j * E i) := by
    rw [AEGIS.RHGramExpansionV13.sum_erase_comm
      (fun i j => c i j * E j)]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have hc : c j i = c i j := by
      dsimp [c, actualQ16PairCost]
      rw [hsym j i]
    rw [hc]
  have hfactor :
      (∑ i, ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        c i j * E i) =
      ∑ i, E i * (∑ j ∈
        (Finset.univ : Finset (Fin (n + 1))).erase i, c i j) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have htwo :
      (∑ i, ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        c i j * (E i + E j)) =
      2 * (∑ i, E i * (∑ j ∈
        (Finset.univ : Finset (Fin (n + 1))).erase i, c i j)) := by
    calc
      _ = (∑ i, ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
             c i j * E i) +
          (∑ i, ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
             c i j * E j) := by
            simp only [mul_add, Finset.sum_add_distrib]
      _ = 2 * (∑ i, E i * (∑ j ∈
           (Finset.univ : Finset (Fin (n + 1))).erase i, c i j)) := by
            rw [hswap]
            simp only [hfactor]
            ring
  have hrowtotal :
      (∑ i, E i * (∑ j ∈
        (Finset.univ : Finset (Fin (n + 1))).erase i, c i j)) ≤
      (57430 / 65536 : ℝ) * (∑ i, E i) := by
    calc
      _ ≤ ∑ i, E i * (57430 / 65536 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left (hrows i)
          (energy_nonnegative (gs i).1)
      _ = (57430 / 65536 : ℝ) * (∑ i, E i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
  calc
    AEGIS.RHActualMixedDefectV1.actualMixedDefect n gs =
        (∑ i, ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
          (B (gs i) (gs j)).re) := hdef
    _ ≤ (∑ i, ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
          c i j * (E i + E j)) := hoff
    _ = 2 * (∑ i, E i * (∑ j ∈
          (Finset.univ : Finset (Fin (n + 1))).erase i, c i j)) := htwo
    _ ≤ 2 * ((57430 / 65536 : ℝ) * (∑ i, E i)) :=
        mul_le_mul_of_nonneg_left hrowtotal (by norm_num)
    _ = (114860 / 65536 : ℝ) * (∑ i, energy (gs i).1) := by
        dsimp [E]
        ring

/-- Q16.16 analytic input plus exact integer row checks leaves an actual
strict positive margin, even for atoms with unequal energies.  The
coercivity conclusion is for the genuine Weil quadratic form. -/
theorem actual_fine_gram_q16_coercive_of_pair_certificate
    {n : ℕ} (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (cost : Fin (n + 1) → Fin (n + 1) → ℕ)
    (hsym : ∀ i j, cost i j = cost j i)
    (hdiag : ∀ i, (5671 / 3200 : ℝ) * energy (gs i).1 ≤
      -(B (gs i) (gs i)).re)
    (hcross : ∀ i j, i ≠ j →
      ‖B (gs i) (gs j)‖ ≤
        actualQ16PairCost cost i j *
          (energy (gs i).1 + energy (gs j).1))
    (hrow : ∀ i, (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
       cost i j) ≤ 57430) :
    (B (packetSum (fun _ => (1 : ℂ)) gs)
        (packetSum (fun _ => (1 : ℂ)) gs)).re ≤
       -(641 / 32768 : ℝ) * (∑ i, energy (gs i).1) := by
  have hmixed := actual_mixed_defect_le_of_q16_matrix
    gs cost hsym hcross hrow
  have hlocal := fine_mixed_defect_lower_bound n gs hdiag
  have hgram :
      (B (packetSum (fun _ => (1 : ℂ)) gs)
        (packetSum (fun _ => (1 : ℂ)) gs)).re =
      (∑ i, ∑ j, B (gs i) (gs j)).re := by
    rw [AEGIS.RHGramExpansionV13.B_packetSum]
    simp
  rw [← hgram] at hlocal
  have hE : 0 ≤ (∑ i, energy (gs i).1) :=
    Finset.sum_nonneg (fun i _ => energy_nonnegative (gs i).1)
  have hround :
      (116142 / 65536 : ℝ) * (∑ i, energy (gs i).1) ≤
        (5671 / 3200 : ℝ) * (∑ i, energy (gs i).1) :=
    mul_le_mul_of_nonneg_right (by norm_num) hE
  linarith

/-- The full conditional Q16.16 route to the canonical RH theorem.  The
certificate producer must select at least one admissible finite
reconstruction for each moment-zero packet; arbitrary decompositions
are not assumed to satisfy the same strict Q16.16 row budget. -/
theorem riemannHypothesis_of_universal_actual_q16_pair_certificates
    (hcert : ∀ (g : WeilCompactSmoothGV1),
      WeilMomentConditionsV1 g →
      ∃ (n : ℕ) (gs : Fin (n + 1) → WeilCompactSmoothGV1),
        g = packetSum (fun _ => (1 : ℂ)) gs ∧
        (∀ i, (5671 / 3200 : ℝ) * energy (gs i).1 ≤
          -(B (gs i) (gs i)).re) ∧
        ∃ cost : Fin (n + 1) → Fin (n + 1) → ℕ,
          (∀ i j, cost i j = cost j i) ∧
          (∀ i j, i ≠ j →
            ‖B (gs i) (gs j)‖ ≤
              actualQ16PairCost cost i j *
                (energy (gs i).1 + energy (gs j).1)) ∧
          (∀ i, (∑ j ∈
            (Finset.univ : Finset (Fin (n + 1))).erase i,
            cost i j) ≤ 57430)) :
    RiemannHypothesis := by
  apply AEGIS.RHRestrictedWeilBridgeV13.final_sign_implies_rh_v13
  intro g hm
  obtain ⟨n, gs, hg, hd, cost, hsym, hcross, hrow⟩ := hcert g hm
  have hbound := actual_fine_gram_q16_coercive_of_pair_certificate
    gs cost hsym hd hcross hrow
  have hE : 0 ≤ (∑ i, energy (gs i).1) :=
    Finset.sum_nonneg (fun i _ => energy_nonnegative (gs i).1)
  rw [hg]
  change (B (packetSum (fun _ => (1 : ℂ)) gs)
    (packetSum (fun _ => (1 : ℂ)) gs)).re ≤ 0
  linarith


/-! ## Exact real-weight Schur summation without integer ceiling per pair -/

/-- For a symmetric real matrix of actual Weil cross coefficients, a
uniform row bound controls the entire signed mixed defect in arbitrary
finite dimension. Unlike independent Q16 pairwise rounding, the theorem
does not impose any cardinality-dependent minimum cost on each pair. -/
theorem actual_mixed_defect_le_of_real_symmetric_row
    {n : ℕ} (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (c : Fin (n + 1) → Fin (n + 1) → ℝ) (R : ℝ)
    (hsym : ∀ i j, c i j = c j i)
    (hcross : ∀ i j, i ≠ j →
      ‖B (gs i) (gs j)‖ ≤
        c i j * (energy (gs i).1 + energy (gs j).1))
    (hrow : ∀ i, (∑ j ∈
      (Finset.univ : Finset (Fin (n + 1))).erase i, c i j) ≤ R) :
    AEGIS.RHActualMixedDefectV1.actualMixedDefect n gs ≤
      (2 * R) * (∑ i, energy (gs i).1) := by
  let E : Fin (n + 1) → ℝ := fun i => energy (gs i).1
  have hsplit (i : Fin (n + 1)) :
      (∑ j, (B (gs i) (gs j)).re) =
        (B (gs i) (gs i)).re +
          ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
            (B (gs i) (gs j)).re := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have hdef :
      AEGIS.RHActualMixedDefectV1.actualMixedDefect n gs =
        ∑ i, ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
          (B (gs i) (gs j)).re := by
    unfold AEGIS.RHActualMixedDefectV1.actualMixedDefect
    rw [Complex.re_sum]
    simp_rw [Complex.re_sum]
    simp_rw [hsplit]
    rw [Finset.sum_add_distrib]
    ring
  have hrows (i : Fin (n + 1)) :
      (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i, c i j) ≤ R :=
    hrow i
  have hoff :
      (∑ i, ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        (B (gs i) (gs j)).re) ≤
      ∑ i, ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        c i j * (E i + E j) := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j hj
    have hij : i ≠ j := by
      intro h
      exact (Finset.mem_erase.mp hj).1 h.symm
    calc
      (B (gs i) (gs j)).re ≤ ‖B (gs i) (gs j)‖ :=
        Complex.re_le_norm _
      _ ≤ c i j * (E i + E j) := hcross i j hij
  have hswap :
      (∑ i, ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        c i j * E j) =
      (∑ i, ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        c i j * E i) := by
    rw [AEGIS.RHGramExpansionV13.sum_erase_comm
      (fun i j => c i j * E j)]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hsym j i]
  have hfactor :
      (∑ i, ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        c i j * E i) =
      ∑ i, E i * (∑ j ∈
        (Finset.univ : Finset (Fin (n + 1))).erase i, c i j) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have htwo :
      (∑ i, ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        c i j * (E i + E j)) =
      2 * (∑ i, E i * (∑ j ∈
        (Finset.univ : Finset (Fin (n + 1))).erase i, c i j)) := by
    calc
      _ = (∑ i, ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
             c i j * E i) +
          (∑ i, ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
             c i j * E j) := by
            simp only [mul_add, Finset.sum_add_distrib]
      _ = 2 * (∑ i, E i * (∑ j ∈
           (Finset.univ : Finset (Fin (n + 1))).erase i, c i j)) := by
            rw [hswap]
            simp only [hfactor]
            ring
  have hrowtotal :
      (∑ i, E i * (∑ j ∈
        (Finset.univ : Finset (Fin (n + 1))).erase i, c i j)) ≤
      R * (∑ i, E i) := by
    calc
      _ ≤ ∑ i, E i * R := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left (hrows i)
          (energy_nonnegative (gs i).1)
      _ = R * (∑ i, E i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
  calc
    AEGIS.RHActualMixedDefectV1.actualMixedDefect n gs =
        (∑ i, ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
          (B (gs i) (gs j)).re) := hdef
    _ ≤ (∑ i, ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
          c i j * (E i + E j)) := hoff
    _ = 2 * (∑ i, E i * (∑ j ∈
          (Finset.univ : Finset (Fin (n + 1))).erase i, c i j)) := htwo
    _ ≤ 2 * (R * (∑ i, E i)) :=
        mul_le_mul_of_nonneg_left hrowtotal (by norm_num)
    _ = (2 * R) * (∑ i, energy (gs i).1) := by
        dsimp [E]
        ring

theorem actual_mixed_defect_le_of_signed_symmetric_row
    {n : ℕ} (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (c : Fin (n + 1) → Fin (n + 1) → ℝ) (R : ℝ)
    (hsym : ∀ i j, c i j = c j i)
    (hcross : ∀ i j, i ≠ j →
      (B (gs i) (gs j)).re ≤
        c i j * (energy (gs i).1 + energy (gs j).1))
    (hrow : ∀ i, (∑ j ∈
      (Finset.univ : Finset (Fin (n + 1))).erase i, c i j) ≤ R) :
    AEGIS.RHActualMixedDefectV1.actualMixedDefect n gs ≤
      (2 * R) * (∑ i, energy (gs i).1) := by
  let E : Fin (n + 1) → ℝ := fun i => energy (gs i).1
  have hsplit (i : Fin (n + 1)) :
      (∑ j, (B (gs i) (gs j)).re) =
        (B (gs i) (gs i)).re +
          ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
            (B (gs i) (gs j)).re := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have hdef :
      AEGIS.RHActualMixedDefectV1.actualMixedDefect n gs =
        ∑ i, ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
          (B (gs i) (gs j)).re := by
    unfold AEGIS.RHActualMixedDefectV1.actualMixedDefect
    rw [Complex.re_sum]
    simp_rw [Complex.re_sum]
    simp_rw [hsplit]
    rw [Finset.sum_add_distrib]
    ring
  have hrows (i : Fin (n + 1)) :
      (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i, c i j) ≤ R :=
    hrow i
  have hoff :
      (∑ i, ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        (B (gs i) (gs j)).re) ≤
      ∑ i, ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        c i j * (E i + E j) := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j hj
    have hij : i ≠ j := by
      intro h
      exact (Finset.mem_erase.mp hj).1 h.symm
    exact hcross i j hij
  have hswap :
      (∑ i, ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        c i j * E j) =
      (∑ i, ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        c i j * E i) := by
    rw [AEGIS.RHGramExpansionV13.sum_erase_comm
      (fun i j => c i j * E j)]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hsym j i]
  have hfactor :
      (∑ i, ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        c i j * E i) =
      ∑ i, E i * (∑ j ∈
        (Finset.univ : Finset (Fin (n + 1))).erase i, c i j) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have htwo :
      (∑ i, ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        c i j * (E i + E j)) =
      2 * (∑ i, E i * (∑ j ∈
        (Finset.univ : Finset (Fin (n + 1))).erase i, c i j)) := by
    calc
      _ = (∑ i, ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
             c i j * E i) +
          (∑ i, ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
             c i j * E j) := by
            simp only [mul_add, Finset.sum_add_distrib]
      _ = 2 * (∑ i, E i * (∑ j ∈
           (Finset.univ : Finset (Fin (n + 1))).erase i, c i j)) := by
            rw [hswap]
            simp only [hfactor]
            ring
  have hrowtotal :
      (∑ i, E i * (∑ j ∈
        (Finset.univ : Finset (Fin (n + 1))).erase i, c i j)) ≤
      R * (∑ i, E i) := by
    calc
      _ ≤ ∑ i, E i * R := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left (hrows i)
          (energy_nonnegative (gs i).1)
      _ = R * (∑ i, E i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
  calc
    AEGIS.RHActualMixedDefectV1.actualMixedDefect n gs =
        (∑ i, ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
          (B (gs i) (gs j)).re) := hdef
    _ ≤ (∑ i, ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
          c i j * (E i + E j)) := hoff
    _ = 2 * (∑ i, E i * (∑ j ∈
          (Finset.univ : Finset (Fin (n + 1))).erase i, c i j)) := htwo
    _ ≤ 2 * (R * (∑ i, E i)) :=
        mul_le_mul_of_nonneg_left hrowtotal (by norm_num)
    _ = (2 * R) * (∑ i, energy (gs i).1) := by
        dsimp [E]
        ring


/-- True signed Weil-Gram coercivity from a symmetric REAL row bound.
This strengthens the norm-based Q16 consumer without demanding that
off-diagonal prime contributions have a prescribed sign. -/
theorem actual_fine_gram_coercive_of_signed_real_row_certificate
    {n : ℕ} (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (c : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hsym : ∀ i j, c i j = c j i)
    (hdiag : ∀ i, (5671 / 3200 : ℝ) * energy (gs i).1 ≤
      -(B (gs i) (gs i)).re)
    (hcross : ∀ i j, i ≠ j →
      (B (gs i) (gs j)).re ≤
        c i j * (energy (gs i).1 + energy (gs j).1))
    (hrow : ∀ i, (∑ j ∈
      (Finset.univ : Finset (Fin (n + 1))).erase i,
      c i j) ≤ (57430 / 65536 : ℝ)) :
    (B (packetSum (fun _ => (1 : ℂ)) gs)
       (packetSum (fun _ => (1 : ℂ)) gs)).re ≤
        -(641 / 32768 : ℝ) * (∑ i, energy (gs i).1) := by
  have hmixed := actual_mixed_defect_le_of_signed_symmetric_row
    gs c (57430 / 65536 : ℝ) hsym hcross hrow
  have hlocal := fine_mixed_defect_lower_bound n gs hdiag
  have hgram :
      (B (packetSum (fun _ => (1 : ℂ)) gs)
         (packetSum (fun _ => (1 : ℂ)) gs)).re =
      (∑ i, ∑ j, B (gs i) (gs j)).re := by
    rw [AEGIS.RHGramExpansionV13.B_packetSum]
    simp
  rw [← hgram] at hlocal
  have hE : 0 ≤ (∑ i, energy (gs i).1) :=
    Finset.sum_nonneg (fun i _ => energy_nonnegative (gs i).1)
  have hround :
      (116142 / 65536 : ℝ) * (∑ i, energy (gs i).1) ≤
        (5671 / 3200 : ℝ) * (∑ i, energy (gs i).1) :=
    mul_le_mul_of_nonneg_right (by norm_num) hE
  linarith

/-! ## Dimension-free Q16.16 bound on the summed moment-zero Arch envelope

Do not round the Arch component separately for each off-diagonal entry.
The actual remainder-to-geometric majorization has to be established
independently, and the true prime term is not controlled here.
-/

/-- The symmetric geometric envelope from a moment-zero separated Arch
kernel has a rational row bound uniform in the number of packets.
This discharges the arithmetic FINITE ROW part of the Arch tail budget,
without assuming a finite bound on n. -/
theorem geometric_arch_row_q16 {n : ℕ} (i : Fin (n + 1)) :
    (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
      (13 / 384 : ℝ) * ((2 / 37 : ℝ) ^ Nat.dist i j)) ≤
      (254 / 65536 : ℝ) := by
  have hgeom : (∑ k ∈ Finset.Icc 1 n, ((2 / 37 : ℝ) ^ k)) ≤
      (2 / 35 : ℝ) := by
    have hIcc :
        (Finset.Icc 1 n : Finset ℕ) = Finset.Ico 1 (n + 1) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega
    rw [hIcc]
    have h := geom_sum_Ico_le_of_lt_one
      (m := 1) (n := n + 1) (x := (2 / 37 : ℝ))
      (by norm_num) (by norm_num)
    norm_num at h ⊢
    exact h
  have hcost : (∑ k ∈ Finset.Icc 1 n,
        (13 / 384 : ℝ) * ((2 / 37 : ℝ) ^ k)) ≤
        (13 / 384 : ℝ) * (2 / 35 : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hgeom
      (by norm_num : (0 : ℝ) ≤ 13 / 384)
    simpa only [Finset.mul_sum] using h
  have hrow := AEGIS.RHGramExpansionV13.rowSum_le
    (n := n) (c := fun k => (13 / 384 : ℝ) *
      ((2 / 37 : ℝ) ^ k))
    (by intro k; positivity) i
  have hbound :
      (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        (13 / 384 : ℝ) * ((2 / 37 : ℝ) ^ Nat.dist i j)) ≤
          2 * ((13 / 384 : ℝ) * (2 / 35 : ℝ)) := by
    exact hrow.trans (mul_le_mul_of_nonneg_left hcost
      (by norm_num : (0 : ℝ) ≤ 2))
  nlinarith


/-- The true Weil Gram is coercive for an arbitrary-size packet family
whenever its genuine von Mangoldt terms admit a symmetric real prime
row budget and its genuine Arch terms obey the geometric envelope.
Both analytic hypotheses remain visible; there is NO universal
certificate producer or unconditional RH assertion here. -/
theorem actual_fine_gram_coercive_of_summable_arch_prime_row
    {n : ℕ} (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (primeCost : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hsym : ∀ i j, primeCost i j = primeCost j i)
    (hdiag : ∀ i, (5671 / 3200 : ℝ) * energy (gs i).1 ≤
      -(B (gs i) (gs i)).re)
    (hprime : ∀ i j, i ≠ j →
      ‖WeilPrimeSumV1 (mixed (gs i) (gs j))‖ ≤
        primeCost i j * (energy (gs i).1 + energy (gs j).1))
    (harch : ∀ i j, i ≠ j →
      ‖B (gs i) (gs j)‖ ≤
        ‖WeilPrimeSumV1 (mixed (gs i) (gs j))‖ +
        ((13 / 384 : ℝ) * ((2 / 37 : ℝ) ^ Nat.dist i j)) *
          (energy (gs i).1 + energy (gs j).1))
    (hprimeRow : ∀ i, (∑ j ∈
      (Finset.univ : Finset (Fin (n + 1))).erase i,
      primeCost i j) ≤ (57176 / 65536 : ℝ)) :
    (B (packetSum (fun _ => (1 : ℂ)) gs)
       (packetSum (fun _ => (1 : ℂ)) gs)).re ≤
        -(641 / 32768 : ℝ) * (∑ i, energy (gs i).1) := by
  let c : Fin (n + 1) → Fin (n + 1) → ℝ := fun i j =>
    primeCost i j + (13 / 384 : ℝ) * ((2 / 37 : ℝ) ^ Nat.dist i j)
  have hc : ∀ i j, c i j = c j i := by
    intro i j
    dsimp [c]
    rw [hsym i j, Nat.dist_comm i j]
  have hcost : ∀ i j, i ≠ j →
      ‖B (gs i) (gs j)‖ ≤
        c i j * (energy (gs i).1 + energy (gs j).1) := by
    intro i j hij
    dsimp [c]
    calc
      ‖B (gs i) (gs j)‖ ≤
          ‖WeilPrimeSumV1 (mixed (gs i) (gs j))‖ +
          ((13 / 384 : ℝ) * ((2 / 37 : ℝ) ^ Nat.dist i j)) *
          (energy (gs i).1 + energy (gs j).1) := harch i j hij
      _ ≤ primeCost i j * (energy (gs i).1 + energy (gs j).1) +
          ((13 / 384 : ℝ) * ((2 / 37 : ℝ) ^ Nat.dist i j)) *
          (energy (gs i).1 + energy (gs j).1) :=
            add_le_add (hprime i j hij) le_rfl
      _ = (primeCost i j +
            (13 / 384 : ℝ) * ((2 / 37 : ℝ) ^ Nat.dist i j)) *
          (energy (gs i).1 + energy (gs j).1) := by ring
  have hrowc : ∀ i, (∑ j ∈
      (Finset.univ : Finset (Fin (n + 1))).erase i, c i j) ≤
        (57430 / 65536 : ℝ) := by
    intro i
    have hsplit :
        (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i, c i j) =
          (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
            primeCost i j) +
          (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
            (13 / 384 : ℝ) * ((2 / 37 : ℝ) ^ Nat.dist i j)) := by
      simp only [c, Finset.sum_add_distrib]
    rw [hsplit]
    have hp := hprimeRow i
    have ha := geometric_arch_row_q16 i
    linarith
  have hmixed := actual_mixed_defect_le_of_real_symmetric_row
    gs c (57430 / 65536 : ℝ) hc hcost hrowc
  have hlocal := fine_mixed_defect_lower_bound n gs hdiag
  have hgram :
      (B (packetSum (fun _ => (1 : ℂ)) gs)
         (packetSum (fun _ => (1 : ℂ)) gs)).re =
      (∑ i, ∑ j, B (gs i) (gs j)).re := by
    rw [AEGIS.RHGramExpansionV13.B_packetSum]
    simp
  rw [← hgram] at hlocal
  have hE : 0 ≤ (∑ i, energy (gs i).1) :=
    Finset.sum_nonneg (fun i _ => energy_nonnegative (gs i).1)
  have hround :
      (116142 / 65536 : ℝ) * (∑ i, energy (gs i).1) ≤
        (5671 / 3200 : ℝ) * (∑ i, energy (gs i).1) :=
    mul_le_mul_of_nonneg_right (by norm_num) hE
  linarith


/-- A closed finite-dimensional REAL Schur consumer of the already
formalized moment-zero geometric Arch estimate. Every genuine Weil
off-diagonal term is retained. Prime-side row majorants and ordered
logarithmic separation are the only remaining analytic/geometric inputs.
The pairwise Arch bound is derived, not postulated. -/
theorem actual_far_fine_gram_coercive_of_geometric_arch_prime_row
    {n : ℕ} (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (center : Fin (n + 1) → ℝ)
    (hw : ∀ i, AEGIS.RHRationalNinePacketPrimeWindowV1.WidthOneOneTwentyEightAt
      (gs i) (center i))
    (hm : ∀ i, WeilMomentConditionsV1 (gs i))
    (hsep : ∀ i j : Fin (n + 1), i < j →
      1 ≤ Nat.dist i j ∧
      (65 / 32 : ℝ) * (Nat.dist i j : ℝ) ≤ center j - center i)
    (primeCost : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hsym : ∀ i j, primeCost i j = primeCost j i)
    (hprime : ∀ i j : Fin (n + 1), i < j →
      ‖WeilPrimeSumV1 (mixed (gs i) (gs j))‖ ≤
        primeCost i j * (energy (gs i).1 + energy (gs j).1))
    (hprimeRow : ∀ i, (∑ j ∈
      (Finset.univ : Finset (Fin (n + 1))).erase i,
      primeCost i j) ≤ (57176 / 65536 : ℝ)) :
    (B (packetSum (fun _ => (1 : ℂ)) gs)
       (packetSum (fun _ => (1 : ℂ)) gs)).re ≤
        -(641 / 32768 : ℝ) * (∑ i, energy (gs i).1) := by
  let c : Fin (n + 1) → Fin (n + 1) → ℝ := fun i j =>
    primeCost i j + (13 / 384 : ℝ) * ((2 / 37 : ℝ) ^ Nat.dist i j)
  have hc : ∀ i j, c i j = c j i := by
    intro i j
    dsimp [c]
    rw [hsym i j, Nat.dist_comm i j]
  have hforward (i j : Fin (n + 1)) (hij : i < j) :
      ‖B (gs i) (gs j)‖ ≤
        c i j * (energy (gs i).1 + energy (gs j).1) := by
    obtain ⟨hk, hgap⟩ := hsep i j hij
    have hb :=
      AEGIS.RHActualMixedDefectV1.distinct_fine_far_actual_B_norm_le_prime_plus_geometric_arch
        (gs i) (gs j) (center i) (center j)
        (hw i) (hw j) (hm i)
        (Nat.dist i j) hk hgap
    dsimp [c]
    calc
      ‖B (gs i) (gs j)‖ ≤
          ‖WeilPrimeSumV1 (mixed (gs i) (gs j))‖ +
          ((13 / 384 : ℝ) * ((2 / 37 : ℝ) ^ Nat.dist i j)) *
            (energy (gs i).1 + energy (gs j).1) := hb
      _ ≤ primeCost i j * (energy (gs i).1 + energy (gs j).1) +
          ((13 / 384 : ℝ) * ((2 / 37 : ℝ) ^ Nat.dist i j)) *
            (energy (gs i).1 + energy (gs j).1) :=
              add_le_add (hprime i j hij) le_rfl
      _ = (primeCost i j +
            (13 / 384 : ℝ) * ((2 / 37 : ℝ) ^ Nat.dist i j)) *
          (energy (gs i).1 + energy (gs j).1) := by ring
  have hcross : ∀ i j, i ≠ j →
      ‖B (gs i) (gs j)‖ ≤
        c i j * (energy (gs i).1 + energy (gs j).1) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with hijlt | hjilt
    · exact hforward i j hijlt
    · have hb := hforward j i hjilt
      rw [B_hermitian, norm_conj]
      simpa only [hc j i,
        add_comm (energy (gs j).1) (energy (gs i).1)] using hb
  have hrowc : ∀ i, (∑ j ∈
      (Finset.univ : Finset (Fin (n + 1))).erase i, c i j) ≤
        (57430 / 65536 : ℝ) := by
    intro i
    calc
      (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
          c i j) =
        (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
          primeCost i j) +
        (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
          (13 / 384 : ℝ) * ((2 / 37 : ℝ) ^ Nat.dist i j)) := by
            simp only [c, Finset.sum_add_distrib]
      _ ≤ (57176 / 65536 : ℝ) + (254 / 65536 : ℝ) :=
        add_le_add (hprimeRow i) (geometric_arch_row_q16 i)
      _ = (57430 / 65536 : ℝ) := by norm_num
  have hmixed := actual_mixed_defect_le_of_real_symmetric_row
    gs c (57430 / 65536 : ℝ) hc hcross hrowc
  have hdiag : ∀ i, (5671 / 3200 : ℝ) * energy (gs i).1 ≤
      -(B (gs i) (gs i)).re := by
    intro i
    exact AEGIS.RHFineDiagonalUpgradeV3.fine_diagonal_5671_over_3200_v3
      (gs i) (center i) (hw i)
  have hlocal := fine_mixed_defect_lower_bound n gs hdiag
  have hgram :
      (B (packetSum (fun _ => (1 : ℂ)) gs)
         (packetSum (fun _ => (1 : ℂ)) gs)).re =
      (∑ i, ∑ j, B (gs i) (gs j)).re := by
    rw [AEGIS.RHGramExpansionV13.B_packetSum]
    simp
  rw [← hgram] at hlocal
  have hE : 0 ≤ (∑ i, energy (gs i).1) :=
    Finset.sum_nonneg (fun i _ => energy_nonnegative (gs i).1)
  have hround :
      (116142 / 65536 : ℝ) * (∑ i, energy (gs i).1) ≤
        (5671 / 3200 : ℝ) * (∑ i, energy (gs i).1) :=
    mul_le_mul_of_nonneg_right (by norm_num) hE
  linarith



/-! ## Exact final consumer: one genuine signed certificate per packet

This is a genuine assembly into the existing canonical RH statement.
Every source packet uses its own finite decomposition: no uniform number
of pieces and no far-separated reconstruction are presumed.

The existential mixed-defect budget is strictly less demanding than the
earlier statement quantifying over ALL decompositions. Its production
remains an explicit universal arithmetic obligation. The signed-row
version preserves favorable negative REAL Weil mixed interference.
Neither theorem asserts its hypothesis without proof.
-/

/-- ONE source-exact finite moment-zero Gram with a sufficiently controlled
actual mixed defect has the genuine arithmetic Weil sign. -/
theorem actual_sign_of_one_fine_mixed_budget
    {n : ℕ} (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (hd : ∀ i, (5671 / 3200 : ℝ) * energy (gs i).1 ≤
      -(B (gs i) (gs i)).re)
    (hbudget : AEGIS.RHActualMixedDefectV1.actualMixedDefect n gs ≤
      (5671 / 3200 : ℝ) * (∑ i, energy (gs i).1)) :
    (B (packetSum (fun _ => (1 : ℂ)) gs)
       (packetSum (fun _ => (1 : ℂ)) gs)).re ≤ 0 := by
  have hlo := fine_mixed_defect_lower_bound n gs hd
  have hgram :
      (B (packetSum (fun _ => (1 : ℂ)) gs)
        (packetSum (fun _ => (1 : ℂ)) gs)).re =
      (∑ i, ∑ j, B (gs i) (gs j)).re := by
    rw [AEGIS.RHGramExpansionV13.B_packetSum]
    simp
  rw [← hgram] at hlo
  linarith

/-- Kernel-facing terminal: an independently witnessed actual mixed budget
for each arbitrary source moment-zero packet implies the canonical RH. -/
theorem riemannHypothesis_of_one_actual_mixed_budget_per_packet
    (hcert : ∀ (g : WeilCompactSmoothGV1),
      WeilMomentConditionsV1 g →
      ∃ (n : ℕ) (gs : Fin (n + 1) → WeilCompactSmoothGV1),
        g = packetSum (fun _ => (1 : ℂ)) gs ∧
        (∀ i, (5671 / 3200 : ℝ) * energy (gs i).1 ≤
          -(B (gs i) (gs i)).re) ∧
        AEGIS.RHActualMixedDefectV1.actualMixedDefect n gs ≤
          (5671 / 3200 : ℝ) * (∑ i, energy (gs i).1)) :
    RiemannHypothesis := by
  apply AEGIS.RHRestrictedWeilBridgeV13.final_sign_implies_rh_v13
  intro g hm
  obtain ⟨n, gs, hg, hd, hbudget⟩ := hcert g hm
  have hsign := actual_sign_of_one_fine_mixed_budget gs hd hbudget
  rw [hg]
  change (B (packetSum (fun _ => (1 : ℂ)) gs)
    (packetSum (fun _ => (1 : ℂ)) gs)).re ≤ 0
  exact hsign

/-- Signed-real row producer, allowing negative cross interference.
Unlike norm-only pair certificates, it bounds actual real Weil B. The
finite family and its source identity may depend on each g. -/
theorem riemannHypothesis_of_universal_actual_signed_row_certificates
    (hcert : ∀ (g : WeilCompactSmoothGV1),
      WeilMomentConditionsV1 g →
      ∃ (n : ℕ) (gs : Fin (n + 1) → WeilCompactSmoothGV1),
        g = packetSum (fun _ => (1 : ℂ)) gs ∧
        (∀ i, (5671 / 3200 : ℝ) * energy (gs i).1 ≤
          -(B (gs i) (gs i)).re) ∧
        ∃ c : Fin (n + 1) → Fin (n + 1) → ℝ,
          (∀ i j, c i j = c j i) ∧
          (∀ i j, i ≠ j →
            (B (gs i) (gs j)).re ≤
              c i j * (energy (gs i).1 + energy (gs j).1)) ∧
          (∀ i, (∑ j ∈
            (Finset.univ : Finset (Fin (n + 1))).erase i,
            c i j) ≤ (57430 / 65536 : ℝ))) :
    RiemannHypothesis := by
  apply AEGIS.RHRestrictedWeilBridgeV13.final_sign_implies_rh_v13
  intro g hm
  obtain ⟨n, gs, hg, hd, c, hsym, hcross, hrow⟩ := hcert g hm
  have hbound := actual_fine_gram_coercive_of_signed_real_row_certificate
    gs c hsym hd hcross hrow
  have hE : 0 ≤ (∑ i, energy (gs i).1) :=
    Finset.sum_nonneg (fun i _ => energy_nonnegative (gs i).1)
  rw [hg]
  change (B (packetSum (fun _ => (1 : ℂ)) gs)
    (packetSum (fun _ => (1 : ℂ)) gs)).re ≤ 0
  linarith

private theorem separated_centers_dist {n : ℕ} (center : Fin (n + 1) → ℝ)
    (hsep : ∀ i j : Fin (n + 1), i < j →
      (65 / 32 : ℝ) ≤ center j - center i) :
    ∀ i j : Fin (n + 1), i < j →
      1 ≤ Nat.dist i j ∧
      (65 / 32 : ℝ) * (Nat.dist i j : ℝ) ≤ center j - center i := by
  have hscaled (i j : Fin (n + 1)) (hij : i ≤ j) :
      (65 / 32 : ℝ) * ((j.val : ℝ) - (i.val : ℝ)) ≤ center j - center i := by
    induction j using Fin.induction with
    | zero =>
      have hi : i = 0 := by
        apply Fin.ext
        have hz : i.val ≤ 0 := hij
        simpa using Nat.eq_zero_of_le_zero hz
      subst i
      simp
    | succ j ih =>
      by_cases heq : i = j.succ
      · subst i
        simp
      · have hiprev : i ≤ j.castSucc := by
          simp only [Fin.le_iff_val_le_val, Fin.val_succ, Fin.val_castSucc] at hij ⊢
          have hne : i.val ≠ j.val + 1 := by
            intro he
            apply heq
            exact Fin.ext he
          omega
        have hp := ih hiprev
        have hs := hsep j.castSucc j.succ (Fin.castSucc_lt_succ)
        simp only [Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one] at hp ⊢
        linarith
  intro i j hij
  have hijval : i.val < j.val := hij
  have hi : i.val ≤ j.val := Nat.le_of_lt hijval
  have hd : Nat.dist i.val j.val = j.val - i.val := Nat.dist_eq_sub_of_le hi
  refine ⟨?_, ?_⟩
  · rw [hd]
    omega
  rw [hd, Nat.cast_sub hi]
  exact hscaled i j (le_of_lt hij)


/-- All actual distant off-diagonal entries of an arbitrary finite fine
moment-zero packet family can be certified by prime-side integer Q16.16
costs plus a whole-row rational Archimedean allowance of 120 units.
The proof uses the sharper geometric Arch-29 bound for the complete row.

The ordered centers are separated by 65/32 in log coordinates.
The *only* analytic mixed estimate required from the caller is on the
genuine von Mangoldt prime sum. In particular, no actual-Weil \`hcross\`
is assumed and all off-diagonal entries are retained.

This is a finite separated-family theorem. It does not assert that every
Weil packet has a reconstruction satisfying its separation or prime-budget
hypotheses. -/
theorem actual_far_fine_gram_coercive_of_rational_prime_row_budget
    {n : ℕ} (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (center : Fin (n + 1) → ℝ)
    (hw : ∀ i, AEGIS.RHRationalNinePacketPrimeWindowV1.WidthOneOneTwentyEightAt
      (gs i) (center i))
    (hm : ∀ i, WeilMomentConditionsV1 (gs i))
    (hsep : ∀ i j : Fin (n + 1), i < j →
      (65 / 32 : ℝ) ≤ center j - center i)
    (primeCost : Fin (n + 1) → Fin (n + 1) → ℕ)
    (hsym : ∀ i j, primeCost i j = primeCost j i)
    (hprime : ∀ i j : Fin (n + 1), i < j →
      ‖WeilPrimeSumV1 (mixed (gs i) (gs j))‖ ≤
        ((primeCost i j : ℝ) / 65536) *
          (energy (gs i).1 + energy (gs j).1))
    (hrow : ∀ i, (∑ j ∈
      (Finset.univ : Finset (Fin (n + 1))).erase i,
        primeCost i j + 120) ≤ 57430) :
    (B (packetSum (fun _ => (1 : ℂ)) gs)
      (packetSum (fun _ => (1 : ℂ)) gs)).re ≤
        -(641 / 32768 : ℝ) * (∑ i, energy (gs i).1) := by
  let c : Fin (n + 1) → Fin (n + 1) → ℝ := fun i j =>
    ((primeCost i j : ℝ) / 65536) +
      ((1 / 32 : ℝ) * (54 / 53)) * ((1 / 145 : ℝ) ^ Nat.dist i j)
  have hc : ∀ i j, c i j = c j i := by
    intro i j
    dsimp [c]
    rw [hsym i j, Nat.dist_comm i j]
  have hforward (i j : Fin (n + 1)) (hij : i < j) :
      ‖B (gs i) (gs j)‖ ≤
        c i j * (energy (gs i).1 + energy (gs j).1) := by
    obtain ⟨hk, hgap⟩ := separated_centers_dist center hsep i j hij
    have ha := AEGIS.RHArchRow29V1.actual_B_norm_le_prime_plus_arch145
      (gs i) (gs j) (center i) (center j)
      (hw i) (hw j) (hm i) (Nat.dist i j) hk hgap
    dsimp [c]
    calc
      ‖B (gs i) (gs j)‖ ≤
          ‖WeilPrimeSumV1 (mixed (gs i) (gs j))‖ +
          (((1 / 32 : ℝ) * (54 / 53)) *
            ((1 / 145 : ℝ) ^ Nat.dist i j)) *
              (energy (gs i).1 + energy (gs j).1) := ha
      _ ≤ ((primeCost i j : ℝ) / 65536) * (energy (gs i).1 + energy (gs j).1) +
          (((1 / 32 : ℝ) * (54 / 53)) *
            ((1 / 145 : ℝ) ^ Nat.dist i j)) *
              (energy (gs i).1 + energy (gs j).1) :=
        add_le_add (hprime i j hij) le_rfl
      _ = (((primeCost i j : ℝ) / 65536) +
            ((1 / 32 : ℝ) * (54 / 53)) *
              ((1 / 145 : ℝ) ^ Nat.dist i j)) *
            (energy (gs i).1 + energy (gs j).1) := by ring
  have hcross : ∀ i j, i ≠ j →
      ‖B (gs i) (gs j)‖ ≤
        c i j * (energy (gs i).1 + energy (gs j).1) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with hijlt | hjilt
    · exact hforward i j hijlt
    · have hb := hforward j i hjilt
      rw [B_hermitian, norm_conj]
      simpa only [hc j i,
        add_comm (energy (gs j).1) (energy (gs i).1)] using hb

  have hprimeRow : ∀ i, (∑ j ∈
      (Finset.univ : Finset (Fin (n + 1))).erase i,
      ((primeCost i j : ℝ) / 65536)) ≤ (57310 / 65536 : ℝ) := by
    intro i
    have hnat : (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        primeCost i j) ≤ 57310 := by
      have hi := hrow i
      omega
    have hreal : (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        (primeCost i j : ℝ)) ≤ (57310 : ℝ) := by
      exact_mod_cast hnat
    simpa only [Finset.sum_div] using (div_le_div_of_nonneg_right hreal (by norm_num : (0 : ℝ) ≤ 65536))
  have hcostrow : ∀ i, (∑ j ∈
      (Finset.univ : Finset (Fin (n + 1))).erase i,
      c i j) ≤ (57430 / 65536 : ℝ) := by
    intro i
    calc
      (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i, c i j) =
        (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
          ((primeCost i j : ℝ) / 65536)) +
        (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
          ((1 / 32 : ℝ) * (54 / 53)) *
            ((1 / 145 : ℝ) ^ Nat.dist i j)) := by
          simp only [c, Finset.sum_add_distrib]
      _ ≤ (57310 / 65536 : ℝ) + (29 / 65536 : ℝ) :=
        add_le_add (hprimeRow i) (AEGIS.RHArchRow29V1.geometric_arch_row_29 i)
      _ ≤ (57430 / 65536 : ℝ) := by norm_num
  have hd : ∀ i, (5671 / 3200 : ℝ) * energy (gs i).1 ≤
      -(B (gs i) (gs i)).re := by
    intro i
    exact AEGIS.RHFineDiagonalUpgradeV3.fine_diagonal_5671_over_3200_v3
      (gs i) (center i) (hw i)
  apply AEGIS.RHActualUniversalFineGramV1.actual_fine_gram_coercive_of_signed_real_row_certificate
    gs c hc hd
  · intro i j hij
    exact ((le_abs_self (B (gs i) (gs j)).re).trans
      (Complex.abs_re_le_norm (B (gs i) (gs j)))).trans (hcross i j hij)
  · exact hcostrow



end AEGIS.RHActualUniversalFineGramV1

#print axioms AEGIS.RHActualUniversalFineGramV1.every_moment_zero_packet_actual_fine_gram

#print axioms AEGIS.RHActualUniversalFineGramV1.fine_mixed_defect_lower_bound
#print axioms AEGIS.RHActualUniversalFineGramV1.every_packet_actual_fine_mixed_defect_lower_bound

#print axioms AEGIS.RHActualUniversalFineGramV1.riemannHypothesis_of_uniform_actual_fine_mixed_budget

#print axioms AEGIS.RHActualUniversalFineGramV1.actual_mixed_defect_le_of_q16_matrix
#print axioms AEGIS.RHActualUniversalFineGramV1.actual_fine_gram_q16_coercive_of_pair_certificate
#print axioms AEGIS.RHActualUniversalFineGramV1.riemannHypothesis_of_universal_actual_q16_pair_certificates
#print axioms AEGIS.RHActualUniversalFineGramV1.actual_far_fine_gram_coercive_of_rational_prime_row_budget

#print axioms AEGIS.RHActualUniversalFineGramV1.geometric_arch_row_q16

#print axioms AEGIS.RHActualUniversalFineGramV1.actual_mixed_defect_le_of_real_symmetric_row
#print axioms AEGIS.RHActualUniversalFineGramV1.actual_fine_gram_coercive_of_summable_arch_prime_row

#print axioms AEGIS.RHActualUniversalFineGramV1.actual_far_fine_gram_coercive_of_geometric_arch_prime_row

#print axioms AEGIS.RHActualUniversalFineGramV1.actual_mixed_defect_le_of_signed_symmetric_row
#print axioms AEGIS.RHActualUniversalFineGramV1.actual_fine_gram_coercive_of_signed_real_row_certificate

#print axioms AEGIS.RHActualUniversalFineGramV1.every_moment_zero_packet_actual_fine_gram_at_radius
#print axioms AEGIS.RHActualUniversalFineGramV1.every_moment_zero_packet_actual_fine_gram_with_support

#print axioms AEGIS.RHActualUniversalFineGramV1.actual_sign_of_one_fine_mixed_budget
#print axioms AEGIS.RHActualUniversalFineGramV1.riemannHypothesis_of_one_actual_mixed_budget_per_packet
#print axioms AEGIS.RHActualUniversalFineGramV1.riemannHypothesis_of_universal_actual_signed_row_certificates
