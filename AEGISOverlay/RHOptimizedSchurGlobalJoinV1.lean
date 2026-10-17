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
import AEGISOverlay.RHFourBlockIntegerWeightedSchurV1
import RHKreinTrigramAdaptiveV1
import AEGISOverlay.RHTimeSliceWeilV1
import AEGISOverlay.RHLogThreeSignedPrimeProducerV1
import WeilRHImpliesFinalSignV13
import Mathlib.Algebra.Order.Field.GeomSum
import AEGISOverlay.H64ZetaMappingAuditV1

/-!
# Optimized actual Weil–Schur global join

This module composes the EXISTING arbitrary-packet fine Gram constructor with
the EXISTING optimized weighted-Schur bound, using the genuine Weil pairing.
The optimized Q16.16 diagonal-minus-row margin is 34727/32768.

The universal mathematical input is the explicit producer `hselect`,
which selects a reconstruction with certified actual off-diagonal entries.
The premise is NOT constructed here. In particular, this module does not
assert unconditional RiemannHypothesis or provide an upstream formal_proof.
-/

open Finset
open scoped BigOperators
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHOptimizedSchurGlobalJoinV1

open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilDisjointEnergyV2
open AEGIS.RHGramExpansionV13

/-! ## Sharp scalar signed-defect route (no Schur or absolute-row assumption)

The actual mixed defect has an exact scalar criterion, irrespective of
the energies and relative locations of the atoms. This is strictly weaker
than the conservative 5671/3200 energy budget as a sufficient condition.
It is an identity, not a universal arithmetic estimate. The cluster
producer below supplies the exact budget on its proved domain.
-/

/-- Necessary and sufficient exact signed mixed budget for the genuine
finite Weil Gram, with no diagonal coercivity or matrix norm assumptions. -/
theorem actual_signed_defect_iff_packet_nonpositive
    {n : ℕ} (gs : Fin (n + 1) → WeilCompactSmoothGV1) :
    AEGIS.RHActualMixedDefectV1.actualMixedDefect n gs ≤
      -(∑ i, (B (gs i) (gs i)).re) ↔
    (B (packetSum (fun _ => (1 : ℂ)) gs)
      (packetSum (fun _ => (1 : ℂ)) gs)).re ≤ 0 := by
  have hgram :
      (B (packetSum (fun _ => (1 : ℂ)) gs)
        (packetSum (fun _ => (1 : ℂ)) gs)).re =
      (∑ i, ∑ j, B (gs i) (gs j)).re := by
    rw [B_packetSum]
    simp
  rw [hgram]
  unfold AEGIS.RHActualMixedDefectV1.actualMixedDefect
  constructor <;> intro h <;> linarith

/-- Source-proved 9/64 cluster coercivity pays the exact signed budget.
No absolute values, weights or pairwise row bounds occur in the statement.
The common-center geometric hypothesis is preserved without weakening. -/
theorem actual_fine_cluster_sharp_signed_budget
    (n : ℕ) (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (centers : Fin (n + 1) → ℝ) (center : ℝ)
    (hm : ∀ i, WeilMomentConditionsV1 (gs i))
    (hw : ∀ i, AEGIS.RHRationalNinePacketPrimeWindowV1.WidthOneOneTwentyEightAt
      (gs i) (centers i))
    (hnear : ∀ i, |centers i - center| ≤ (35 / 256 : ℝ)) :
    AEGIS.RHActualMixedDefectV1.actualMixedDefect n gs ≤
      -(∑ i, (B (gs i) (gs i)).re) := by
  have h := AEGIS.RHActualMixedDefectV1.fine_cluster_nine_mixed_defect_opposite
    n gs centers center hm hw hnear
  have hE : 0 ≤ energy (packetSum (fun _ => (1 : ℂ)) gs).1 :=
    energy_nonnegative _
  linarith

/-- The existing optimized bound makes one actual reconstructed packet
nonpositive once the genuine mixed-entry and weighted-row estimates are
available. Unequal atom energies and arbitrary finite dimension are allowed. -/
theorem actual_packet_sum_nonpositive_of_optimized_rows
    {n : ℕ}
    (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (c : Fin (n + 1) → Fin (n + 1) → ℝ)
    (w : Fin (n + 1) → ℝ)
    (hc : ∀ i j, 0 ≤ c i j)
    (hzero : ∀ i, c i i = 0)
    (hsym : ∀ i j, c i j = c j i)
    (hw : ∀ i, 0 < w i)
    (hd : ∀ i, (5671 / 3200 : ℝ) * energy (gs i).1 ≤
      -(B (gs i) (gs i)).re)
    (hcross : ∀ i j, i ≠ j →
      ‖B (gs i) (gs j)‖ ≤ c i j *
        (Real.sqrt (energy (gs i).1) *
          Real.sqrt (energy (gs j).1)))
    (hrow : ∀ i, ∑ j, c i j * (w j / w i) ≤
      (46688 / 65536 : ℝ)) :
    (B (packetSum (fun _ => (1 : ℂ)) gs)
      (packetSum (fun _ => (1 : ℂ)) gs)).re ≤ 0 := by
  have hopt :=
    AEGIS.RHScaleRowCompositionV1.actual_optimized_weighted_schur_unequal_energy_from_fine_diagonals
      gs (fun _ => (1 : ℂ)) c w hc hzero hsym hw hd hcross hrow
  have henergy :
      0 ≤ ∑ i : Fin (n + 1), energy (gs i).1 * ‖(1 : ℂ)‖ ^ 2 :=
    Finset.sum_nonneg (fun i _ =>
      mul_nonneg (energy_nonnegative (gs i).1) (sq_nonneg _))
  have hnonpos :
      -(34727 / 32768 : ℝ) *
        (∑ i : Fin (n + 1), energy (gs i).1 * ‖(1 : ℂ)‖ ^ 2) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by norm_num) henergy
  exact hopt.trans hnonpos

/-- Universal sign consumer using a *selected* finite reconstruction, not
an arbitrary partition. The starting geometry and actual Weil Gram are
constructed by the existing source theorem. The explicit hselect obligation
may replace that partition with one certified weighted-Schur reconstruction.

This choice of quantifiers is essential: arbitrary fine decompositions may
contain repeated or nearly identical atoms and need not satisfy a strict
off-diagonal row budget. No universal analytic producer is assumed proved. -/
theorem riemannHypothesis_of_optimized_actual_row_producer
    (hselect :
      ∀ (g : WeilCompactSmoothGV1)
        (_hm : WeilMomentConditionsV1 g)
        (n : ℕ)
        (gs : Fin (n + 1) → WeilCompactSmoothGV1)
        (center : Fin (n + 1) → ℝ),
        (∀ i, AEGIS.RHRationalNinePacketPrimeWindowV1.WidthOneOneTwentyEightAt
          (gs i) (center i)) →
        (∀ i, (5671 / 3200 : ℝ) * energy (gs i).1 ≤
          -(B (gs i) (gs i)).re) →
        g = packetSum (fun _ => (1 : ℂ)) gs →
        ∃ (m : ℕ) (selected : Fin (m + 1) → WeilCompactSmoothGV1),
          g = packetSum (fun _ => (1 : ℂ)) selected ∧
          (∀ i, (5671 / 3200 : ℝ) * energy (selected i).1 ≤
            -(B (selected i) (selected i)).re) ∧
          ∃ (c : Fin (m + 1) → Fin (m + 1) → ℝ)
            (w : Fin (m + 1) → ℝ),
            (∀ i j, 0 ≤ c i j) ∧
            (∀ i, c i i = 0) ∧
            (∀ i j, c i j = c j i) ∧
            (∀ i, 0 < w i) ∧
            (∀ i j, i ≠ j →
              ‖B (selected i) (selected j)‖ ≤ c i j *
                (Real.sqrt (energy (selected i).1) *
                  Real.sqrt (energy (selected j).1))) ∧
            (∀ i, ∑ j, c i j * (w j / w i) ≤
              (46688 / 65536 : ℝ))) :
    RiemannHypothesis := by
  apply AEGIS.RHRestrictedWeilBridgeV13.final_sign_implies_rh_v13
  intro g hm
  obtain ⟨n, gs, center, _hmom, hd, hwidth, hpacket, _hgram⟩ :=
    AEGIS.RHActualUniversalFineGramV1.every_moment_zero_packet_actual_fine_gram_with_support g hm
  obtain ⟨m, selected, hselected, hdiag, c, w, hc, hzero, hsym, hw,
    hcross, hrow⟩ :=
    hselect g hm n gs center hwidth hd hpacket
  have hsign :=
    actual_packet_sum_nonpositive_of_optimized_rows
      selected c w hc hzero hsym hw hdiag hcross hrow
  rw [hselected]
  change (B (packetSum (fun _ => (1 : ℂ)) selected)
    (packetSum (fun _ => (1 : ℂ)) selected)).re ≤ 0
  exact hsign


/-! ## Certified-window fine Gram: same reconstruction, aligned sign

The UNIVERSAL fine partition exists for every moment-zero packet.
The signed Weil bound below is additionally available on the already
proved 693/2000 source window. Both certificates are attached to the
SAME actual reconstructed Gram, without replacing any real mixed term.
No statement about a source outside this window is made here.
-/

/-- For each moment-zero source in the certified 693/2000 log-window,
one actual fine decomposition simultaneously enjoys exact packet
reconstruction, exact full real Weil Gram, strong fine diagonals,
source-specific width control, and the SHARP signed mixed budget.
This aligns the existing universal fine-Gram constructor with the
existing unconditional narrow-window arithmetic sign theorem. -/
theorem certified_window_fine_gram_signed_budget_alignment
    (g : WeilCompactSmoothGV1)
    (hm : WeilMomentConditionsV1 g)
    (hw : AEGIS.WeilWindowExhaustionV1.LogWindowContainsV1
      g (693 / 2000)) :
    ∃ (n : ℕ)
      (gs : Fin (n + 1) → WeilCompactSmoothGV1)
      (center : Fin (n + 1) → ℝ),
      (∀ i, WeilMomentConditionsV1 (gs i)) ∧
      (∀ i, (5671 / 3200 : ℝ) * energy (gs i).1 ≤
        -(B (gs i) (gs i)).re) ∧
      (∀ i, AEGIS.RHRationalNinePacketPrimeWindowV1.WidthOneOneTwentyEightAt
        (gs i) (center i)) ∧
      g = packetSum (fun _ => (1 : ℂ)) gs ∧
      AEGIS.RHActualMixedDefectV1.actualMixedDefect n gs ≤
        -(∑ i, (B (gs i) (gs i)).re) := by
  obtain ⟨n, gs, center, hmom, hdiag, hwidth, hpacket, hgram⟩ :=
    AEGIS.RHActualUniversalFineGramV1.every_moment_zero_packet_actual_fine_gram_with_support
      g hm
  have hwindow :
      (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re ≤ 0 :=
    AEGIS.RHWindow693Over2000V1.window_693_over_2000_arithmetic_nonpositive_v1
      g hm hw
  have hfull :
      (B (packetSum (fun _ => (1 : ℂ)) gs)
        (packetSum (fun _ => (1 : ℂ)) gs)).re ≤ 0 := by
    calc
      (B (packetSum (fun _ => (1 : ℂ)) gs)
        (packetSum (fun _ => (1 : ℂ)) gs)).re =
          (∑ i, ∑ j, B (gs i) (gs j)).re := by
            rw [B_packetSum]
            simp
      _ = (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re :=
        hgram.symm
      _ ≤ 0 := hwindow
  have hbudget :=
    (actual_signed_defect_iff_packet_nonpositive gs).mpr hfull
  exact ⟨n, gs, center, hmom, hdiag, hwidth, hpacket, hbudget⟩

/-! ## Time slices: distinguish the exact shift ledger from its created Weil packet

The time coordinate is an integer spectral-translation label. The created
packet is the translated test function, with all genuine B-interactions
retained. The established common-window inequality immediately pays the
sharp signed defect. This does not assume or imply a global sign for
unrestricted time shifts.
-/

/-- Every finite family of exact femtosecond spectral translates of a
moment-zero narrow packet pays its entire REAL signed Weil mixed defect
whenever the established common-window span bound holds. Neither Schur
weights nor absolute off-diagonal bounds are used. -/
theorem actual_time_slice_sharp_signed_budget
    {n : ℕ} (g : WeilCompactSmoothGV1) (p origin center : ℝ)
    (ticks : Fin (n + 1) → ℤ)
    (hm : WeilMomentConditionsV1 g)
    (hw : AEGIS.RHDyadicDiagonalV13.HalfWidthAt
      g (1 / 256) origin)
    (hspan : ∀ i,
      |origin + AEGIS.RHTimeSliceWeilV1.fsLogSlice p (ticks i) - center| ≤
        (507 / 1280 : ℝ)) :
    AEGIS.RHActualMixedDefectV1.actualMixedDefect n
      (AEGIS.RHTimeSliceWeilV1.timeSliceFamily g p ticks) ≤
      -(∑ i, (B
        (AEGIS.RHTimeSliceWeilV1.timeSliceFamily g p ticks i)
        (AEGIS.RHTimeSliceWeilV1.timeSliceFamily g p ticks i)).re) := by
  have hmargin :=
    AEGIS.RHTimeSliceWeilV1.timeSliceFamily_full_weighted_margin
      g p origin center ticks (fun _ => (1 : ℂ)) hm hw hspan
  have hfull :=
    AEGIS.RHTimeSliceWeilV1.timeSliceFamily_full_gram
      g p ticks (fun _ => (1 : ℂ))
  rw [← hfull] at hmargin
  have hE : 0 ≤ (1 / 16 : ℝ) *
      energy (packetSum (fun _ => (1 : ℂ))
        (AEGIS.RHTimeSliceWeilV1.timeSliceFamily g p ticks)).1 :=
    mul_nonneg (by norm_num) (energy_nonnegative _)
  apply (actual_signed_defect_iff_packet_nonpositive
    (AEGIS.RHTimeSliceWeilV1.timeSliceFamily g p ticks)).mpr
  linarith

/-! ## Canonical RH equivalence using ONE sharp signed actual reconstruction

Unlike optimized Schur, this formulation has no hselect, no pointwise
absolute-value estimates and no diagonal-energy requirements.
The existential sign estimate is *precisely* the universal RH-equivalent
mathematical obligation, not an unconditionally proved producer.
-/

/-- The exact Mathlib RH target is equivalent to one signed actual Weil
finite reconstruction for each moment-zero source packet. No invented
matrix estimate, equal-energy reduction, or selected partition is assumed.
-/
theorem rh_iff_one_actual_sharp_signed_budget :
    RiemannHypothesis ↔
      ∀ (g : WeilCompactSmoothGV1), WeilMomentConditionsV1 g →
        ∃ (n : ℕ) (gs : Fin (n + 1) → WeilCompactSmoothGV1),
          g = packetSum (fun _ => (1 : ℂ)) gs ∧
          AEGIS.RHActualMixedDefectV1.actualMixedDefect n gs ≤
            -(∑ i, (B (gs i) (gs i)).re) := by
  constructor
  · intro hRH g hm
    obtain ⟨n, gs, _hmom, _hd, hpacket, hgram⟩ :=
      AEGIS.RHActualUniversalFineGramV1.every_moment_zero_packet_actual_fine_gram
        g hm
    refine ⟨n, gs, hpacket, ?_⟩
    have hfinal :
        (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re ≤ 0 :=
      (AEGIS.WeilAutocorrelationExplicitFormulaV10.autocorrelation_arithmetic_nonpositive_iff_zero_nonnegative_v10
        g hm).mpr
          ((AEGIS.WeilRHImpliesFinalSignV13.rh_implies_universal_v13 hRH) g hm)
    have hsum : (∑ i, ∑ j, B (gs i) (gs j)).re ≤ 0 := by
      rw [← hgram]
      exact hfinal
    apply (actual_signed_defect_iff_packet_nonpositive gs).mpr
    rw [B_packetSum]
    simpa using hsum
  · intro hcert
    apply AEGIS.RHRestrictedWeilBridgeV13.final_sign_implies_rh_v13
    intro g hm
    obtain ⟨n, gs, hpacket, hsigned⟩ := hcert g hm
    have hsign := (actual_signed_defect_iff_packet_nonpositive gs).mp hsigned
    rw [hpacket]
    change (B (packetSum (fun _ => (1 : ℂ)) gs)
      (packetSum (fun _ => (1 : ℂ)) gs)).re ≤ 0
    exact hsign


/-! ## Exact nonlocal log-three creation of a time slice

The newly created packet at two integer seconds in the declared p=3
spectral clock is EXACTLY the arithmetic translate by 2*log 3.
The signed von Mangoldt/Arch theorem therefore applies with its
original source hypotheses, without any shared 9/64 window and without
a floating-point approximation of the temporal shift.
-/

theorem fsLogSlice_three_two_seconds_exact :
    AEGIS.RHTimeSliceWeilV1.fsLogSlice 3 2000000000000000 =
      2 * Real.log 3 := by
  norm_num [AEGIS.RHTimeSliceWeilV1.fsLogSlice]

/-- A genuine nonlocal two-time-slice Weil coercivity with no extra
prime-row or Schur premise. This is the source-proved two-log-three
von Mangoldt estimate transported to exact integer time slices. -/
theorem actual_two_log_three_time_slice_coercive
    (g : WeilCompactSmoothGV1) (a : ℝ)
    (hm : WeilMomentConditionsV1 g)
    (hw : AEGIS.RHDyadicDiagonalV13.HalfWidthAt
      g (1 / 256 : ℝ) a) :
    (B
      (addPacket (AEGIS.RHTimeSliceWeilV1.timeSlicePacket g 3 0)
        (AEGIS.RHTimeSliceWeilV1.timeSlicePacket
          g 3 2000000000000000))
      (addPacket (AEGIS.RHTimeSliceWeilV1.timeSlicePacket g 3 0)
        (AEGIS.RHTimeSliceWeilV1.timeSlicePacket
          g 3 2000000000000000))).re ≤
      -(10517 / 4800 : ℝ) * energy g.1 := by
  simpa only [AEGIS.RHTimeSliceWeilV1.timeSlicePacket,
    AEGIS.RHTimeSliceWeilV1.fsLogSlice_zero,
    fsLogSlice_three_two_seconds_exact] using
      AEGIS.RHLogThreeSignedPrimeProducerV1.actual_two_log_three_gram_coercive
        g a hm hw

/-- The two created, far-separated actual Weil slices have a
nonpositive complete signed quadratic, including their mixed entry. -/
theorem actual_two_log_three_time_slice_nonpositive
    (g : WeilCompactSmoothGV1) (a : ℝ)
    (hm : WeilMomentConditionsV1 g)
    (hw : AEGIS.RHDyadicDiagonalV13.HalfWidthAt
      g (1 / 256 : ℝ) a) :
    (B
      (addPacket (AEGIS.RHTimeSliceWeilV1.timeSlicePacket g 3 0)
        (AEGIS.RHTimeSliceWeilV1.timeSlicePacket
          g 3 2000000000000000))
      (addPacket (AEGIS.RHTimeSliceWeilV1.timeSlicePacket g 3 0)
        (AEGIS.RHTimeSliceWeilV1.timeSlicePacket
          g 3 2000000000000000))).re ≤ 0 := by
  have h := actual_two_log_three_time_slice_coercive g a hm hw
  exact h.trans (mul_nonpos_of_nonpos_of_nonneg
    (by norm_num) (energy_nonnegative g.1))


/-! ## Horizon-dependent exact spectral resolution

The finite smooth local partition accepts arbitrarily small positive
widths. For a finite logarithmic-prime horizon K we choose a non-rounded
width sufficiently fine to isolate 3^k for every 1 <= k <= K.
No assumption about RH or the sign of distant cross terms enters.
This is the arithmetic resolution obligation for the *created* moment
at a given future spectral horizon, not an assertion about physical time.
-/

open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.WeilMixedClosureV2

/-- Exact spatial resolution that scales with the finite prime horizon. -/
def timeHorizonRadius (K : ℕ) : ℝ :=
  min (1 / 256) (1 / (4 * (3 : ℝ) ^ K))

theorem timeHorizonRadius_pos (K : ℕ) :
    0 < timeHorizonRadius K := by
  unfold timeHorizonRadius
  exact lt_min (by norm_num) (by positivity)

theorem timeHorizonRadius_le_fine (K : ℕ) :
    timeHorizonRadius K ≤ (1 / 256 : ℝ) := by
  unfold timeHorizonRadius
  exact min_le_left _ _


/-- Every moment-zero source packet has an actual finite Gram whose individual
Krein atoms retain the exact prime-horizon radius, with all mixed entries
preserved. No uniform mixed-sign estimate is inferred here. -/
theorem every_packet_actual_gram_at_time_horizon
    (K : ℕ)
    (g : WeilCompactSmoothGV1)
    (hm : WeilMomentConditionsV1 g) :
    ∃ (n : ℕ) (gs : Fin (n + 1) → WeilCompactSmoothGV1)
      (center : Fin (n + 1) → ℝ),
      (∀ i, WeilMomentConditionsV1 (gs i)) ∧
      (∀ i, (5671 / 3200 : ℝ) * energy (gs i).1 ≤
        -(B (gs i) (gs i)).re) ∧
      (∀ i, AEGIS.RHDyadicDiagonalV13.HalfWidthAt
        (gs i) (timeHorizonRadius K) (center i)) ∧
      g = packetSum (fun _ => (1 : ℂ)) gs ∧
      (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re =
        (∑ i, ∑ j, B (gs i) (gs j)).re := by
  exact
    AEGIS.RHActualUniversalFineGramV1.every_moment_zero_packet_actual_fine_gram_at_radius
      g hm (timeHorizonRadius K)
      (timeHorizonRadius_pos K) (timeHorizonRadius_le_fine K)


/-- An arbitrary moment-zero Weil packet admits, at EVERY finite prime
horizon, an exact local Gram decomposition whose genuine componentwise zero
quadratics satisfy the already proved analytic Krein/trigram E/16 margin.
All prime/Arch mixed entries of the reconstructed source remain in the Gram.
This asserts no sign for their global sum. -/
theorem every_packet_actual_horizon_gram_with_local_zero_margin
    (K : ℕ) (g : WeilCompactSmoothGV1)
    (hm : WeilMomentConditionsV1 g) :
    ∃ (n : ℕ) (gs : Fin (n + 1) → WeilCompactSmoothGV1)
      (center : Fin (n + 1) → ℝ),
      (∀ i, WeilMomentConditionsV1 (gs i)) ∧
      (∀ i, (5671 / 3200 : ℝ) * energy (gs i).1 ≤
        -(B (gs i) (gs i)).re) ∧
      (∀ i, AEGIS.RHDyadicDiagonalV13.HalfWidthAt
        (gs i) (timeHorizonRadius K) (center i)) ∧
      (∀ i, (1 / 16 : ℝ) * energy (gs i).1 ≤
        (∑' rho : RiemannNontrivialZeroIndexV2,
          WeilZeroIndexSummandV1
            (WeilAutocorrelationV1 (gs i)) rho).re) ∧
      g = packetSum (fun _ => (1 : ℂ)) gs ∧
      (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re =
        (∑ i, ∑ j, B (gs i) (gs j)).re := by
  obtain ⟨n, gs, center, hmom, hdiag, hw, hpacket, hgram⟩ :=
    every_packet_actual_gram_at_time_horizon K g hm
  refine ⟨n, gs, center, hmom, hdiag, hw, ?_, hpacket, hgram⟩
  intro i
  exact AEGIS.RHKreinTrigramAdaptiveV1.zero_quadratic_margin_trigram_v1
    (gs i) (timeHorizonRadius K) (center i)
    (le_of_lt (timeHorizonRadius_pos K))
    ((timeHorizonRadius_le_fine K).trans (by norm_num))
    (hw i) (hmom i)

/-- The exact source small-support prime condition holds SIMULTANEOUSLY
for every index not beyond the chosen integer spectral horizon. -/
theorem timeHorizonRadius_prime_gap (K k : ℕ) (hk : k ≤ K) :
    2 * timeHorizonRadius K ≤ 1 / (2 * (3 : ℝ) ^ k) := by
  have hpow : (3 : ℝ) ^ k ≤ (3 : ℝ) ^ K :=
    pow_le_pow_right₀ (by norm_num) hk
  have hdenK : 0 < 4 * (3 : ℝ) ^ K := by positivity
  have hdenk : 0 < 4 * (3 : ℝ) ^ k := by positivity
  have hinv :
      (1 : ℝ) / (4 * (3 : ℝ) ^ K) ≤
        1 / (4 * (3 : ℝ) ^ k) := by
    apply (div_le_div_iff₀ hdenK hdenk).2
    nlinarith [hpow]
  have hsmall : timeHorizonRadius K ≤
      1 / (4 * (3 : ℝ) ^ K) := by
    unfold timeHorizonRadius
    exact min_le_right _ _
  calc
    2 * timeHorizonRadius K ≤
        2 * (1 / (4 * (3 : ℝ) ^ K)) :=
      mul_le_mul_of_nonneg_left hsmall (by norm_num)
    _ ≤ 2 * (1 / (4 * (3 : ℝ) ^ k)) := by
      nlinarith [hinv]
    _ = 1 / (2 * (3 : ℝ) ^ k) := by ring

/-- A true finite-horizon von Mangoldt identity, valid for EVERY integer
prime gap k within K when the source packet has adaptive support width.
This is the original prime row, not a surrogate or norm approximation. -/
theorem exact_von_mangoldt_time_horizon
    (K k : ℕ) (hk : 1 ≤ k) (hkK : k ≤ K)
    (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : AEGIS.RHDyadicDiagonalV13.HalfWidthAt
      g (timeHorizonRadius K) a) :
    WeilPrimeSumV1
      (mixed (translatePacket g 0)
        (translatePacket g (k * Real.log 3))) =
      ((Real.log 3 * AEGIS.RHPrimeThreeWindowV1.triadicHalf k *
        energy g.1 : ℝ) : ℂ) := by
  exact AEGIS.RHPrimeThreeWindowV1.gap_prime_sum_exact_three
    g (timeHorizonRadius K) a k hk
    (timeHorizonRadius_pos K)
    (timeHorizonRadius_prime_gap K k hkK)
    ((timeHorizonRadius_le_fine K).trans (by norm_num))
    hw

/-- The same adaptive exact prime computation controls the genuine
complex mixed Weil B, retaining the Archimedean 1/100 allowance. -/
theorem actual_mixed_B_norm_time_horizon
    (K k : ℕ) (hk : 1 ≤ k) (hkK : k ≤ K)
    (g : WeilCompactSmoothGV1) (a : ℝ)
    (hm : WeilMomentConditionsV1 g)
    (hw : AEGIS.RHDyadicDiagonalV13.HalfWidthAt
      g (timeHorizonRadius K) a) :
    ‖B (translatePacket g 0)
      (translatePacket g (k * Real.log 3))‖ ≤
      (Real.log 3 * AEGIS.RHPrimeThreeWindowV1.triadicHalf k +
        1 / 100) * energy g.1 := by
  exact AEGIS.RHPrimeThreeWindowV1.gap_B_norm_bound_three
    g (timeHorizonRadius K) a k hk
    (timeHorizonRadius_pos K)
    (timeHorizonRadius_prime_gap K k hkK)
    ((timeHorizonRadius_le_fine K).trans (by norm_num))
    hw hm


/-! ## Uniform exact prime-row arithmetic at four-log-three gaps

For ANY finite horizon the arithmetic rows of a 4·log(3) translation
lattice are bounded independently of the number of translations.
This is a row certificate for the specified triadic SAME-SEED lattice,
not a producer for every arbitrary moment-zero packet. The original
RiemannHypothesis target is untouched.

The ratio 1/9 is exact: gap 4*d*log(3) contributes
3^(-2*d) = (1/9)^d to the original von Mangoldt factor.
-/

/-- Every positive finite geometric tail, for EVERY natural horizon. -/
theorem four_log_three_prime_geometric_tail (n : ℕ) :
    (∑ k ∈ Finset.Ico 1 (n + 1), (1 / 9 : ℝ) ^ k) ≤ 1 / 8 := by
  have h := geom_sum_Ico_le_of_lt_one
    (x := (1 / 9 : ℝ)) (m := 1) (n := n + 1)
    (by norm_num) (by norm_num)
  have hratio : (1 / 9 : ℝ) ^ 1 / (1 - 1 / 9) = 1 / 8 := by
    norm_num
  rw [hratio] at h
  exact h

/-- Two-sided row: no fixed matrix size or finite numerical enumeration. -/
theorem four_log_three_prime_two_sided_row (left right : ℕ) :
    (∑ k ∈ Finset.Ico 1 (left + 1), (1 / 9 : ℝ) ^ k) +
      (∑ k ∈ Finset.Ico 1 (right + 1), (1 / 9 : ℝ) ^ k) ≤
        (1 / 4 : ℝ) := by
  have hl := four_log_three_prime_geometric_tail left
  have hr := four_log_three_prime_geometric_tail right
  linarith

/-- The exact all-horizon rational row is below the existing Arch-29
signed-prime producer's ceiling. This proves the arithmetic BUDGET
for the sparse lattice; the support and arbitrary-packet reconstruction
requirements are distinct and are not silently erased. -/
theorem four_log_three_prime_row_below_arch29 (left right : ℕ) :
    (∑ k ∈ Finset.Ico 1 (left + 1), (1 / 9 : ℝ) ^ k) +
      (∑ k ∈ Finset.Ico 1 (right + 1), (1 / 9 : ℝ) ^ k) ≤
        (57401 / 65536 : ℝ) := by
  have h := four_log_three_prime_two_sided_row left right
  linarith

/-- Exact, rounding-free triadic spectral clock for EVERY integer
number of four-second translation steps. -/
theorem fsLogSlice_three_four_second_steps (k : ℤ) :
    AEGIS.RHTimeSliceWeilV1.fsLogSlice 3
      (4000000000000000 * k) =
        4 * (k : ℝ) * Real.log 3 := by
  norm_num [AEGIS.RHTimeSliceWeilV1.fsLogSlice, Int.cast_mul]; ring


/-! ## Existing full femtosecond Weil Gram specialized to 64 hexagrams

The previous source already proves the full signed Weil Gram for EVERY
finite family; here n=63 retains ALL 64^2=4096 ordered interactions.
This is an exact type-level integration, NOT a new assumption that any
mixed terms vanish or that arbitrary physical spacetimes are described.
-/

/-- Every one of the 64 × 64 ordered actual Weil coefficients survives.
No diagonal/off-diagonal suppression and no new arithmetic premise. -/
theorem hexagram64_actual_femtosecond_full_gram
    (g : WeilCompactSmoothGV1) (p : ℝ)
    (ticks : Fin 64 → ℤ) (z : Fin 64 → ℂ) :
    B (packetSum z (AEGIS.RHTimeSliceWeilV1.timeSliceFamily g p ticks))
      (packetSum z (AEGIS.RHTimeSliceWeilV1.timeSliceFamily g p ticks)) =
    ∑ i : Fin 64, ∑ j : Fin 64,
      z i * star (z j) *
        B (AEGIS.RHTimeSliceWeilV1.timeSliceFamily g p ticks i)
          (AEGIS.RHTimeSliceWeilV1.timeSliceFamily g p ticks j) := by
  exact AEGIS.RHTimeSliceWeilV1.timeSliceFamily_full_gram
    (n := 63) g p ticks z

/-- Exact unconditional-in-RH 64-state coercivity on the ALREADY PROVED
common-window domain. The geometric hypotheses are explicitly retained. -/
theorem hexagram64_actual_femtosecond_window_margin
    (g : WeilCompactSmoothGV1) (p origin center : ℝ)
    (ticks : Fin 64 → ℤ) (z : Fin 64 → ℂ)
    (hm : WeilMomentConditionsV1 g)
    (hw : AEGIS.RHDyadicDiagonalV13.HalfWidthAt
      g (1 / 256) origin)
    (hspan : ∀ i,
      |origin + AEGIS.RHTimeSliceWeilV1.fsLogSlice p (ticks i) - center| ≤
        (507 / 1280 : ℝ)) :
    (1 / 16 : ℝ) *
      energy (packetSum z (AEGIS.RHTimeSliceWeilV1.timeSliceFamily g p ticks)).1 ≤
      -(∑ i : Fin 64, ∑ j : Fin 64,
          z i * star (z j) *
            B (AEGIS.RHTimeSliceWeilV1.timeSliceFamily g p ticks i)
              (AEGIS.RHTimeSliceWeilV1.timeSliceFamily g p ticks j)).re := by
  exact AEGIS.RHTimeSliceWeilV1.timeSliceFamily_full_weighted_margin
    (n := 63) g p origin center ticks z hm hw hspan


/-! ## Sixty-four hexagrams as the tensor of two eight-trigram characters

Each hexagram is canonically two trigrams (upper, lower).
No rounding, no physical space-time assumption, and no suppression of
the genuine 4,096 ordered Weil Gram entries is introduced here.
-/

open AEGIS.RHBaguaWalshV1
open AEGIS.RHActualNarrowGramSignV1

/-- The upper three binary lines of a six-bit hexagram. -/
def hexagramUpper (a : Fin 64) : Fin 8 :=
  ⟨a.val / 8, by have ha := a.isLt; omega⟩

/-- The lower three binary lines of a six-bit hexagram. -/
def hexagramLower (a : Fin 64) : Fin 8 :=
  ⟨a.val % 8, Nat.mod_lt _ (by omega)⟩

/-- Tensor of two already proven integer Walsh characters, H8 ⊗ H8. -/
def hexagramWalsh64 (a i : Fin 64) : ℤ :=
  walsh8 (hexagramUpper a) (hexagramUpper i) *
    walsh8 (hexagramLower a) (hexagramLower i)

/-- The 64 × 64 character kernel is exactly symmetric. -/
theorem hexagramWalsh64_symmetric (a i : Fin 64) :
    hexagramWalsh64 a i = hexagramWalsh64 i a := by
  unfold hexagramWalsh64
  rw [walsh8_symmetric (hexagramUpper a) (hexagramUpper i),
    walsh8_symmetric (hexagramLower a) (hexagramLower i)]

/-- Each Walsh spectral mode retains every one of its 64 actual packets. -/
def hexagram64WalshMode
    (gs : Fin 64 → WeilCompactSmoothGV1) (a : Fin 64) :
    WeilCompactSmoothGV1 :=
  packetSum (fun i : Fin 64 => (hexagramWalsh64 a i : ℂ)) gs

/-- The actual Weil Gram in the 64-mode tensor Bagua basis. -/
def hexagram64WalshGram
    (gs : Fin 64 → WeilCompactSmoothGV1) (a b : Fin 64) : ℂ :=
  B (hexagram64WalshMode gs a) (hexagram64WalshMode gs b)

/-- EXACT congruence H64 * G * H64^T: every transformed entry expands
to all 4,096 genuine signed original Weil coefficients. No diagonal or
off-diagonal entry is erased and no positivity is assumed. -/
theorem hexagram64WalshGram_exact
    (gs : Fin 64 → WeilCompactSmoothGV1) (a b : Fin 64) :
    hexagram64WalshGram gs a b =
      ∑ i : Fin 64, ∑ j : Fin 64,
        (hexagramWalsh64 a i : ℂ) *
          star (hexagramWalsh64 b j : ℂ) * B (gs i) (gs j) := by
  unfold hexagram64WalshGram hexagram64WalshMode
  rw [B_packetSum_left]
  apply Finset.sum_congr rfl
  intro i _
  rw [B_packetSum_right, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Every full 64-mode Gram, including all cross terms, is the
untruncated true Weil pairing of its complex weighted sum. -/
theorem hexagram64WalshGram_weighted_exact
    (gs : Fin 64 → WeilCompactSmoothGV1) (z : Fin 64 → ℂ) :
    B (packetSum z (hexagram64WalshMode gs))
      (packetSum z (hexagram64WalshMode gs)) =
    ∑ a : Fin 64, ∑ b : Fin 64,
      z a * star (z b) * hexagram64WalshGram gs a b := by
  simpa only [hexagram64WalshGram] using
    (B_packetSum z (hexagram64WalshMode gs))

/-- The two zero moments survive every six-bit Walsh mode. -/
theorem hexagram64WalshMode_moments
    (gs : Fin 64 → WeilCompactSmoothGV1)
    (hm : ∀ i, WeilMomentConditionsV1 (gs i)) (a : Fin 64) :
    WeilMomentConditionsV1 (hexagram64WalshMode gs a) := by
  unfold hexagram64WalshMode
  exact trigram_moment_packetSum 63
    (fun i : Fin 64 => (hexagramWalsh64 a i : ℂ)) gs hm

/-- A common certified log-window survives the full 64-state Walsh
combination. No separated-family or fake near-neighbour assumption. -/
theorem hexagram64WalshMode_window
    (gs : Fin 64 → WeilCompactSmoothGV1) (center : ℝ)
    (hwin : ∀ i, AEGIS.RHDyadicDiagonalV13.HalfWidthAt
      (gs i) (2 / 5) center) (a : Fin 64) :
    AEGIS.RHDyadicDiagonalV13.HalfWidthAt
      (hexagram64WalshMode gs a) (2 / 5) center := by
  unfold hexagram64WalshMode
  exact trigram_window_packetSum 63
    (fun i : Fin 64 => (hexagramWalsh64 a i : ℂ)) gs center hwin

/-- A true 64×64 transformed Weil sign margin for ANY complex
amplitudes, under the existing explicitly certified common window.
This is unconditional in RH, not unconditional in spatial support. -/
theorem hexagram64Walsh_full_weighted_margin
    (gs : Fin 64 → WeilCompactSmoothGV1) (center : ℝ)
    (hm : ∀ i, WeilMomentConditionsV1 (gs i))
    (hwin : ∀ i, AEGIS.RHDyadicDiagonalV13.HalfWidthAt
      (gs i) (2 / 5) center)
    (z : Fin 64 → ℂ) :
    (1 / 16 : ℝ) * energy
      (packetSum z (hexagram64WalshMode gs)).1 ≤
      -(∑ a : Fin 64, ∑ b : Fin 64,
          z a * star (z b) * hexagram64WalshGram gs a b).re := by
  have hmModes : ∀ a, WeilMomentConditionsV1 (hexagram64WalshMode gs a) :=
    fun a => hexagram64WalshMode_moments gs hm a
  have hwModes : ∀ a, AEGIS.RHDyadicDiagonalV13.HalfWidthAt
      (hexagram64WalshMode gs a) (2 / 5) center :=
    fun a => hexagram64WalshMode_window gs center hwin a
  simpa only [hexagram64WalshGram] using
    (trigram_full_weighted_gram_margin 63 z
      (hexagram64WalshMode gs) center hmModes hwModes)


/-! ## Exact H64² = 64·I via the eight-trigram tensor factorization

This is a dimension-64 theorem, proved from the already kernel-checked
H8 character orthogonality, not a 4096-entry floating-point probe.
The product Fin 8 × Fin 8 is precisely the complete 64-hexagram carrier.
-/

def hexagramTensorCharacter
    (a b : Fin 8 × Fin 8) : ℤ :=
  walsh8 a.1 b.1 * walsh8 a.2 b.2

theorem hexagramTensor_row_orthogonality
    (a b : Fin 8 × Fin 8) :
    (∑ x : Fin 8 × Fin 8,
      hexagramTensorCharacter a x * hexagramTensorCharacter b x) =
    if a = b then (64 : ℤ) else 0 := by
  have hfactor :
      (∑ x : Fin 8 × Fin 8,
        hexagramTensorCharacter a x * hexagramTensorCharacter b x) =
        (∑ i : Fin 8, walsh8 a.1 i * walsh8 b.1 i) *
          (∑ j : Fin 8, walsh8 a.2 j * walsh8 b.2 j) := by
    rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [hexagramTensorCharacter]
    ring
  rw [hfactor, walsh8_row_orthogonality, walsh8_row_orthogonality]
  rcases a with ⟨a₁, a₂⟩
  rcases b with ⟨b₁, b₂⟩
  by_cases h₁ : a₁ = b₁ <;> by_cases h₂ : a₂ = b₂ <;>
    simp [h₁, h₂, Prod.mk.injEq]

/-- The tensor transform is normalized by exactly eight, and
its inverse coefficient 1/64 is exactly 1024 Q16.16 units. -/
theorem hexagramTensor_q16_inverse_exact :
    (1024 : ℤ) * 64 = 65536 := by norm_num


/-! ## Six-bit causal poset and an exact 1+3 Lorentzian realization

The Boolean six-cube has exactly 64 states. We assign positive,
superincreasing femtosecond tick weights 1,2,4,8,16,32 and pair
opposite null spatial directions along three axes. The following
is an explicit order-preserving FLAT Lorentzian realization, NOT a
derivation of a curved physical spacetime from the positive Weil Gram.

Each order-preserving bit addition has a future non-spacelike
displacement. A finite independent enumeration separately checks all
4,096 pairs; no converse is asserted (this embedding has additional
Minkowski-causal pairs that are not Boolean comparable).
-/

abbrev HexagramBits := Fin 6 → Bool

def hexagramBitValue (s : HexagramBits) (i : Fin 6) : ℤ :=
  if s i = true then 1 else 0

/-- Exactly the Boolean componentwise subset order. -/
def hexagramCausal (a b : HexagramBits) : Prop :=
  ∀ i : Fin 6, hexagramBitValue a i ≤ hexagramBitValue b i

theorem hexagramBits_count :
    Fintype.card HexagramBits = 64 := by decide

theorem hexagramCausal_refl (a : HexagramBits) :
    hexagramCausal a a := by
  intro i
  exact le_refl _

theorem hexagramCausal_trans (a b c : HexagramBits)
    (hab : hexagramCausal a b)
    (hbc : hexagramCausal b c) :
    hexagramCausal a c := by
  intro i
  exact (hab i).trans (hbc i)

theorem hexagramCausal_antisymm (a b : HexagramBits)
    (hab : hexagramCausal a b)
    (hba : hexagramCausal b a) : a = b := by
  funext i
  have h1 := hab i
  have h2 := hba i
  cases ha : a i <;> cases hb : b i <;>
    simp_all [hexagramBitValue]

/-- Coordinates in femtoseconds and c·femtoseconds (light-fs). -/
def hexagramClockFs (s : HexagramBits) : ℤ :=
  hexagramBitValue s 0 + 2 * hexagramBitValue s 1 +
    4 * hexagramBitValue s 2 + 8 * hexagramBitValue s 3 +
    16 * hexagramBitValue s 4 + 32 * hexagramBitValue s 5

def hexagramSpaceX (s : HexagramBits) : ℤ :=
  hexagramBitValue s 0 - 2 * hexagramBitValue s 1

def hexagramSpaceY (s : HexagramBits) : ℤ :=
  4 * hexagramBitValue s 2 - 8 * hexagramBitValue s 3

def hexagramSpaceZ (s : HexagramBits) : ℤ :=
  16 * hexagramBitValue s 4 - 32 * hexagramBitValue s 5

/-- (-,+,+,+) signature, with integer arithmetic throughout. -/
def hexagramMinkowskiIntervalSq (a b : HexagramBits) : ℤ :=
  -(hexagramClockFs b - hexagramClockFs a)^2 +
    (hexagramSpaceX b - hexagramSpaceX a)^2 +
    (hexagramSpaceY b - hexagramSpaceY a)^2 +
    (hexagramSpaceZ b - hexagramSpaceZ a)^2

/-- Pure algebraic light-cone estimate for six nonnegative bit increments.
No physics axiom is hidden in the calculation. -/
private theorem six_nonnegative_increments_causal
    (d0 d1 d2 d3 d4 d5 : ℤ)
    (h0 : 0 ≤ d0) (h1 : 0 ≤ d1)
    (h2 : 0 ≤ d2) (h3 : 0 ≤ d3)
    (h4 : 0 ≤ d4) (h5 : 0 ≤ d5) :
    -((d0 + d1 + d2 + d3 + d4 + d5)^2) +
      (d0 - d1)^2 + (d2 - d3)^2 + (d4 - d5)^2 ≤ 0 := by
  have h01 : 0 ≤ d0 * d1 := mul_nonneg h0 h1
  have h23 : 0 ≤ d2 * d3 := mul_nonneg h2 h3
  have h45 : 0 ≤ d4 * d5 := mul_nonneg h4 h5
  have hAB : 0 ≤ (d0 + d1) * (d2 + d3) :=
    mul_nonneg (add_nonneg h0 h1) (add_nonneg h2 h3)
  have hAC : 0 ≤ (d0 + d1) * (d4 + d5) :=
    mul_nonneg (add_nonneg h0 h1) (add_nonneg h4 h5)
  have hBC : 0 ≤ (d2 + d3) * (d4 + d5) :=
    mul_nonneg (add_nonneg h2 h3) (add_nonneg h4 h5)
  nlinarith

/-- Every Boolean-causally ordered pair lies in the future Minkowski cone.
The reverse implication is deliberately NOT asserted. -/
theorem hexagramCausal_future_nonspacelike
    (a b : HexagramBits) (hab : hexagramCausal a b) :
    0 ≤ hexagramClockFs b - hexagramClockFs a ∧
      hexagramMinkowskiIntervalSq a b ≤ 0 := by
  let d0 : ℤ := hexagramBitValue b 0 - hexagramBitValue a 0
  let d1 : ℤ := 2 * (hexagramBitValue b 1 - hexagramBitValue a 1)
  let d2 : ℤ := 4 * (hexagramBitValue b 2 - hexagramBitValue a 2)
  let d3 : ℤ := 8 * (hexagramBitValue b 3 - hexagramBitValue a 3)
  let d4 : ℤ := 16 * (hexagramBitValue b 4 - hexagramBitValue a 4)
  let d5 : ℤ := 32 * (hexagramBitValue b 5 - hexagramBitValue a 5)
  have h1 : 0 ≤ d1 := by dsimp [d1]; nlinarith [hab 1]
  have h2 : 0 ≤ d2 := by dsimp [d2]; nlinarith [hab 2]
  have h3 : 0 ≤ d3 := by dsimp [d3]; nlinarith [hab 3]
  have h4 : 0 ≤ d4 := by dsimp [d4]; nlinarith [hab 4]
  have h5 : 0 ≤ d5 := by dsimp [d5]; nlinarith [hab 5]
  have hzero : 0 ≤ d0 := by dsimp [d0]; exact sub_nonneg.mpr (hab 0)
  have ht :
      hexagramClockFs b - hexagramClockFs a =
      d0 + d1 + d2 + d3 + d4 + d5 := by
    dsimp [hexagramClockFs, d0, d1, d2, d3, d4, d5]
    ring
  have hx : hexagramSpaceX b - hexagramSpaceX a = d0 - d1 := by
    dsimp [hexagramSpaceX, d0, d1]
    ring
  have hy : hexagramSpaceY b - hexagramSpaceY a = d2 - d3 := by
    dsimp [hexagramSpaceY, d2, d3]
    ring
  have hz : hexagramSpaceZ b - hexagramSpaceZ a = d4 - d5 := by
    dsimp [hexagramSpaceZ, d4, d5]
    ring
  constructor
  · rw [ht]
    omega
  · unfold hexagramMinkowskiIntervalSq
    rw [ht, hx, hy, hz]
    exact six_nonnegative_increments_causal d0 d1 d2 d3 d4 d5
      hzero h1 h2 h3 h4 h5



/-! ## Real mixed-entry Gershgorin/Schur bound

This theorem is conditional on *actual* Weil cross-entry estimates.
The 2199 Krein analytic cells do not produce these estimates for
arbitrary packet partitions. No RH claim follows from this lemma alone.
-/

/-- A sufficient off-diagonal bound measured against the genuine negative
Weil diagonal, rather than against a surrogate or numerical Gram. -/
def mixed_defect_bound (n : ℕ)
    (gs : Fin (n + 1) → WeilCompactSmoothGV1) : Prop :=
  ∀ i j : Fin (n + 1), i ≠ j →
    ‖(B (gs i) (gs j)).re‖ ≤
      (1 / (n + 1 : ℝ)) *
        Real.sqrt (-(B (gs i) (gs i)).re *
          -(B (gs j) (gs j)).re)

/-- The real Weil Gram is nonpositive on the all-ones vector whenever
the explicitly supplied off-diagonal bound holds. This is a finite
Schur estimate, NOT a constructor for the bound. -/
theorem mixed_defect_bound_satisfies_matrix
    (n : ℕ)
    (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (hd : ∀ i, (5671 / 3200 : ℝ) * energy (gs i).1 ≤
      -(B (gs i) (gs i)).re)
    (hmix : mixed_defect_bound n gs) :
    (∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
      (B (gs i) (gs j)).re) ≤ 0 := by
  classical
  let E : Fin (n + 1) → ℝ :=
    fun i => -(B (gs i) (gs i)).re
  let H : Fin (n + 1) → Fin (n + 1) → ℂ :=
    fun i j => ((B (gs i) (gs j)).re : ℂ)
  let c : Fin (n + 1) → Fin (n + 1) → ℝ :=
    fun i j => if i = j then 0 else 1 / (n + 1 : ℝ)
  let w : Fin (n + 1) → ℝ := fun _ => 1
  have hE : ∀ i, 0 ≤ E i := by
    intro i
    have he : 0 ≤ energy (gs i).1 := energy_nonnegative _
    have hh : 0 ≤ (5671 / 3200 : ℝ) * energy (gs i).1 :=
      mul_nonneg (by norm_num) he
    exact hh.trans (hd i)
  have hc : ∀ i j, 0 ≤ c i j := by
    intro i j
    dsimp [c]
    split_ifs <;> positivity
  have hzero : ∀ i, c i i = 0 := by
    intro i
    simp [c]
  have hsym : ∀ i j, c i j = c j i := by
    intro i j
    by_cases hij : i = j
    · subst j
      rfl
    · simp [c, hij, Ne.symm hij]
  have hw : ∀ i, 0 < w i := by
    intro i
    norm_num [w]
  have hdiag : ∀ i, (1 : ℝ) * E i ≤ -(H i i).re := by
    intro i
    simp [E, H]
  have hcross : ∀ i j, i ≠ j →
      ‖H i j‖ ≤ c i j * (Real.sqrt (E i) * Real.sqrt (E j)) := by
    intro i j hij
    have hr := Real.sqrt_mul (hE i) (E j)
    change ‖((B (gs i) (gs j)).re : ℂ)‖ ≤
      (if i = j then 0 else 1 / (n + 1 : ℝ)) *
        (Real.sqrt (E i) * Real.sqrt (E j))
    rw [if_neg hij, ← hr, Complex.norm_real]
    exact hmix i j hij
  have hrow : ∀ i, (∑ j, c i j * (w j / w i)) ≤ (1 : ℝ) := by
    intro i
    have hrow_le :
        (∑ j : Fin (n + 1), c i j) ≤
          ∑ _j : Fin (n + 1), (1 / (n + 1 : ℝ)) := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hij : i = j
      · simp only [c, if_pos hij]
        positivity
      · simpa only [c, if_neg hij] using
          (le_refl (1 / (n + 1 : ℝ)))
    have hconst :
        (∑ _j : Fin (n + 1), (1 / (n + 1 : ℝ))) = 1 := by
      simp only [Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      have hn : (n + 1 : ℝ) ≠ 0 := by positivity
      field_simp [hn]
      norm_num [Nat.cast_add]
    simpa [w] using hrow_le.trans (le_of_eq hconst)
  have hschur :=
    AEGIS.WeightedSchur.weighted_gram_variable_energy
      H (fun _ => (1 : ℂ)) E c w (1 : ℝ) (1 : ℝ)
      hE hc hzero hsym hw hdiag hcross hrow
  simpa [H] using hschur

/-- Exact signed-defect form of the preceding finite Schur criterion. -/
theorem mixed_defect_bound_implies_signed_budget
    (n : ℕ)
    (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (hd : ∀ i, (5671 / 3200 : ℝ) * energy (gs i).1 ≤
      -(B (gs i) (gs i)).re)
    (hmix : mixed_defect_bound n gs) :
    AEGIS.RHActualMixedDefectV1.actualMixedDefect n gs ≤
      -(∑ i, (B (gs i) (gs i)).re) := by
  apply (actual_signed_defect_iff_packet_nonpositive gs).mpr
  rw [B_packetSum]
  simpa using mixed_defect_bound_satisfies_matrix n gs hd hmix

end AEGIS.RHOptimizedSchurGlobalJoinV1

#print axioms AEGIS.RHOptimizedSchurGlobalJoinV1.mixed_defect_bound_satisfies_matrix
#print axioms AEGIS.RHOptimizedSchurGlobalJoinV1.mixed_defect_bound_implies_signed_budget
#print axioms AEGIS.RHOptimizedSchurGlobalJoinV1.actual_signed_defect_iff_packet_nonpositive
#print axioms AEGIS.RHOptimizedSchurGlobalJoinV1.actual_fine_cluster_sharp_signed_budget
#print axioms AEGIS.RHOptimizedSchurGlobalJoinV1.certified_window_fine_gram_signed_budget_alignment
#print axioms AEGIS.RHOptimizedSchurGlobalJoinV1.actual_packet_sum_nonpositive_of_optimized_rows
#print axioms AEGIS.RHOptimizedSchurGlobalJoinV1.riemannHypothesis_of_optimized_actual_row_producer

#print axioms AEGIS.RHOptimizedSchurGlobalJoinV1.actual_time_slice_sharp_signed_budget
#print axioms AEGIS.RHOptimizedSchurGlobalJoinV1.rh_iff_one_actual_sharp_signed_budget

#print axioms AEGIS.RHOptimizedSchurGlobalJoinV1.fsLogSlice_three_two_seconds_exact
#print axioms AEGIS.RHOptimizedSchurGlobalJoinV1.actual_two_log_three_time_slice_coercive
#print axioms AEGIS.RHOptimizedSchurGlobalJoinV1.actual_two_log_three_time_slice_nonpositive

#print axioms AEGIS.RHOptimizedSchurGlobalJoinV1.every_packet_actual_horizon_gram_with_local_zero_margin
#print axioms AEGIS.RHOptimizedSchurGlobalJoinV1.every_packet_actual_gram_at_time_horizon
#print axioms AEGIS.RHOptimizedSchurGlobalJoinV1.timeHorizonRadius_prime_gap
#print axioms AEGIS.RHOptimizedSchurGlobalJoinV1.exact_von_mangoldt_time_horizon
#print axioms AEGIS.RHOptimizedSchurGlobalJoinV1.actual_mixed_B_norm_time_horizon

#print axioms AEGIS.RHOptimizedSchurGlobalJoinV1.four_log_three_prime_geometric_tail
#print axioms AEGIS.RHOptimizedSchurGlobalJoinV1.four_log_three_prime_two_sided_row
#print axioms AEGIS.RHOptimizedSchurGlobalJoinV1.four_log_three_prime_row_below_arch29
#print axioms AEGIS.RHOptimizedSchurGlobalJoinV1.fsLogSlice_three_four_second_steps

#print axioms AEGIS.RHOptimizedSchurGlobalJoinV1.hexagram64_actual_femtosecond_full_gram
#print axioms AEGIS.RHOptimizedSchurGlobalJoinV1.hexagram64_actual_femtosecond_window_margin

#print axioms AEGIS.RHOptimizedSchurGlobalJoinV1.hexagramWalsh64_symmetric
#print axioms AEGIS.RHOptimizedSchurGlobalJoinV1.hexagram64WalshGram_exact
#print axioms AEGIS.RHOptimizedSchurGlobalJoinV1.hexagram64WalshGram_weighted_exact
#print axioms AEGIS.RHOptimizedSchurGlobalJoinV1.hexagram64WalshMode_moments
#print axioms AEGIS.RHOptimizedSchurGlobalJoinV1.hexagram64WalshMode_window
#print axioms AEGIS.RHOptimizedSchurGlobalJoinV1.hexagram64Walsh_full_weighted_margin

#print axioms AEGIS.RHOptimizedSchurGlobalJoinV1.hexagramTensor_row_orthogonality
#print axioms AEGIS.RHOptimizedSchurGlobalJoinV1.hexagramTensor_q16_inverse_exact

#print axioms AEGIS.RHOptimizedSchurGlobalJoinV1.hexagramBits_count
#print axioms AEGIS.RHOptimizedSchurGlobalJoinV1.hexagramCausal_refl
#print axioms AEGIS.RHOptimizedSchurGlobalJoinV1.hexagramCausal_trans
#print axioms AEGIS.RHOptimizedSchurGlobalJoinV1.hexagramCausal_antisymm
#print axioms AEGIS.RHOptimizedSchurGlobalJoinV1.hexagramCausal_future_nonspacelike
