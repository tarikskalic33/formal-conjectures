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

import AEGISOverlay.RHActualLocalGramCoercivityV1
import RHWindowNineOver64GlobalizationV14
import WeilFinalSignTranslationBoundV10
import WeilSeparatedArchBridgeV31

/-!
AEGIS Ω — genuine full-Weil mixed-term defect, without dropped off-diagonals.

The entire finite Gram is the original arithmetic form, not a surrogate.
For every given compact-support local smooth partition we construct genuine
moment-zero narrow atoms with 32/25 diagonal gain and prove the EXACT global
lower bound in terms of the actual mixed contribution.

The remaining universal-sign obligation is precisely control of this
genuine mixed defect. No unconditional RH statement is introduced.
-/

open Set Finset Complex MeasureTheory
open scoped ContDiff BigOperators ComplexConjugate
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHActualMixedDefectV1

open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilMixedClosureV2
open AEGIS.WeilDisjointEnergyV2
open AEGIS.RHGramExpansionV13

/-- Genuine off-diagonal contribution: total B-Gram real part minus all
diagonal real parts. No term is discarded or replaced. -/
def actualMixedDefect (n : ℕ)
    (gs : Fin (n + 1) → WeilCompactSmoothGV1) : ℝ :=
  (∑ i, ∑ j, B (gs i) (gs j)).re -
    ∑ i, (B (gs i) (gs i)).re

/-- Pure algebraic summation of the original pointwise 32/25 diagonal
coercivity. No mixed-term bound is assumed. -/
theorem quantitative_lower_of_diagonal
    (n : ℕ) (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (hd : ∀ i, (32 / 25 : ℝ) * energy (gs i).1 ≤
      -(B (gs i) (gs i)).re) :
    (32 / 25 : ℝ) * (∑ i, energy (gs i).1) -
      actualMixedDefect n gs ≤
        -(∑ i, ∑ j, B (gs i) (gs j)).re := by
  have hs :
      (∑ i, (32 / 25 : ℝ) * energy (gs i).1) ≤
        ∑ i, -(B (gs i) (gs i)).re :=
    Finset.sum_le_sum (fun i _ => hd i)
  have hdiag :
      (32 / 25 : ℝ) * (∑ i, energy (gs i).1) ≤
        -(∑ i, (B (gs i) (gs i)).re) := by
    rw [Finset.mul_sum]
    simpa only [Finset.sum_neg_distrib] using hs
  unfold actualMixedDefect
  linarith

/-- For every arbitrary packet and every feasible locally complete narrow
smooth partition, construct an actual finite Gram and its exact quantitative
mixed-defect lower bound. -/
theorem every_packet_actual_mixed_defect_bound
    (n : ℕ)
    (g : WeilCompactSmoothGV1)
    (hm : WeilMomentConditionsV1 g)
    (L : ℝ) (hL : 0 ≤ L)
    (hs : tsupport (AEGIS.RHKreinFactorV13.lift g.1) ⊆ Icc (-L) L)
    (χ : Fin (n + 1) → ℝ → ℂ)
    (hχ : ∀ i, ContDiff ℝ ∞ (χ i))
    (hpart : ∀ x ∈ Icc (-L) L, ∑ i : Fin (n + 1), χ i x = 1)
    (center : Fin (n + 1) → ℝ)
    (hcut : ∀ i, tsupport (χ i) ⊆
      Icc (center i - 1 / 128) (center i + 1 / 128)) :
    ∃ gs : Fin (n + 1) → WeilCompactSmoothGV1,
      (∀ i, WeilMomentConditionsV1 (gs i)) ∧
      g = packetSum (fun _ => (1 : ℂ)) gs ∧
      (32 / 25 : ℝ) * (∑ i, energy (gs i).1) -
          actualMixedDefect n gs ≤
            -(WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re := by
  obtain ⟨gs, hmom, hd, hpacket, hgram⟩ :=
    AEGIS.RHActualLocalGramCoercivityV1.every_packet_actual_narrow_coercive_gram
      n g hm L hL hs χ hχ hpart center hcut
  refine ⟨gs, hmom, hpacket, ?_⟩
  calc
    (32 / 25 : ℝ) * (∑ i, energy (gs i).1) -
          actualMixedDefect n gs ≤
      -(∑ i, ∑ j, B (gs i) (gs j)).re :=
        quantitative_lower_of_diagonal n gs hd
    _ = -(WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re := by
      rw [hgram]

/-- The exact, separately identifiable mixed-term budget that would close
the sign of this *particular* genuine Weil Gram. It is not assumed globally. -/
theorem actual_zero_sign_of_paid_mixed_defect
    (n : ℕ) (g : WeilCompactSmoothGV1)
    (hm : WeilMomentConditionsV1 g)
    (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (hdiag : ∀ i, (32 / 25 : ℝ) * energy (gs i).1 ≤
      -(B (gs i) (gs i)).re)
    (hgram : (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re =
      (∑ i, ∑ j, B (gs i) (gs j)).re)
    (hbudget : actualMixedDefect n gs ≤
      (32 / 25 : ℝ) * (∑ i, energy (gs i).1)) :
    0 ≤ (∑' rho : RiemannNontrivialZeroIndexV2,
      WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re := by
  have hbound := quantitative_lower_of_diagonal n gs hdiag
  have hsign : (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re ≤ 0 := by
    rw [hgram]
    linarith
  exact (AEGIS.WeilAutocorrelationExplicitFormulaV10.autocorrelation_arithmetic_nonpositive_iff_zero_nonnegative_v10
    g hm).mp hsign


/-! ## Unconditional, actual-B control of local interacting atoms

This section does not assume any global sign. A *common* certified
1/64-width log window is stable under finite sums and complex scaling.
Applying the existing analytic diagonal inequality to u+v and u-v
controls the real off-diagonal arithmetic B(u,v) itself. No cross
coefficient is set to zero, and no mixed budget for widely separated
atoms is inferred from this strictly local estimate. -/

open AEGIS.RHKreinFactorV13

theorem narrow_width_scale
    (u : WeilCompactSmoothGV1) (z : ℂ) (center : ℝ)
    (hu : AEGIS.RHNarrowDiagonalUpgradeV2.WidthOneSixtyFourAt u center) :
    AEGIS.RHNarrowDiagonalUpgradeV2.WidthOneSixtyFourAt
      (scalePacket z u) center := by
  change tsupport (lift (scalePacket z u).1) ⊆
    Icc (center - 1 / 128) (center + 1 / 128)
  change tsupport (lift u.1) ⊆
    Icc (center - 1 / 128) (center + 1 / 128) at hu
  have hlift : lift (scalePacket z u).1 =
      (fun x => z * lift u.1 x) := by
    funext x
    simp only [AEGIS.RHKreinFactorV13.lift, scalePacket]
    ring
  rw [hlift]
  have hsupport : tsupport (fun x => z * lift u.1 x) ⊆
      tsupport (lift u.1) := by
    apply closure_minimal ?_ (isClosed_tsupport _)
    intro x hx
    by_contra hn
    have hzero : lift u.1 x = 0 :=
      image_eq_zero_of_notMem_tsupport hn
    exact hx (by simp [hzero])
  exact hsupport.trans hu

theorem narrow_width_add
    (u v : WeilCompactSmoothGV1) (center : ℝ)
    (hu : AEGIS.RHNarrowDiagonalUpgradeV2.WidthOneSixtyFourAt u center)
    (hv : AEGIS.RHNarrowDiagonalUpgradeV2.WidthOneSixtyFourAt v center) :
    AEGIS.RHNarrowDiagonalUpgradeV2.WidthOneSixtyFourAt
      (addPacket u v) center := by
  change tsupport (lift (addPacket u v).1) ⊆
    Icc (center - 1 / 128) (center + 1 / 128)
  change tsupport (lift u.1) ⊆
    Icc (center - 1 / 128) (center + 1 / 128) at hu
  change tsupport (lift v.1) ⊆
    Icc (center - 1 / 128) (center + 1 / 128) at hv
  have hlift : lift (addPacket u v).1 =
      (fun x => lift u.1 x + lift v.1 x) := by
    funext x
    simp only [AEGIS.RHKreinFactorV13.lift, addPacket, mul_add]
  rw [hlift]
  have hsupport :
      tsupport (fun x => lift u.1 x + lift v.1 x) ⊆
        tsupport (lift u.1) ∪ tsupport (lift v.1) := by
    apply closure_minimal ?_
      ((isClosed_tsupport _).union (isClosed_tsupport _))
    intro x hx
    by_contra hn
    have hzeroU : lift u.1 x = 0 :=
      image_eq_zero_of_notMem_tsupport (by
        intro hxU
        exact hn (Or.inl hxU))
    have hzeroV : lift v.1 x = 0 :=
      image_eq_zero_of_notMem_tsupport (by
        intro hxV
        exact hn (Or.inr hxV))
    exact hx (by simp [hzeroU, hzeroV])
  intro x hx
  rcases hsupport hx with hxU | hxV
  · exact hu hxU
  · exact hv hxV

/-- A genuinely narrow SUM controls the actual positive mixed interaction.
The 32/25 coercive gain for the SUM is retained as an explicit term. -/
theorem actual_mixed_re_upper_of_narrow_sum
    (u v : WeilCompactSmoothGV1) (center : ℝ)
    (hw : AEGIS.RHNarrowDiagonalUpgradeV2.WidthOneSixtyFourAt
      (addPacket u v) center) :
    2 * (B u v).re +
      (32 / 25 : ℝ) * energy (addPacket u v).1 ≤
      -(B u u).re - (B v v).re := by
  have hdiag :=
    AEGIS.RHNarrowDiagonalUpgradeV2.narrow_diagonal_32_over_25_v2
      (addPacket u v) center hw
  have hgram :=
    AEGIS.RHCofinalSchurAdapterV1.actual_two_block_gram_coefficients u v
  linarith

/-- On a common certified narrow log-window, both u+v and u-v are
admissible for the existing REAL Weil diagonal inequality. Their
polarization gives a true bound on the actual mixed interaction B(u,v)
with no assumed cross-term inequality and no global RH sign premise. -/
theorem actual_mixed_re_abs_of_common_narrow_window
    (u v : WeilCompactSmoothGV1) (center : ℝ)
    (hu : AEGIS.RHNarrowDiagonalUpgradeV2.WidthOneSixtyFourAt u center)
    (hv : AEGIS.RHNarrowDiagonalUpgradeV2.WidthOneSixtyFourAt v center) :
    |(B u v).re| ≤ (-(B u u).re - (B v v).re) / 2 := by
  have hwPlus := narrow_width_add u v center hu hv
  have hwMinus : AEGIS.RHNarrowDiagonalUpgradeV2.WidthOneSixtyFourAt
      (addPacket u (scalePacket (-1 : ℂ) v)) center :=
    narrow_width_add u (scalePacket (-1 : ℂ) v) center hu
      (narrow_width_scale v (-1 : ℂ) center hv)
  have hplus := actual_mixed_re_upper_of_narrow_sum u v center hwPlus
  have hminus :=
    actual_mixed_re_upper_of_narrow_sum
      u (scalePacket (-1 : ℂ) v) center hwMinus
  have hcross :
      (B u (scalePacket (-1 : ℂ) v)).re = -(B u v).re := by
    rw [B_scale_right]
    simp
  have hdiag :
      (B (scalePacket (-1 : ℂ) v) (scalePacket (-1 : ℂ) v)).re =
        (B v v).re := by
    rw [B_scale_left, B_scale_right]
    simp
  rw [hcross, hdiag] at hminus
  have heplus :
      0 ≤ (32 / 25 : ℝ) * energy (addPacket u v).1 :=
    mul_nonneg (by norm_num) (energy_nonnegative _)
  have heminus :
      0 ≤ (32 / 25 : ℝ) *
        energy (addPacket u (scalePacket (-1 : ℂ) v)).1 :=
    mul_nonneg (by norm_num) (energy_nonnegative _)
  apply abs_le.mpr
  constructor <;> linarith


/-- A bound on the entire complex genuine Weil mixed entry. Apply the
same real-polarization lemma to u and i v to control its imaginary part;
then use the pinned Mathlib complex norm inequality. This controls B,
not a surrogate or its real projection only, for pairs sharing a
certified width-1/64 log window. -/
theorem actual_mixed_norm_le_of_common_narrow_window
    (u v : WeilCompactSmoothGV1) (center : ℝ)
    (hu : AEGIS.RHNarrowDiagonalUpgradeV2.WidthOneSixtyFourAt u center)
    (hv : AEGIS.RHNarrowDiagonalUpgradeV2.WidthOneSixtyFourAt v center) :
    ‖B u v‖ ≤ -(B u u).re - (B v v).re := by
  have hreal :=
    actual_mixed_re_abs_of_common_narrow_window u v center hu hv
  have himag :=
    actual_mixed_re_abs_of_common_narrow_window
      u (scalePacket Complex.I v) center hu
      (narrow_width_scale v Complex.I center hv)
  have hrot :
      (B u (scalePacket Complex.I v)).re = (B u v).im := by
    rw [B_scale_right]
    simp [Complex.mul_re]
  have hdiag :
      (B (scalePacket Complex.I v) (scalePacket Complex.I v)).re =
        (B v v).re := by
    rw [B_scale_left, B_scale_right]
    simp
  rw [hrot, hdiag] at himag
  have htri := Complex.norm_le_abs_re_add_abs_im (B u v)
  linarith


/-! ## Source-locked radius 9/64 coercive mixed-term bridge

This uses the original V14 rational moment gain, not a proxy positivity
hypothesis. The mixed B identity is exact. The sum's moment and 9/64
window membership are explicit, not silently assumed. -/

open AEGIS.WeilThreeBlockTranslatedPacketsV22

theorem actual_nine_over_64_mixed_re_upper
    (u v : WeilCompactSmoothGV1) (center : ℝ)
    (hm : WeilMomentConditionsV1 (addPacket u v))
    (hw : AEGIS.RHDyadicDiagonalV13.HalfWidthAt (addPacket u v) (9 / 64) center) :
    2 * (B u v).re +
      (1 / 10 : ℝ) * energy (addPacket u v).1 ≤
      -(B u u).re - (B v v).re := by
  have hcoercive :=
    AEGIS.RHWindowNineOver64GlobalizationV14.nine_over_64_coercive
      (addPacket u v) center hw hm
  change (B (addPacket u v) (addPacket u v)).re ≤
    -(1 / 10 : ℝ) * energy (addPacket u v).1 at hcoercive
  have hgram :=
    AEGIS.RHCofinalSchurAdapterV1.actual_two_block_gram_coefficients u v
  linarith

theorem actual_nine_over_64_mixed_re_abs
    (u v : WeilCompactSmoothGV1) (center : ℝ)
    (hmp : WeilMomentConditionsV1 (addPacket u v))
    (hwp : AEGIS.RHDyadicDiagonalV13.HalfWidthAt (addPacket u v) (9 / 64) center)
    (hmm : WeilMomentConditionsV1
      (addPacket u (scalePacket (-1 : ℂ) v)))
    (hwm : AEGIS.RHDyadicDiagonalV13.HalfWidthAt
      (addPacket u (scalePacket (-1 : ℂ) v)) (9 / 64) center) :
    |(B u v).re| ≤ (-(B u u).re - (B v v).re) / 2 := by
  have hplus := actual_nine_over_64_mixed_re_upper u v center hmp hwp
  have hminus := actual_nine_over_64_mixed_re_upper
    u (scalePacket (-1 : ℂ) v) center hmm hwm
  have hcross :
      (B u (scalePacket (-1 : ℂ) v)).re = -(B u v).re := by
    rw [B_scale_right]
    simp
  have hdiag :
      (B (scalePacket (-1 : ℂ) v) (scalePacket (-1 : ℂ) v)).re =
        (B v v).re := by
    rw [B_scale_left, B_scale_right]
    simp
  rw [hcross, hdiag] at hminus
  have heplus : 0 ≤ energy (addPacket u v).1 := energy_nonnegative _
  have heminus :
      0 ≤ energy (addPacket u (scalePacket (-1 : ℂ) v)).1 :=
    energy_nonnegative _
  apply abs_le.mpr
  constructor <;> linarith


/-- Actual COMPLEX mixed coefficient at half-width 9/64.
The caller supplies moment/centered-window witnesses for the four actual
polarized sums u+v, u-v, u+i v and u-i v. None is an assumption about
B itself; no universal cofinal row bound is inferred from this theorem. -/
theorem actual_nine_over_64_mixed_norm_le
    (u v : WeilCompactSmoothGV1) (center : ℝ)
    (hmp : WeilMomentConditionsV1 (addPacket u v))
    (hwp : AEGIS.RHDyadicDiagonalV13.HalfWidthAt (addPacket u v) (9 / 64) center)
    (hmm : WeilMomentConditionsV1
      (addPacket u (scalePacket (-1 : ℂ) v)))
    (hwm : AEGIS.RHDyadicDiagonalV13.HalfWidthAt
      (addPacket u (scalePacket (-1 : ℂ) v)) (9 / 64) center)
    (hmi : WeilMomentConditionsV1
      (addPacket u (scalePacket Complex.I v)))
    (hwi : AEGIS.RHDyadicDiagonalV13.HalfWidthAt
      (addPacket u (scalePacket Complex.I v)) (9 / 64) center)
    (hmni : WeilMomentConditionsV1
      (addPacket u (scalePacket (-Complex.I) v)))
    (hwni : AEGIS.RHDyadicDiagonalV13.HalfWidthAt
      (addPacket u (scalePacket (-Complex.I) v)) (9 / 64) center) :
    ‖B u v‖ ≤ -(B u u).re - (B v v).re := by
  have hreal :=
    actual_nine_over_64_mixed_re_abs u v center hmp hwp hmm hwm
  have hiplus :=
    actual_nine_over_64_mixed_re_upper
      u (scalePacket Complex.I v) center hmi hwi
  have himinus :=
    actual_nine_over_64_mixed_re_upper
      u (scalePacket (-Complex.I) v) center hmni hwni
  have hcrossi :
      (B u (scalePacket Complex.I v)).re = (B u v).im := by
    rw [B_scale_right]
    simp [Complex.mul_re]
  have hcrossni :
      (B u (scalePacket (-Complex.I) v)).re = -(B u v).im := by
    rw [B_scale_right]
    simp [Complex.mul_re]
  have hdiagi :
      (B (scalePacket Complex.I v) (scalePacket Complex.I v)).re =
        (B v v).re := by
    rw [B_scale_left, B_scale_right]
    simp
  have hdiagn :
      (B (scalePacket (-Complex.I) v)
        (scalePacket (-Complex.I) v)).re = (B v v).re := by
    rw [B_scale_left, B_scale_right]
    simp
  rw [hcrossi, hdiagi] at hiplus
  rw [hcrossni, hdiagn] at himinus
  have hei : 0 ≤ energy (addPacket u (scalePacket Complex.I v)).1 :=
    energy_nonnegative _
  have heni : 0 ≤ energy (addPacket u (scalePacket (-Complex.I) v)).1 :=
    energy_nonnegative _
  have himag :
      |(B u v).im| ≤ (-(B u u).re - (B v v).re) / 2 := by
    apply abs_le.mpr
    constructor <;> linarith
  have htri := Complex.norm_le_abs_re_add_abs_im (B u v)
  linarith


/-! ## Exact counterpart on an arbitrary finite *common local* window

Unlike an entrywise Q16.16 majorant, this proof retains the signed
off-diagonal contributions and applies the existing *actual* strong
fine-window diagonal inequality to the whole packet sum.  The
summands may have distinct shapes and energies, but all share a
single center and a half-width 1/256 in log coordinates.

The exact counterpart concerns the full contracted Gram and its
off-diagonal defect; it does not assert a pairwise norm bound for
remote support windows or a global RH theorem. -/

open AEGIS.RHRationalNinePacketPrimeWindowV1
open AEGIS.RHGramExpansionV13

/-- A complex scalar does not enlarge a fine log-support window. -/
theorem fine_width_scale
    (u : WeilCompactSmoothGV1) (z : ℂ) (center : ℝ)
    (hu : WidthOneOneTwentyEightAt u center) :
    WidthOneOneTwentyEightAt (scalePacket z u) center := by
  change tsupport (lift (scalePacket z u).1) ⊆
    Icc (center - 1 / 256) (center + 1 / 256)
  change tsupport (lift u.1) ⊆
    Icc (center - 1 / 256) (center + 1 / 256) at hu
  have hlift : lift (scalePacket z u).1 =
      (fun x => z * lift u.1 x) := by
    funext x
    simp only [AEGIS.RHKreinFactorV13.lift, scalePacket]
    ring
  rw [hlift]
  have hs : tsupport (fun x => z * lift u.1 x) ⊆
      tsupport (lift u.1) := by
    apply closure_minimal ?_ (isClosed_tsupport _)
    intro x hx
    by_contra hn
    have hzero : lift u.1 x = 0 :=
      image_eq_zero_of_notMem_tsupport hn
    exact hx (by simp [hzero])
  exact hs.trans hu

/-- Two fine packets centered on the same finite window remain fine
after exact addition, independently of their relative energies. -/
theorem fine_width_add
    (u v : WeilCompactSmoothGV1) (center : ℝ)
    (hu : WidthOneOneTwentyEightAt u center)
    (hv : WidthOneOneTwentyEightAt v center) :
    WidthOneOneTwentyEightAt (addPacket u v) center := by
  change tsupport (lift (addPacket u v).1) ⊆
    Icc (center - 1 / 256) (center + 1 / 256)
  change tsupport (lift u.1) ⊆
    Icc (center - 1 / 256) (center + 1 / 256) at hu
  change tsupport (lift v.1) ⊆
    Icc (center - 1 / 256) (center + 1 / 256) at hv
  have hlift : lift (addPacket u v).1 =
      (fun x => lift u.1 x + lift v.1 x) := by
    funext x
    simp only [AEGIS.RHKreinFactorV13.lift, addPacket, mul_add]
  rw [hlift]
  have hs :
      tsupport (fun x => lift u.1 x + lift v.1 x) ⊆
        tsupport (lift u.1) ∪ tsupport (lift v.1) := by
    apply closure_minimal ?_
      ((isClosed_tsupport _).union (isClosed_tsupport _))
    intro x hx
    by_contra hn
    have hu0 : lift u.1 x = 0 :=
      image_eq_zero_of_notMem_tsupport (by
        intro hxU
        exact hn (Or.inl hxU))
    have hv0 : lift v.1 x = 0 :=
      image_eq_zero_of_notMem_tsupport (by
        intro hxV
        exact hn (Or.inr hxV))
    exact hx (by simp [hu0, hv0])
  intro x hx
  rcases hs hx with hxU | hxV
  · exact hu hxU
  · exact hv hxV

/-- Any finite complex linear combination of arbitrary *different*
fine packets stays on their common window. This is not a theorem
about translates with different centers. -/
theorem fine_width_packetSum :
    ∀ (n : ℕ)
      (z : Fin (n + 1) → ℂ)
      (gs : Fin (n + 1) → WeilCompactSmoothGV1)
      (center : ℝ),
      (∀ i, WidthOneOneTwentyEightAt (gs i) center) →
      WidthOneOneTwentyEightAt (packetSum z gs) center := by
  intro n
  induction n with
  | zero =>
      intro z gs center hwin
      change WidthOneOneTwentyEightAt
        (scalePacket (z 0) (gs 0)) center
      exact fine_width_scale (gs 0) (z 0) center (hwin 0)
  | succ n ih =>
      intro z gs center hwin
      change WidthOneOneTwentyEightAt
        (addPacket
          (packetSum (fun i : Fin (n + 1) => z i.castSucc)
            (fun i : Fin (n + 1) => gs i.castSucc))
          (scalePacket (z (Fin.last (n + 1)))
            (gs (Fin.last (n + 1))))) center
      exact fine_width_add _ _ center
        (ih (fun i => z i.castSucc) (fun i => gs i.castSucc)
          center (fun i => hwin i.castSucc))
        (fine_width_scale _ _ center (hwin (Fin.last (n + 1))))

/-- The actual full signed Weil Gram on any common fine finite window
has the *exact* rational coercivity, for arbitrary coefficients. The
off-diagonal cancellations are not replaced by norm majorants. -/
theorem fine_local_exact_counterpart
    (n : ℕ) (z : Fin (n + 1) → ℂ)
    (gs : Fin (n + 1) → WeilCompactSmoothGV1) (center : ℝ)
    (hwin : ∀ i, WidthOneOneTwentyEightAt (gs i) center) :
    (5671 / 3200 : ℝ) * energy (packetSum z gs).1 ≤
      -(B (packetSum z gs) (packetSum z gs)).re := by
  exact AEGIS.RHFineDiagonalUpgradeV3.fine_diagonal_5671_over_3200_v3
    (packetSum z gs) center
    (fine_width_packetSum n z gs center hwin)

/-- The outward-rounded *opposite-sign* Q16.16 companion to the exact
local finite-window proof. Rounding the positive diagonal gain down
cannot change the direction of this inequality. -/
theorem fine_local_q16_counterpart
    (n : ℕ) (z : Fin (n + 1) → ℂ)
    (gs : Fin (n + 1) → WeilCompactSmoothGV1) (center : ℝ)
    (hwin : ∀ i, WidthOneOneTwentyEightAt (gs i) center) :
    (116142 / 65536 : ℝ) * energy (packetSum z gs).1 ≤
      -(B (packetSum z gs) (packetSum z gs)).re := by
  have hE : 0 ≤ energy (packetSum z gs).1 :=
    energy_nonnegative _
  have hround : (116142 / 65536 : ℝ) ≤ 5671 / 3200 := by
    norm_num
  exact (mul_le_mul_of_nonneg_right hround hE).trans
    (fine_local_exact_counterpart n z gs center hwin)

/-- Signed (not absolute) upper bound for the exact actual mixed defect
of an arbitrary finite family on one common fine window.  This is the
opposite-side counterpart of the global Q16.16 pairwise budget. -/
theorem fine_local_exact_mixed_defect_opposite
    (n : ℕ) (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (center : ℝ)
    (hwin : ∀ i, WidthOneOneTwentyEightAt (gs i) center) :
    actualMixedDefect n gs ≤
      -((5671 / 3200 : ℝ) *
        energy (packetSum (fun _ => (1 : ℂ)) gs).1) -
      ∑ i, (B (gs i) (gs i)).re := by
  have hcoercive := fine_local_exact_counterpart n
    (fun _ => (1 : ℂ)) gs center hwin
  have hgram :
      (B (packetSum (fun _ => (1 : ℂ)) gs)
        (packetSum (fun _ => (1 : ℂ)) gs)).re =
        (∑ i, ∑ j, B (gs i) (gs j)).re := by
    rw [B_packetSum]
    simp
  rw [hgram] at hcoercive
  unfold actualMixedDefect
  linarith


/-! ## Nearby but distinct fine windows: an unconditional actual-B bridge

If two fine atoms have individual log half-width 1/256 and their
centers have distance at most 35/128, their union fits exactly inside
one 9/64 half-width interval centered at their midpoint.  The pinned
9/64 analytic coercivity then bounds the genuine mixed Weil
coefficient of the two DIFFERENT atoms.

This is a finite-range bridge, NOT a claim for arbitrarily distant
windows or a universal Q16.16 producer. -/

open AEGIS.WeilFinalSignTranslationBoundV10

/-- Geometric recentering of a genuinely fine source packet: all
constants are exact rationals (1/256 + (35/128)/2 = 9/64). -/
theorem fine_width_into_nine_midpoint
    (u : WeilCompactSmoothGV1) (a b : ℝ)
    (hu : WidthOneOneTwentyEightAt u a)
    (hab : |a - b| ≤ (35 / 128 : ℝ)) :
    AEGIS.RHDyadicDiagonalV13.HalfWidthAt
      u (9 / 64) ((a + b) / 2) := by
  change tsupport (lift u.1) ⊆
    Icc ((a + b) / 2 - 9 / 64) ((a + b) / 2 + 9 / 64)
  change tsupport (lift u.1) ⊆
    Icc (a - 1 / 256) (a + 1 / 256) at hu
  intro t ht
  obtain ⟨hlo, hhi⟩ := hu ht
  obtain ⟨hablo, habhi⟩ := abs_le.mp hab
  constructor <;> linarith

/-- Multiplication by any complex scalar preserves the common 9/64
logarithmic support; the proof is about the genuine source packet. -/
theorem nine_width_scale
    (u : WeilCompactSmoothGV1) (z : ℂ) (center : ℝ)
    (hu : AEGIS.RHDyadicDiagonalV13.HalfWidthAt u (9 / 64) center) :
    AEGIS.RHDyadicDiagonalV13.HalfWidthAt
      (scalePacket z u) (9 / 64) center := by
  change tsupport (lift (scalePacket z u).1) ⊆
    Icc (center - 9 / 64) (center + 9 / 64)
  change tsupport (lift u.1) ⊆
    Icc (center - 9 / 64) (center + 9 / 64) at hu
  have hlift : lift (scalePacket z u).1 =
      (fun x => z * lift u.1 x) := by
    funext x
    simp only [AEGIS.RHKreinFactorV13.lift, scalePacket]
    ring
  rw [hlift]
  have hs : tsupport (fun x => z * lift u.1 x) ⊆
      tsupport (lift u.1) := by
    apply closure_minimal ?_ (isClosed_tsupport _)
    intro x hx
    by_contra hn
    have hz : lift u.1 x = 0 := image_eq_zero_of_notMem_tsupport hn
    exact hx (by simp [hz])
  exact hs.trans hu

/-- Adding packets with different shapes preserves their shared
9/64 local support without assuming their mixed Weil sign. -/
theorem nine_width_add
    (u v : WeilCompactSmoothGV1) (center : ℝ)
    (hu : AEGIS.RHDyadicDiagonalV13.HalfWidthAt u (9 / 64) center)
    (hv : AEGIS.RHDyadicDiagonalV13.HalfWidthAt v (9 / 64) center) :
    AEGIS.RHDyadicDiagonalV13.HalfWidthAt
      (addPacket u v) (9 / 64) center := by
  change tsupport (lift (addPacket u v).1) ⊆
    Icc (center - 9 / 64) (center + 9 / 64)
  change tsupport (lift u.1) ⊆
    Icc (center - 9 / 64) (center + 9 / 64) at hu
  change tsupport (lift v.1) ⊆
    Icc (center - 9 / 64) (center + 9 / 64) at hv
  have hlift : lift (addPacket u v).1 =
      (fun x => lift u.1 x + lift v.1 x) := by
    funext x
    simp only [AEGIS.RHKreinFactorV13.lift, addPacket, mul_add]
  rw [hlift]
  have hs :
      tsupport (fun x => lift u.1 x + lift v.1 x) ⊆
        tsupport (lift u.1) ∪ tsupport (lift v.1) := by
    apply closure_minimal ?_
      ((isClosed_tsupport _).union (isClosed_tsupport _))
    intro x hx
    by_contra hn
    have hu0 : lift u.1 x = 0 :=
      image_eq_zero_of_notMem_tsupport (by
        intro hxU
        exact hn (Or.inl hxU))
    have hv0 : lift v.1 x = 0 :=
      image_eq_zero_of_notMem_tsupport (by
        intro hxV
        exact hn (Or.inr hxV))
    exact hx (by simp [hu0, hv0])
  intro x hx
  rcases hs hx with hxU | hxV
  · exact hu hxU
  · exact hv hxV

/-- Nearby distinct local packets have a common 9/64 window:
there is no assumption that they are translates of a fixed seed. -/
theorem nearby_fine_pair_shared_nine_window
    (u v : WeilCompactSmoothGV1) (a b : ℝ)
    (hu : WidthOneOneTwentyEightAt u a)
    (hv : WidthOneOneTwentyEightAt v b)
    (hab : |a - b| ≤ (35 / 128 : ℝ)) :
    AEGIS.RHDyadicDiagonalV13.HalfWidthAt u (9 / 64) ((a + b) / 2) ∧
    AEGIS.RHDyadicDiagonalV13.HalfWidthAt v (9 / 64) ((a + b) / 2) := by
  constructor
  · exact fine_width_into_nine_midpoint u a b hu hab
  · have hba : |b - a| ≤ (35 / 128 : ℝ) := by
      simpa only [abs_sub_comm] using hab
    simpa only [add_comm] using
      (fine_width_into_nine_midpoint v b a hv hba)

/-- GENUINE signed mixed-term estimate for two DISTINCT fine-window
Weil packets, from pinned unconditional radius-9/64 coercivity.
Both moment annihilations are propagated through addition. -/
theorem nearby_fine_pair_actual_mixed_signed
    (u v : WeilCompactSmoothGV1) (a b : ℝ)
    (hmu : WeilMomentConditionsV1 u)
    (hmv : WeilMomentConditionsV1 v)
    (hu : WidthOneOneTwentyEightAt u a)
    (hv : WidthOneOneTwentyEightAt v b)
    (hab : |a - b| ≤ (35 / 128 : ℝ)) :
    2 * (B u v).re + (1 / 10 : ℝ) * energy (addPacket u v).1 ≤
      -(B u u).re - (B v v).re := by
  obtain ⟨hwu, hwv⟩ := nearby_fine_pair_shared_nine_window
    u v a b hu hv hab
  exact actual_nine_over_64_mixed_re_upper u v ((a + b) / 2)
    (momentConditions_addPacket_v10 u v hmu hmv)
    (nine_width_add u v ((a + b) / 2) hwu hwv)

/-- The same signed actual-Weil estimate, conservatively rounded
down to Q16.16. No float computation or postulated inequality. -/
theorem nearby_fine_pair_actual_mixed_q16
    (u v : WeilCompactSmoothGV1) (a b : ℝ)
    (hmu : WeilMomentConditionsV1 u)
    (hmv : WeilMomentConditionsV1 v)
    (hu : WidthOneOneTwentyEightAt u a)
    (hv : WidthOneOneTwentyEightAt v b)
    (hab : |a - b| ≤ (35 / 128 : ℝ)) :
    2 * (B u v).re +
      (6553 / 65536 : ℝ) * energy (addPacket u v).1 ≤
      -(B u u).re - (B v v).re := by
  have he : 0 ≤ energy (addPacket u v).1 := energy_nonnegative _
  have hround : (6553 / 65536 : ℝ) ≤ 1 / 10 := by norm_num
  have hprod := mul_le_mul_of_nonneg_right hround he
  have hexact := nearby_fine_pair_actual_mixed_signed u v a b
    hmu hmv hu hv hab
  linarith

/-- Complex mixed norm for nearby DIFFERENT fine windows, with all
four exact polarization tests supplied by the same geometric support
and preserved moment conditions.  No cross estimate is an input. -/
theorem nearby_fine_pair_actual_mixed_norm
    (u v : WeilCompactSmoothGV1) (a b : ℝ)
    (hmu : WeilMomentConditionsV1 u)
    (hmv : WeilMomentConditionsV1 v)
    (hu : WidthOneOneTwentyEightAt u a)
    (hv : WidthOneOneTwentyEightAt v b)
    (hab : |a - b| ≤ (35 / 128 : ℝ)) :
    ‖B u v‖ ≤ -(B u u).re - (B v v).re := by
  obtain ⟨hwu, hwv⟩ := nearby_fine_pair_shared_nine_window
    u v a b hu hv hab
  let c : ℝ := (a + b) / 2
  have hpolarM (z : ℂ) :
      WeilMomentConditionsV1 (addPacket u (scalePacket z v)) :=
    momentConditions_addPacket_v10 u (scalePacket z v) hmu
      (momentConditions_scalePacket_v10 z v hmv)
  have hpolarW (z : ℂ) :
      AEGIS.RHDyadicDiagonalV13.HalfWidthAt
        (addPacket u (scalePacket z v)) (9 / 64) c :=
    nine_width_add u (scalePacket z v) c hwu
      (nine_width_scale v z c hwv)
  exact actual_nine_over_64_mixed_norm_le u v c
    (momentConditions_addPacket_v10 u v hmu hmv)
    (nine_width_add u v c hwu hwv)
    (hpolarM (-1)) (hpolarW (-1))
    (hpolarM Complex.I) (hpolarW Complex.I)
    (hpolarM (-Complex.I)) (hpolarW (-Complex.I))


/-! ## Actual distant-window ARCH control for unequal packet shapes

The existing separated support theorem bounds the real arithmetic
Archimedean integral if supplied a logCross envelope.  Here we prove
that envelope for two arbitrary, distinct packets from the exact L²
isometry, and discharge all geometric hypotheses by padding the
individual fine windows to radius 1/64.

This is a REAL ANALYTIC PRODUCER for the distant Arch term, not a
complete bound on B: the von Mangoldt prime contribution remains.
-/

open AEGIS.WeilSeparatedArchBridgeV31
open AEGIS.WeilThreeBlockCrossPrimeV28
open AEGIS.WeilWidthArchCorrelationV25
open AEGIS.WeilLogCoordinateIsometryV21

/-- General distinct-packet mixed correlation, with no shared seed:
the energy bound is the arithmetic mean, avoiding sqrt/CS obligations. -/
theorem distinct_logCross_norm_le_mean_energy
    (p q : WeilCompactSmoothGV1) (u : ℝ) :
    ‖logCrossV28 p q u‖ ≤
      (energy p.1 + energy q.1) / 2 := by
  let F : ℝ → ℂ := fun v =>
    logLift p.1 (v + u) * conj (logLift q.1 v)
  let M : ℝ → ℝ := fun v =>
    (1 / 2 : ℝ) *
      (‖logLift p.1 (v + u)‖ ^ 2 + ‖logLift q.1 v‖ ^ 2)
  have hM : Integrable M := by
    unfold M
    exact ((shifted_logLift_sq_integrable_v25 p u).add
      (logLift_sq_integrable_v25 q)).const_mul (1 / 2 : ℝ)
  have hmeas : AEStronglyMeasurable F := by
    exact (((logLift_continuous p).comp (by fun_prop)).aestronglyMeasurable.mul
      ((continuous_conj.comp (logLift_continuous q)).aestronglyMeasurable))
  have hpoint : ∀ v : ℝ, ‖F v‖ ≤ M v := by
    intro v
    have hab :
        ‖logLift p.1 (v + u)‖ * ‖logLift q.1 v‖ ≤
        (1 / 2 : ℝ) *
          (‖logLift p.1 (v + u)‖ ^ 2 + ‖logLift q.1 v‖ ^ 2) := by
      nlinarith [sq_nonneg (‖logLift p.1 (v + u)‖ - ‖logLift q.1 v‖)]
    simpa [F, M, norm_mul, norm_conj] using hab
  have hF : Integrable F :=
    hM.mono' hmeas (Filter.Eventually.of_forall hpoint)
  calc
    ‖logCrossV28 p q u‖ = ‖∫ v : ℝ, F v‖ := rfl
    _ ≤ ∫ v : ℝ, ‖F v‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ v : ℝ, M v := integral_mono hF.norm hM hpoint
    _ = (1 / 2 : ℝ) *
        ((∫ v : ℝ, ‖logLift p.1 (v + u)‖ ^ 2) +
           ∫ v : ℝ, ‖logLift q.1 v‖ ^ 2) := by
          unfold M
          rw [integral_const_mul, integral_add
            (shifted_logLift_sq_integrable_v25 p u)
            (logLift_sq_integrable_v25 q)]
    _ = (energy p.1 + energy q.1) / 2 := by
          rw [shifted_logLift_sq_integral_v25,
            logLift_energy_eq_packet_energy]
          ring

/-- The actual separated ARCH term for arbitrary distinct fine local
Weil atoms, with an exact gap threshold log 2 and no postulated cross
correlation bound. The sum of energies is explicit. -/
theorem distinct_fine_far_arch_norm_le
    (p q : WeilCompactSmoothGV1) (a b : ℝ)
    (hp : WidthOneOneTwentyEightAt p a)
    (hq : WidthOneOneTwentyEightAt q b)
    (hm : WeilMomentConditionsV1 p)
    (hgap : Real.log 2 ≤ b - a) :
    ‖WeilArchimedeanIntegralV1 (mixed p q)‖ ≤
      (1 / 200 : ℝ) * (energy p.1 + energy q.1) := by
  let E : ℝ := (energy p.1 + energy q.1) / 2
  have hEp : 0 ≤ energy p.1 := energy_nonnegative p.1
  have hEq : 0 ≤ energy q.1 := energy_nonnegative q.1
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hlogp :
      LogSupportIn p (a - 1 / 64) (a + 1 / 64) := by
    intro t ht
    obtain ⟨hlo, hhi⟩ := hp ht
    exact ⟨by linarith, by linarith⟩
  have hlogq :
      LogSupportIn q (b - 1 / 64) (b + 1 / 64) := by
    intro t ht
    obtain ⟨hlo, hhi⟩ := hq ht
    exact ⟨by linarith, by linarith⟩
  have harch := separated_arch_norm_bound
    p q (a - 1 / 64) (a + 1 / 64)
    (b - 1 / 64) (b + 1 / 64) E
    hlogp hlogq (by linarith) (by
      norm_num [CorrelationSupportDifferenceWidthV31]
      ring) hm hE
    (fun u => distinct_logCross_norm_le_mean_energy p q u)
  dsimp [E] at harch
  convert harch using 1; ring


/-- The exact off-diagonal B form of two distant, different fine atoms:
the term at 1 is actually zero by disjoint logarithmic supports. -/
theorem distinct_fine_far_mixed_one_zero
    (p q : WeilCompactSmoothGV1) (a b : ℝ)
    (hp : WidthOneOneTwentyEightAt p a)
    (hq : WidthOneOneTwentyEightAt q b)
    (hgap : Real.log 2 ≤ b - a) :
    mixed p q 1 = 0 := by
  have hlog : logCrossV28 p q 0 = 0 := by
    apply logCross_zero_outside p q
      (a - 1 / 256) (a + 1 / 256)
      (b - 1 / 256) (b + 1 / 256) 0 hp hq
    right
    linarith [hgap, log_two_gt_one_thirty_two]
  have h := logCross_eq_mixed_v28 p q 0
  simp only [zero_div, Real.exp_zero, Complex.ofReal_one, one_mul] at h
  exact h.symm.trans hlog

/-- Exact decomposition of the FULL distant Weil B interaction.  This
is the established ARCH bound plus the genuine remaining von Mangoldt
prime contribution, not an assumed mixed-Weil estimate and not a
claim that remote prime contributions vanish. -/
theorem distinct_fine_far_actual_B_norm_le_prime_plus_arch
    (p q : WeilCompactSmoothGV1) (a b : ℝ)
    (hp : WidthOneOneTwentyEightAt p a)
    (hq : WidthOneOneTwentyEightAt q b)
    (hm : WeilMomentConditionsV1 p)
    (hgap : Real.log 2 ≤ b - a) :
    ‖B p q‖ ≤ ‖WeilPrimeSumV1 (mixed p q)‖ +
      (1 / 200 : ℝ) * (energy p.1 + energy q.1) := by
  have hzero := distinct_fine_far_mixed_one_zero p q a b hp hq hgap
  have harch := distinct_fine_far_arch_norm_le p q a b hp hq hm hgap
  have heq : B p q =
      WeilPrimeSumV1 (mixed p q) +
      WeilArchimedeanIntegralV1 (mixed p q) := by
    unfold B WeilExplicitRightSideV1
    rw [hzero]
    ring
  rw [heq]
  exact (norm_add_le _ _).trans (add_le_add le_rfl harch)


/-! ## Moment-zero removal of the distant rank-one Arch kernel

Exact reuse of the source-pinned separated Arch integral identity,
support localization and weighted Mellin-moment annihilation.  Unlike
the old 1/200 energy estimate, the remaining kernel decays as
exp(-5δ/2)/(1-exp(-2δ)).  The von Mangoldt prime sum is not changed.
-/

open Set Function MeasureTheory Complex
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.WeilSeparatedArchBridgeV31
open AEGIS.WeilThreeBlockCrossPrimeV28
open AEGIS.WeilLogCoordinateIsometryV21

theorem separated_arch_decay_bound
    (p q : WeilCompactSmoothGV1) (plo phi qlo qhi E : ℝ)
    (hp : LogSupportIn p plo phi) (hq : LogSupportIn q qlo qhi)
    (hgap : Real.log 2 - 1 / 32 ≤ qlo - phi)
    (δ : ℝ) (hδ : 0 < δ) (hδgap : δ ≤ qlo - phi)
    (hwidth : (qhi - plo) - (qlo - phi) = CorrelationSupportDifferenceWidthV31)
    (hm : WeilMomentConditionsV1 p) (hE : 0 ≤ E)
    (hR : ∀ u : ℝ, ‖logCrossV28 p q u‖ ≤ E) :
    ‖WeilArchimedeanIntegralV1 (mixed p q)‖ ≤
      (1 / 16 : ℝ) *
        (Real.exp (-5 * δ / 2) / (1 - Real.exp (-2 * δ))) * E := by
  let R : ℝ := Real.exp (-5 * δ / 2) / (1 - Real.exp (-2 * δ))
  let lo := qlo - phi
  let hi := qhi - plo
  let K : ℝ → ℝ := fun u => Real.exp (-u / 2) / (1 - Real.exp (-2 * u))
  let F : ℝ → ℂ := fun u => (K u : ℂ) * logCrossV28 p q (-u)
  let M : ℝ → ℂ := fun u => (Real.exp (-u / 2) : ℂ) * logCrossV28 p q (-u)
  have hlo : 0 < lo := by
    dsimp [lo]
    linarith only [hgap, log_two_gt_one_thirty_two]
  have hzero (u : ℝ) (hu : u ∉ Icc lo hi) : logCrossV28 p q (-u) = 0 := by
    apply logCross_zero_outside p q plo phi qlo qhi (-u) hp hq
    by_cases hlow : u < lo
    · right
      dsimp [lo] at hlow
      linarith
    · have hhigh : hi < u := lt_of_not_ge (fun h => hu ⟨le_of_not_gt hlow, h⟩)
      left
      dsimp [hi] at hhigh
      linarith
  have hFfull : (∫ u in Icc lo hi, F u) = ∫ u, F u :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun u hu => by simp [F, hzero u hu])
  have hFpos : (∫ u in Ioi (0 : ℝ), F u) = ∫ u, F u := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro u hu
    have hnot : u ∉ Icc lo hi := by
      intro h
      exact hu (lt_of_lt_of_le hlo h.1)
    simp [F, hzero u hnot]
  have harch : WeilArchimedeanIntegralV1 (mixed p q) = ∫ u in Icc lo hi, F u := by
    rw [separated_arch_eq_log_kernel p q plo phi qlo qhi hp hq (by dsimp [lo] at hlo; linarith)]
    exact hFpos.trans hFfull.symm
  have hMfull : (∫ u, M u) = 0 := by
    have ht := integral_neg_eq_self
      (fun u : ℝ => (Real.exp (u / 2) : ℂ) * logCrossV28 p q u) volume
    exact ht.trans (logCross_plus_moment_zero p q plo phi qlo qhi hp hq hm)
  have hMzero : (∫ u in Icc lo hi, M u) = 0 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (f := M) (s := Icc lo hi)
      (fun u hu => by simp [M, hzero u hu])]
    exact hMfull
  have hMc : Continuous M := by
    dsimp [M]
    exact (by fun_prop : Continuous (fun u : ℝ => (Real.exp (-u / 2) : ℂ))).mul
      ((logCross_continuous p q).comp continuous_neg)
  have hKc : ContinuousOn K (Icc lo hi) := by
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro u hu
    have hup : 0 < u := lt_of_lt_of_le hlo hu.1
    exact ne_of_gt (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith)))
  have hFc : ContinuousOn F (Icc lo hi) :=
    (Complex.continuous_ofReal.comp_continuousOn hKc).mul
      (((logCross_continuous p q).comp continuous_neg).continuousOn)
  have hcancel : (∫ u in Icc lo hi, F u) =
      ∫ u in Icc lo hi, F u - M u := by
    rw [integral_sub hFc.integrableOn_Icc hMc.integrableOn_Icc,
      hMzero, sub_zero]
  have hpoint (u : ℝ) (hu : u ∈ Icc lo hi) :
      ‖F u - M u‖ ≤ R * E := by
    have huPos : 0 < u := lt_of_lt_of_le hlo hu.1
    have hden : 0 < 1 - Real.exp (-2 * u) := by
      apply sub_pos.mpr
      exact Real.exp_lt_one_iff.mpr (by linarith)
    have hku : |K u - Real.exp (-u / 2)| ≤ R := by
      change |Real.exp (-u / 2) / (1 - Real.exp (-2 * u)) -
        Real.exp (-u / 2)| ≤ R
      rw [AEGIS.WeilThreeBlockCrossAssemblyV30.arch_kernel_sub_rank_one u huPos]
      rw [abs_of_nonneg (div_nonneg (Real.exp_pos _).le hden.le)]
      exact AEGIS.WeilThreeBlockCrossAssemblyV30.arch_remainder_le_at_gap
        δ u hδ (hδgap.trans hu.1)
    have heq : F u - M u =
        (((K u - Real.exp (-u / 2)) : ℝ) : ℂ) * logCrossV28 p q (-u) := by
      dsimp [F, M]
      push_cast
      ring
    rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (hR (-u)) (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_right hku hE)
  rw [harch, hcancel]
  calc
    ‖∫ u in Icc lo hi, F u - M u‖ ≤
        R * E * (volume.restrict (Icc lo hi)).real univ := by
      apply norm_integral_le_of_norm_le_const
      filter_upwards [self_mem_ae_restrict measurableSet_Icc] with u hu
      exact hpoint u hu
    _ = (1 / 16 : ℝ) *
      (Real.exp (-5 * δ / 2) / (1 - Real.exp (-2 * δ))) * E := by
      have hw : hi - lo = (1 / 16 : ℝ) := by
        simpa [CorrelationSupportDifferenceWidthV31] using hwidth
      simp [Measure.real, Real.volume_Icc, hw, R]; ring


/-! ## Any strictly positive separation: exact fine-width Arch cancellation

The original distant estimate required log 2 only to establish a
positive support gap. Rank-one moment cancellation itself needs merely
a strictly positive gap. Keeping exact 1/256 packet half-widths gives
correlation width 1/64, rather than padded width 1/16.
The von Mangoldt contribution is NOT discarded. -/

/-- Same rank-one-cancelled Arch integral proof without a log 2 threshold,
with correlation-support width 1/64. -/
theorem separated_arch_decay_any_positive_gap
    (p q : WeilCompactSmoothGV1) (plo phi qlo qhi E : ℝ)
    (hp : LogSupportIn p plo phi) (hq : LogSupportIn q qlo qhi)
    (δ : ℝ) (hδ : 0 < δ) (hδgap : δ ≤ qlo - phi)
    (hwidth : (qhi - plo) - (qlo - phi) = (1 / 64 : ℝ))
    (hm : WeilMomentConditionsV1 p) (hE : 0 ≤ E)
    (hR : ∀ u : ℝ, ‖logCrossV28 p q u‖ ≤ E) :
    ‖WeilArchimedeanIntegralV1 (mixed p q)‖ ≤
      (1 / 64 : ℝ) *
        (Real.exp (-5 * δ / 2) / (1 - Real.exp (-2 * δ))) * E := by
  let R : ℝ := Real.exp (-5 * δ / 2) / (1 - Real.exp (-2 * δ))
  let lo := qlo - phi
  let hi := qhi - plo
  let K : ℝ → ℝ := fun u => Real.exp (-u / 2) / (1 - Real.exp (-2 * u))
  let F : ℝ → ℂ := fun u => (K u : ℂ) * logCrossV28 p q (-u)
  let M : ℝ → ℂ := fun u => (Real.exp (-u / 2) : ℂ) * logCrossV28 p q (-u)
  have hlo : 0 < lo := by
    dsimp [lo]
    exact lt_of_lt_of_le hδ hδgap
  have hzero (u : ℝ) (hu : u ∉ Icc lo hi) : logCrossV28 p q (-u) = 0 := by
    apply logCross_zero_outside p q plo phi qlo qhi (-u) hp hq
    by_cases hlow : u < lo
    · right
      dsimp [lo] at hlow
      linarith
    · have hhigh : hi < u := lt_of_not_ge (fun h => hu ⟨le_of_not_gt hlow, h⟩)
      left
      dsimp [hi] at hhigh
      linarith
  have hFfull : (∫ u in Icc lo hi, F u) = ∫ u, F u :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun u hu => by simp [F, hzero u hu])
  have hFpos : (∫ u in Ioi (0 : ℝ), F u) = ∫ u, F u := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro u hu
    have hnot : u ∉ Icc lo hi := by
      intro h
      exact hu (lt_of_lt_of_le hlo h.1)
    simp [F, hzero u hnot]
  have harch : WeilArchimedeanIntegralV1 (mixed p q) = ∫ u in Icc lo hi, F u := by
    rw [separated_arch_eq_log_kernel p q plo phi qlo qhi hp hq (by dsimp [lo] at hlo; linarith)]
    exact hFpos.trans hFfull.symm
  have hMfull : (∫ u, M u) = 0 := by
    have ht := integral_neg_eq_self
      (fun u : ℝ => (Real.exp (u / 2) : ℂ) * logCrossV28 p q u) volume
    exact ht.trans (logCross_plus_moment_zero p q plo phi qlo qhi hp hq hm)
  have hMzero : (∫ u in Icc lo hi, M u) = 0 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (f := M) (s := Icc lo hi)
      (fun u hu => by simp [M, hzero u hu])]
    exact hMfull
  have hMc : Continuous M := by
    dsimp [M]
    exact (by fun_prop : Continuous (fun u : ℝ => (Real.exp (-u / 2) : ℂ))).mul
      ((logCross_continuous p q).comp continuous_neg)
  have hKc : ContinuousOn K (Icc lo hi) := by
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro u hu
    have hup : 0 < u := lt_of_lt_of_le hlo hu.1
    exact ne_of_gt (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith)))
  have hFc : ContinuousOn F (Icc lo hi) :=
    (Complex.continuous_ofReal.comp_continuousOn hKc).mul
      (((logCross_continuous p q).comp continuous_neg).continuousOn)
  have hcancel : (∫ u in Icc lo hi, F u) =
      ∫ u in Icc lo hi, F u - M u := by
    rw [integral_sub hFc.integrableOn_Icc hMc.integrableOn_Icc,
      hMzero, sub_zero]
  have hpoint (u : ℝ) (hu : u ∈ Icc lo hi) :
      ‖F u - M u‖ ≤ R * E := by
    have huPos : 0 < u := lt_of_lt_of_le hlo hu.1
    have hden : 0 < 1 - Real.exp (-2 * u) := by
      apply sub_pos.mpr
      exact Real.exp_lt_one_iff.mpr (by linarith)
    have hku : |K u - Real.exp (-u / 2)| ≤ R := by
      change |Real.exp (-u / 2) / (1 - Real.exp (-2 * u)) -
        Real.exp (-u / 2)| ≤ R
      rw [AEGIS.WeilThreeBlockCrossAssemblyV30.arch_kernel_sub_rank_one u huPos]
      rw [abs_of_nonneg (div_nonneg (Real.exp_pos _).le hden.le)]
      exact AEGIS.WeilThreeBlockCrossAssemblyV30.arch_remainder_le_at_gap
        δ u hδ (hδgap.trans hu.1)
    have heq : F u - M u =
        (((K u - Real.exp (-u / 2)) : ℝ) : ℂ) * logCrossV28 p q (-u) := by
      dsimp [F, M]
      push_cast
      ring
    rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (hR (-u)) (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_right hku hE)
  rw [harch, hcancel]
  calc
    ‖∫ u in Icc lo hi, F u - M u‖ ≤
        R * E * (volume.restrict (Icc lo hi)).real univ := by
      apply norm_integral_le_of_norm_le_const
      filter_upwards [self_mem_ae_restrict measurableSet_Icc] with u hu
      exact hpoint u hu
    _ = (1 / 64 : ℝ) *
      (Real.exp (-5 * δ / 2) / (1 - Real.exp (-2 * δ))) * E := by
      have hw : hi - lo = (1 / 64 : ℝ) := by
        simpa [lo, hi] using hwidth
      simp [Measure.real, Real.volume_Icc, hw, R]; ring


/-- For any two distinct moment-zero fine packets with disjoint ordered
log supports, the actual Arch integral has a quantitative residual
that decays with their *exact* positive support gap. -/
theorem distinct_fine_arch_decay_any_positive_gap
    (p q : WeilCompactSmoothGV1) (a b : ℝ)
    (hp : WidthOneOneTwentyEightAt p a)
    (hq : WidthOneOneTwentyEightAt q b)
    (hm : WeilMomentConditionsV1 p)
    (hsep : (1 / 128 : ℝ) < b - a) :
    ‖WeilArchimedeanIntegralV1 (mixed p q)‖ ≤
      (1 / 128 : ℝ) *
        (Real.exp (-5 * ((b - a) - 1 / 128) / 2) /
          (1 - Real.exp (-2 * ((b - a) - 1 / 128)))) *
            (energy p.1 + energy q.1) := by
  let δ : ℝ := (b - a) - 1 / 128
  let E : ℝ := (energy p.1 + energy q.1) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hE : 0 ≤ E := by
    dsimp [E]
    have hp0 := energy_nonnegative p.1
    have hq0 := energy_nonnegative q.1
    positivity
  have hlogp : LogSupportIn p (a - 1 / 256) (a + 1 / 256) := hp
  have hlogq : LogSupportIn q (b - 1 / 256) (b + 1 / 256) := hq
  have harch := separated_arch_decay_any_positive_gap
    p q (a - 1 / 256) (a + 1 / 256)
      (b - 1 / 256) (b + 1 / 256) E
      hlogp hlogq δ hδ
      (by dsimp [δ]; linarith)
      (by ring)
      hm hE
      (fun u => distinct_logCross_norm_le_mean_energy p q u)
  dsimp [δ, E] at harch ⊢
  convert harch using 1; ring

/-- True separated mixed Weil coefficient at every positive support gap.
The prime sum remains explicit, while the moment-zero Arch term carries
its exact fine-window width and exponential decay. -/
theorem distinct_fine_actual_B_any_positive_gap
    (p q : WeilCompactSmoothGV1) (a b : ℝ)
    (hp : WidthOneOneTwentyEightAt p a)
    (hq : WidthOneOneTwentyEightAt q b)
    (hm : WeilMomentConditionsV1 p)
    (hsep : (1 / 128 : ℝ) < b - a) :
    ‖B p q‖ ≤ ‖WeilPrimeSumV1 (mixed p q)‖ +
      (1 / 128 : ℝ) *
        (Real.exp (-5 * ((b - a) - 1 / 128) / 2) /
          (1 - Real.exp (-2 * ((b - a) - 1 / 128)))) *
            (energy p.1 + energy q.1) := by
  have hlog : logCrossV28 p q 0 = 0 := by
    apply logCross_zero_outside p q
      (a - 1 / 256) (a + 1 / 256)
      (b - 1 / 256) (b + 1 / 256) 0 hp hq
    right
    linarith
  have hcenter : mixed p q 1 = 0 := by
    have h := logCross_eq_mixed_v28 p q 0
    simp only [zero_div, Real.exp_zero, Complex.ofReal_one, one_mul] at h
    exact h.symm.trans hlog
  have harch :=
    distinct_fine_arch_decay_any_positive_gap p q a b hp hq hm hsep
  have heq : B p q =
      WeilPrimeSumV1 (mixed p q) +
        WeilArchimedeanIntegralV1 (mixed p q) := by
    unfold B WeilExplicitRightSideV1
    rw [hcenter]
    ring
  rw [heq]
  exact (norm_add_le _ _).trans (add_le_add le_rfl harch)

/-- Actual distant ARCH bound after using the zero Mellin moment,
for different fine packets supported near centers a and b. The
right-hand side decreases exponentially with b-a. -/
theorem distinct_fine_far_arch_moment_decay
    (p q : WeilCompactSmoothGV1) (a b : ℝ)
    (hp : WidthOneOneTwentyEightAt p a)
    (hq : WidthOneOneTwentyEightAt q b)
    (hm : WeilMomentConditionsV1 p)
    (hgap : Real.log 2 ≤ b - a) :
    ‖WeilArchimedeanIntegralV1 (mixed p q)‖ ≤
      (1 / 32 : ℝ) *
        (Real.exp (-5 * ((b-a)-1/32) / 2) /
          (1 - Real.exp (-2 * ((b-a)-1/32)))) *
            (energy p.1 + energy q.1) := by
  let δ : ℝ := (b-a)-1/32
  let E : ℝ := (energy p.1 + energy q.1)/2
  have hδ : 0 < δ := by
    dsimp [δ]
    linarith [hgap, log_two_gt_one_thirty_two]
  have hE : 0 ≤ E := by
    dsimp [E]
    have hp0 := energy_nonnegative p.1
    have hq0 := energy_nonnegative q.1
    positivity
  have hlogp :
      LogSupportIn p (a - 1 / 64) (a + 1 / 64) := by
    intro t ht
    obtain ⟨hlo, hhi⟩ := hp ht
    exact ⟨by linarith, by linarith⟩
  have hlogq :
      LogSupportIn q (b - 1 / 64) (b + 1 / 64) := by
    intro t ht
    obtain ⟨hlo, hhi⟩ := hq ht
    exact ⟨by linarith, by linarith⟩
  have harch := separated_arch_decay_bound
    p q (a - 1 / 64) (a + 1 / 64)
      (b - 1 / 64) (b + 1 / 64) E
      hlogp hlogq (by linarith)
      δ hδ (by dsimp [δ]; linarith)
      (by norm_num [CorrelationSupportDifferenceWidthV31]; ring)
      hm hE
      (fun u => distinct_logCross_norm_le_mean_energy p q u)
  dsimp [E, δ] at harch ⊢
  convert harch using 1; ring


/-- The entire genuine distant Weil coefficient inherits the moment-zero
exponential Archimedean decay, *retaining* the von Mangoldt prime term.
This sharpens the constant 1/200 bound for sufficiently distant centers;
no bound for the remaining prime term is assumed or asserted. -/
theorem distinct_fine_far_actual_B_norm_le_prime_plus_moment_decay
    (p q : WeilCompactSmoothGV1) (a b : ℝ)
    (hp : WidthOneOneTwentyEightAt p a)
    (hq : WidthOneOneTwentyEightAt q b)
    (hm : WeilMomentConditionsV1 p)
    (hgap : Real.log 2 ≤ b - a) :
    ‖B p q‖ ≤ ‖WeilPrimeSumV1 (mixed p q)‖ +
      (1 / 32 : ℝ) *
        (Real.exp (-5 * ((b-a)-1/32) / 2) /
          (1 - Real.exp (-2 * ((b-a)-1/32)))) *
            (energy p.1 + energy q.1) := by
  have hzero := distinct_fine_far_mixed_one_zero p q a b hp hq hgap
  have harch := distinct_fine_far_arch_moment_decay p q a b hp hq hm hgap
  have heq : B p q =
      WeilPrimeSumV1 (mixed p q) +
        WeilArchimedeanIntegralV1 (mixed p q) := by
    unfold B WeilExplicitRightSideV1
    rw [hzero]
    ring
  rw [heq]
  exact (norm_add_le _ _).trans (add_le_add le_rfl harch)

/-- Convert an analytic estimate on the *prime part alone* into an
outward Q16.16 bound on the actual distant mixed Weil coefficient.
The source-pinned moment-zero Archimedean remainder is budgeted exactly,
not silently dropped. The prime estimate remains an explicit obligation. -/
theorem distinct_fine_far_actual_B_q16_of_prime_decay_budget
    (p q : WeilCompactSmoothGV1) (a b : ℝ)
    (hp : WidthOneOneTwentyEightAt p a)
    (hq : WidthOneOneTwentyEightAt q b)
    (hm : WeilMomentConditionsV1 p)
    (hgap : Real.log 2 ≤ b - a) (k : ℕ)
    (hprime :
      ‖WeilPrimeSumV1 (mixed p q)‖ ≤
        ((k : ℝ) / 65536 -
          (1 / 32 : ℝ) *
            (Real.exp (-5 * ((b-a)-1/32) / 2) /
              (1 - Real.exp (-2 * ((b-a)-1/32))))) *
          (energy p.1 + energy q.1)) :
    ‖B p q‖ ≤ ((k : ℝ) / 65536) *
      (energy p.1 + energy q.1) := by
  have h := distinct_fine_far_actual_B_norm_le_prime_plus_moment_decay
    p q a b hp hq hm hgap
  calc
    ‖B p q‖ ≤ ‖WeilPrimeSumV1 (mixed p q)‖ +
        (1 / 32 : ℝ) *
          (Real.exp (-5 * ((b-a)-1/32) / 2) /
            (1 - Real.exp (-2 * ((b-a)-1/32)))) *
              (energy p.1 + energy q.1) := h
    _ ≤ (((k : ℝ) / 65536 -
          (1 / 32 : ℝ) *
            (Real.exp (-5 * ((b-a)-1/32) / 2) /
              (1 - Real.exp (-2 * ((b-a)-1/32))))) *
          (energy p.1 + energy q.1)) +
        (1 / 32 : ℝ) *
          (Real.exp (-5 * ((b-a)-1/32) / 2) /
            (1 - Real.exp (-2 * ((b-a)-1/32)))) *
              (energy p.1 + energy q.1) :=
                add_le_add hprime le_rfl
    _ = ((k : ℝ) / 65536) * (energy p.1 + energy q.1) := by ring


/-- Pure rational Q16.16 combination rule for separated actual Weil atoms.
The moment-zero Arch remainder is charged by an outward certified rational
bound, and the genuine von Mangoldt prime term has its own independent cost.
No floating-point evaluation and no assumed sign of the prime term. -/
theorem distinct_fine_far_actual_B_q16_of_separate_rational_budgets
    (p q : WeilCompactSmoothGV1) (a b : ℝ)
    (hp : WidthOneOneTwentyEightAt p a)
    (hq : WidthOneOneTwentyEightAt q b)
    (hm : WeilMomentConditionsV1 p)
    (hgap : Real.log 2 ≤ b - a)
    (primeCost archCost : ℕ)
    (hprime :
      ‖WeilPrimeSumV1 (mixed p q)‖ ≤
        ((primeCost : ℝ) / 65536) *
          (energy p.1 + energy q.1))
    (hdecay :
      (1 / 32 : ℝ) *
        (Real.exp (-5 * ((b-a)-1/32) / 2) /
          (1 - Real.exp (-2 * ((b-a)-1/32)))) ≤
        (archCost : ℝ) / 65536) :
    ‖B p q‖ ≤ (((primeCost + archCost : ℕ) : ℝ) / 65536) *
      (energy p.1 + energy q.1) := by
  have hE : 0 ≤ energy p.1 + energy q.1 :=
    add_nonneg (energy_nonnegative p.1) (energy_nonnegative q.1)
  have harch := mul_le_mul_of_nonneg_right hdecay hE
  have hactual := distinct_fine_far_actual_B_norm_le_prime_plus_moment_decay
    p q a b hp hq hm hgap
  calc
    ‖B p q‖ ≤ ‖WeilPrimeSumV1 (mixed p q)‖ +
      (1 / 32 : ℝ) *
        (Real.exp (-5 * ((b-a)-1/32) / 2) /
          (1 - Real.exp (-2 * ((b-a)-1/32)))) *
            (energy p.1 + energy q.1) := hactual
    _ ≤ ((primeCost : ℝ) / 65536) *
          (energy p.1 + energy q.1) +
        ((archCost : ℝ) / 65536) *
          (energy p.1 + energy q.1) := add_le_add hprime harch
    _ = (((primeCost + archCost : ℕ) : ℝ) / 65536) *
          (energy p.1 + energy q.1) := by
            push_cast
            ring



/-- A fully rational, floating-point-free upper certificate for the
moment-zero Archimedean kernel when the exponential arguments are ≥5
and ≥4 respectively. The proof uses the quadratic Taylor *lower*
bound on the positive exponential, not numerical evaluation. -/
theorem moment_zero_arch_rational_exp_bound
    (x y : ℝ) (hx : 5 ≤ x) (hy : 4 ≤ y) :
    (1 / 32 : ℝ) * (Real.exp (-x) / (1 - Real.exp (-y))) ≤
      (120 / 65536 : ℝ) := by
  have hx0 : 0 ≤ x := by linarith
  have hy0 : 0 ≤ y := by linarith
  have hxexp : (37 / 2 : ℝ) ≤ Real.exp x := by
    have hq := Real.quadratic_le_exp_of_nonneg hx0
    have hp : (37 / 2 : ℝ) ≤ 1 + x + x ^ 2 / 2 := by
      nlinarith [sq_nonneg (x - 5)]
    exact hp.trans hq
  have hyexp : (13 : ℝ) ≤ Real.exp y := by
    have hq := Real.quadratic_le_exp_of_nonneg hy0
    have hp : (13 : ℝ) ≤ 1 + y + y ^ 2 / 2 := by
      nlinarith [sq_nonneg (y - 4)]
    exact hp.trans hq
  have hxpair : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add]
    simp
  have hypair : Real.exp y * Real.exp (-y) = 1 := by
    rw [← Real.exp_add]
    simp
  have hxupper : Real.exp (-x) ≤ (2 / 37 : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right hxexp (Real.exp_nonneg (-x))
    rw [hxpair] at hmul
    nlinarith
  have hyupper : Real.exp (-y) ≤ (1 / 13 : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right hyexp (Real.exp_nonneg (-y))
    rw [hypair] at hmul
    nlinarith
  have hden : 0 < 1 - Real.exp (-y) := by linarith
  have hratio :
      Real.exp (-x) / (1 - Real.exp (-y)) ≤ (13 / 222 : ℝ) := by
    apply (div_le_iff₀ hden).mpr
    linarith
  have hmul := mul_le_mul_of_nonneg_left hratio
    (by norm_num : (0 : ℝ) ≤ 1 / 32)
  nlinarith

/-- The full true distant mixed Weil form, with Archimedean contribution
admitted at exactly 120/65536 for log-center gap at least 65/32.
Any outstanding von Mangoldt estimate stays explicit. -/
theorem distinct_fine_far_actual_B_q16_prime_plus_120
    (p q : WeilCompactSmoothGV1) (a b : ℝ)
    (hp : WidthOneOneTwentyEightAt p a)
    (hq : WidthOneOneTwentyEightAt q b)
    (hm : WeilMomentConditionsV1 p)
    (hgap : Real.log 2 ≤ b - a)
    (hfar : (65 / 32 : ℝ) ≤ b - a)
    (primeCost : ℕ)
    (hprime : ‖WeilPrimeSumV1 (mixed p q)‖ ≤
      ((primeCost : ℝ) / 65536) *
        (energy p.1 + energy q.1)) :
    ‖B p q‖ ≤ (((primeCost + 120 : ℕ) : ℝ) / 65536) *
      (energy p.1 + energy q.1) := by
  have hx : (5 : ℝ) ≤ 5 * ((b-a)-1/32) / 2 := by
    linarith
  have hy : (4 : ℝ) ≤ 2 * ((b-a)-1/32) := by
    linarith
  have hr := moment_zero_arch_rational_exp_bound
    (5 * ((b-a)-1/32) / 2) (2 * ((b-a)-1/32)) hx hy
  have hdecay :
      (1 / 32 : ℝ) *
        (Real.exp (-5 * ((b-a)-1/32) / 2) /
          (1 - Real.exp (-2 * ((b-a)-1/32)))) ≤
            (120 / 65536 : ℝ) := by
    convert hr using 1; congr 2 <;> ring
  exact distinct_fine_far_actual_B_q16_of_separate_rational_budgets
    p q a b hp hq hm hgap primeCost 120 hprime hdecay


/-! ## Exact exponential-to-geometric bridge for moment-zero ARCH

For centers separated by at least 65/32 per index increment,
the rank-one-cancelled Arch contribution decays geometrically with
index distance. No prime-sum inequality is assumed or concluded.
-/

/-- A rational geometric majorant for the moment-zero Arch remainder
at every positive integer gap, without floating-point evaluation. -/
theorem moment_zero_arch_decay_geometric
    (δ : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hδ : 2 * (k : ℝ) ≤ δ) :
    (1 / 32 : ℝ) *
      (Real.exp (-5 * δ / 2) / (1 - Real.exp (-2 * δ))) ≤
        (13 / 384 : ℝ) * ((2 / 37 : ℝ) ^ k) := by
  have hkreal : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have htwo : (2 : ℝ) ≤ δ := by nlinarith
  have he5 : (37 / 2 : ℝ) ≤ Real.exp 5 := by
    have h := Real.quadratic_le_exp_of_nonneg
      (by norm_num : (0 : ℝ) ≤ 5)
    norm_num at h
    exact h
  have he4 : (13 : ℝ) ≤ Real.exp 4 := by
    have h := Real.quadratic_le_exp_of_nonneg
      (by norm_num : (0 : ℝ) ≤ 4)
    norm_num at h
    exact h
  have hprod5 : Real.exp 5 * Real.exp (-5) = 1 := by
    rw [← Real.exp_add]
    norm_num
  have hprod4 : Real.exp 4 * Real.exp (-4) = 1 := by
    rw [← Real.exp_add]
    norm_num
  have hneg5 : Real.exp (-5) ≤ (2 / 37 : ℝ) := by
    have hm := mul_le_mul_of_nonneg_right he5 (Real.exp_nonneg (-5))
    rw [hprod5] at hm
    nlinarith
  have hneg4 : Real.exp (-4) ≤ (1 / 13 : ℝ) := by
    have hm := mul_le_mul_of_nonneg_right he4 (Real.exp_nonneg (-4))
    rw [hprod4] at hm
    nlinarith
  have hdenbound : Real.exp (-2 * δ) ≤ (1 / 13 : ℝ) := by
    exact (Real.exp_le_exp.mpr (by linarith : -2 * δ ≤ -4)).trans hneg4
  have hden : (12 / 13 : ℝ) ≤ 1 - Real.exp (-2 * δ) := by
    linarith
  have hdenpos : 0 < 1 - Real.exp (-2 * δ) := by linarith
  have hpow :
      Real.exp (-(5 * (k : ℝ))) = (Real.exp (-5)) ^ k := by
    calc
      Real.exp (-(5 * (k : ℝ))) =
          Real.exp ((k : ℝ) * (-5)) := by congr 1; ring
      _ = (Real.exp (-5)) ^ k := Real.exp_nat_mul (-5) k
  have hnum :
      Real.exp (-5 * δ / 2) ≤ (2 / 37 : ℝ) ^ k := by
    calc
      Real.exp (-5 * δ / 2) ≤
          Real.exp (-(5 * (k : ℝ))) :=
        Real.exp_le_exp.mpr (by linarith)
      _ = (Real.exp (-5)) ^ k := hpow
      _ ≤ (2 / 37 : ℝ) ^ k :=
        pow_le_pow_left₀ (Real.exp_nonneg _) hneg5 k
  have hratio :
      Real.exp (-5 * δ / 2) / (1 - Real.exp (-2 * δ)) ≤
        ((2 / 37 : ℝ) ^ k) / (12 / 13) := by
    apply (div_le_div_iff₀ hdenpos (by norm_num : (0 : ℝ) < 12 / 13)).mpr
    calc
      Real.exp (-5 * δ / 2) * (12 / 13) ≤
          ((2 / 37 : ℝ) ^ k) * (12 / 13) :=
        mul_le_mul_of_nonneg_right hnum (by norm_num)
      _ ≤ ((2 / 37 : ℝ) ^ k) *
          (1 - Real.exp (-2 * δ)) :=
        mul_le_mul_of_nonneg_left hden
          (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2 / 37) k)
  calc
    (1 / 32 : ℝ) *
      (Real.exp (-5 * δ / 2) / (1 - Real.exp (-2 * δ))) ≤
        (1 / 32 : ℝ) * (((2 / 37 : ℝ) ^ k) / (12 / 13)) :=
      mul_le_mul_of_nonneg_left hratio (by norm_num)
    _ = (13 / 384 : ℝ) * ((2 / 37 : ℝ) ^ k) := by ring

/-- Direct actual Weil-Arch cross bound, indexed by the integer
separation of two fine moment-zero packets. This is the analytic
pair-to-geometric interface used by a dimension-free row certificate. -/
theorem distinct_fine_far_actual_arch_geometric
    (p q : WeilCompactSmoothGV1) (a b : ℝ)
    (hp : WidthOneOneTwentyEightAt p a)
    (hq : WidthOneOneTwentyEightAt q b)
    (hm : WeilMomentConditionsV1 p)
    (k : ℕ) (hk : 1 ≤ k)
    (hsep : (65 / 32 : ℝ) * (k : ℝ) ≤ b - a) :
    ‖WeilArchimedeanIntegralV1 (mixed p q)‖ ≤
      ((13 / 384 : ℝ) * ((2 / 37 : ℝ) ^ k)) *
        (energy p.1 + energy q.1) := by
  have hkreal : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hlog : Real.log 2 ≤ b - a := by
    linarith [AEGIS.WeilThreeBlockAnalyticConstantsV21.log_two_upper]
  have hδ : 2 * (k : ℝ) ≤ (b - a) - 1 / 32 := by
    nlinarith
  have harch := distinct_fine_far_arch_moment_decay
    p q a b hp hq hm hlog
  have hcost := moment_zero_arch_decay_geometric
    ((b - a) - 1 / 32) k hk hδ
  have henergy : 0 ≤ energy p.1 + energy q.1 :=
    add_nonneg (energy_nonnegative p.1) (energy_nonnegative q.1)
  exact harch.trans (mul_le_mul_of_nonneg_right hcost henergy)



/-- Full exact distant Weil-pair bound using the rational geometric
moment-zero Arch envelope. The genuine von Mangoldt prime contribution
remains explicit: this lemma does NOT assert a bound on that prime term. -/
theorem distinct_fine_far_actual_B_norm_le_prime_plus_geometric_arch
    (p q : WeilCompactSmoothGV1) (a b : ℝ)
    (hp : WidthOneOneTwentyEightAt p a)
    (hq : WidthOneOneTwentyEightAt q b)
    (hm : WeilMomentConditionsV1 p)
    (k : ℕ) (hk : 1 ≤ k)
    (hsep : (65 / 32 : ℝ) * (k : ℝ) ≤ b - a) :
    ‖B p q‖ ≤ ‖WeilPrimeSumV1 (mixed p q)‖ +
      ((13 / 384 : ℝ) * ((2 / 37 : ℝ) ^ k)) *
        (energy p.1 + energy q.1) := by
  have hkreal : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hgap : Real.log 2 ≤ b - a := by
    linarith [AEGIS.WeilThreeBlockAnalyticConstantsV21.log_two_upper]
  have hzero :=
    distinct_fine_far_mixed_one_zero p q a b hp hq hgap
  have harch :=
    distinct_fine_far_actual_arch_geometric p q a b hp hq hm k hk hsep
  have heq :
      B p q = WeilPrimeSumV1 (mixed p q) +
        WeilArchimedeanIntegralV1 (mixed p q) := by
    unfold B WeilExplicitRightSideV1
    rw [hzero]
    ring
  rw [heq]
  exact (norm_add_le _ _).trans (add_le_add le_rfl harch)



/-! ## Finite signed actual-Weil counterpart at common half-width 9/64

No entrywise mixed norm budget, no special mother packet, and no bound
on the number of atoms. Unlike a diagonal-only result, this retains
the entire signed Weil Gram contraction and the existing moment-zero
hypotheses. The atoms must share one common 9/64 window. -/

/-- An arbitrary complex linear combination of actual Weil atoms in
one common radius-9/64 window remains in that radius-9/64 window. -/
theorem nine_window_packetSum :
    ∀ (n : ℕ) (z : Fin (n + 1) → ℂ)
      (gs : Fin (n + 1) → WeilCompactSmoothGV1) (center : ℝ),
      (∀ i, AEGIS.RHDyadicDiagonalV13.HalfWidthAt
        (gs i) (9 / 64) center) →
      AEGIS.RHDyadicDiagonalV13.HalfWidthAt
        (packetSum z gs) (9 / 64) center := by
  intro n
  induction n with
  | zero =>
      intro z gs center hwin
      change AEGIS.RHDyadicDiagonalV13.HalfWidthAt
        (scalePacket (z 0) (gs 0)) (9 / 64) center
      exact nine_width_scale (gs 0) (z 0) center (hwin 0)
  | succ n ih =>
      intro z gs center hwin
      change AEGIS.RHDyadicDiagonalV13.HalfWidthAt
        (addPacket
          (packetSum (fun i : Fin (n + 1) => z i.castSucc)
            (fun i : Fin (n + 1) => gs i.castSucc))
          (scalePacket (z (Fin.last (n + 1)))
            (gs (Fin.last (n + 1))))) (9 / 64) center
      exact nine_width_add _ _ center
        (ih (fun i => z i.castSucc) (fun i => gs i.castSucc)
          center (fun i => hwin i.castSucc))
        (nine_width_scale _ _ center (hwin (Fin.last (n + 1))))

/-- Moment-zero conditions are closed under any finite complex
packetSum; all constituent packets are genuine Weil test packets. -/
theorem nine_moment_packetSum :
    ∀ (n : ℕ) (z : Fin (n + 1) → ℂ)
      (gs : Fin (n + 1) → WeilCompactSmoothGV1),
      (∀ i, WeilMomentConditionsV1 (gs i)) →
      WeilMomentConditionsV1 (packetSum z gs) := by
  intro n
  induction n with
  | zero =>
      intro z gs hm
      change WeilMomentConditionsV1 (scalePacket (z 0) (gs 0))
      exact momentConditions_scalePacket_v10 (z 0) (gs 0) (hm 0)
  | succ n ih =>
      intro z gs hm
      change WeilMomentConditionsV1
        (addPacket
          (packetSum (fun i : Fin (n + 1) => z i.castSucc)
            (fun i : Fin (n + 1) => gs i.castSucc))
          (scalePacket (z (Fin.last (n + 1)))
            (gs (Fin.last (n + 1)))))
      exact momentConditions_addPacket_v10 _ _
        (ih (fun i => z i.castSucc) (fun i => gs i.castSucc)
          (fun i => hm i.castSucc))
        (momentConditions_scalePacket_v10 _ _ (hm (Fin.last (n + 1))))

/-- Genuine full signed Weil Gram coercivity for ANY finite complex
linear combination of DIFFERENT moment-zero atoms sharing one 9/64
logarithmic window. No pairwise mixed-term bounds are hypotheses. -/
theorem nine_local_exact_counterpart
    (n : ℕ) (z : Fin (n + 1) → ℂ)
    (gs : Fin (n + 1) → WeilCompactSmoothGV1) (center : ℝ)
    (hm : ∀ i, WeilMomentConditionsV1 (gs i))
    (hwin : ∀ i, AEGIS.RHDyadicDiagonalV13.HalfWidthAt
      (gs i) (9 / 64) center) :
    (1 / 10 : ℝ) * energy (packetSum z gs).1 ≤
      -(B (packetSum z gs) (packetSum z gs)).re := by
  have hmSum := nine_moment_packetSum n z gs hm
  have hwSum := nine_window_packetSum n z gs center hwin
  have h := AEGIS.RHWindowNineOver64GlobalizationV14.nine_over_64_coercive
    (packetSum z gs) center hwSum hmSum
  change (B (packetSum z gs) (packetSum z gs)).re ≤
    -(1 / 10 : ℝ) * energy (packetSum z gs).1 at h
  linarith

/-- Exact opposite-side signed mixed-defect bound for arbitrarily many
atoms on a common 9/64 window; no Gershgorin norm majorant is needed. -/
theorem nine_local_exact_mixed_defect_opposite
    (n : ℕ) (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (center : ℝ)
    (hm : ∀ i, WeilMomentConditionsV1 (gs i))
    (hwin : ∀ i, AEGIS.RHDyadicDiagonalV13.HalfWidthAt
      (gs i) (9 / 64) center) :
    actualMixedDefect n gs ≤
      -((1 / 10 : ℝ) *
        energy (packetSum (fun _ => (1 : ℂ)) gs).1) -
      ∑ i, (B (gs i) (gs i)).re := by
  have hcoercive :=
    nine_local_exact_counterpart n (fun _ => (1 : ℂ)) gs center hm hwin
  have hgram :
      (B (packetSum (fun _ => (1 : ℂ)) gs)
        (packetSum (fun _ => (1 : ℂ)) gs)).re =
        (∑ i, ∑ j, B (gs i) (gs j)).re := by
    rw [B_packetSum]
    simp
  rw [hgram] at hcoercive
  unfold actualMixedDefect
  linarith



/-- A fine Weil atom can move to an explicitly different common
9/64 window whenever its local center is at most 35/256 away.
The radius arithmetic is exact: 1/256 + 35/256 = 9/64. -/
theorem fine_width_into_common_nine
    (u : WeilCompactSmoothGV1) (a center : ℝ)
    (hu : WidthOneOneTwentyEightAt u a)
    (hcenter : |a - center| ≤ (35 / 256 : ℝ)) :
    AEGIS.RHDyadicDiagonalV13.HalfWidthAt u (9 / 64) center := by
  change tsupport (lift u.1) ⊆
    Icc (center - 9 / 64) (center + 9 / 64)
  change tsupport (lift u.1) ⊆
    Icc (a - 1 / 256) (a + 1 / 256) at hu
  intro t ht
  obtain ⟨hlo, hhi⟩ := hu ht
  obtain ⟨haclo, hachi⟩ := abs_le.mp hcenter
  constructor <;> linarith

/-- Arbitrarily many different fine moment-zero atoms with centers
in one 35/256 neighborhood have the exact signed radius-9/64 Weil
coercivity, for arbitrary complex coefficients. No common mother
packet, equal energy, pairwise cross-majorant or fixed n is assumed. -/
theorem fine_cluster_nine_exact_counterpart
    (n : ℕ) (z : Fin (n + 1) → ℂ)
    (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (centers : Fin (n + 1) → ℝ) (center : ℝ)
    (hm : ∀ i, WeilMomentConditionsV1 (gs i))
    (hw : ∀ i, WidthOneOneTwentyEightAt (gs i) (centers i))
    (hnear : ∀ i, |centers i - center| ≤ (35 / 256 : ℝ)) :
    (1 / 10 : ℝ) * energy (packetSum z gs).1 ≤
      -(B (packetSum z gs) (packetSum z gs)).re := by
  apply nine_local_exact_counterpart n z gs center hm
  intro i
  exact fine_width_into_common_nine (gs i) (centers i)
    center (hw i) (hnear i)

/-- Signed opposite-side mixed-defect counterpart for a finite
fine cluster with distinct source centers. -/
theorem fine_cluster_nine_mixed_defect_opposite
    (n : ℕ) (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (centers : Fin (n + 1) → ℝ) (center : ℝ)
    (hm : ∀ i, WeilMomentConditionsV1 (gs i))
    (hw : ∀ i, WidthOneOneTwentyEightAt (gs i) (centers i))
    (hnear : ∀ i, |centers i - center| ≤ (35 / 256 : ℝ)) :
    actualMixedDefect n gs ≤
      -((1 / 10 : ℝ) *
        energy (packetSum (fun _ => (1 : ℂ)) gs).1) -
      ∑ i, (B (gs i) (gs i)).re := by
  apply nine_local_exact_mixed_defect_opposite n gs center hm
  intro i
  exact fine_width_into_common_nine (gs i) (centers i)
    center (hw i) (hnear i)


/-! ## Exact prime-side localization in the missing intermediate log gap

The genuine WeilPrimeTermV1 has BOTH samples m and m⁻¹.
The support-difference window for two distinct fine packets is
(a-b)-1/128 ≤ u ≤ (a-b)+1/128. When b-a > 1/128, the positive
sample m vanishes automatically. The reciprocal sample only survives
when log m lies within 1/128 of b-a. This theorem retains that exact
discrete obstruction rather than postulating a prime-energy bound. -/

/-- If a fine packet pair has a strictly positive support gap and
the integer logarithm misses its correlation window, both actual
multiplicative Weil samples vanish. No special mother packet. -/
theorem distinct_fine_prime_samples_vanish_of_integer_log_gap
    (p q : WeilCompactSmoothGV1) (a b : ℝ)
    (hp : WidthOneOneTwentyEightAt p a)
    (hq : WidthOneOneTwentyEightAt q b)
    (hsep : (1 / 128 : ℝ) < b - a)
    (m : ℕ) (hm : 0 < m)
    (havoid : (1 / 128 : ℝ) <
      |Real.log (m : ℝ) - (b - a)|) :
    mixed p q (m : ℝ) = 0 ∧
      mixed p q ((m : ℝ)⁻¹) = 0 := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hmone : (1 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast (show 1 ≤ m by omega)
  have hlog0 : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hmone
  have hpI : LogSupportIn p (a - 1 / 256) (a + 1 / 256) := hp
  have hqI : LogSupportIn q (b - 1 / 256) (b + 1 / 256) := hq
  have hpos : logCrossV28 p q (Real.log (m : ℝ)) = 0 := by
    apply logCross_zero_outside p q
      (a - 1 / 256) (a + 1 / 256)
      (b - 1 / 256) (b + 1 / 256) (Real.log (m : ℝ)) hpI hqI
    right
    linarith
  have hrealpos : mixed p q (m : ℝ) = 0 := by
    rw [logCross_eq_mixed_v28, Real.exp_log hmR] at hpos
    exact (mul_eq_zero.mp hpos).resolve_left (by simp)
  have hsplit :
      Real.log (m : ℝ) - (b - a) < -(1 / 128 : ℝ) ∨
        (1 / 128 : ℝ) < Real.log (m : ℝ) - (b - a) := by
    by_cases hlow :
        Real.log (m : ℝ) - (b - a) < -(1 / 128 : ℝ)
    · exact Or.inl hlow
    · right
      by_contra hhigh
      have hlo : -(1 / 128 : ℝ) ≤
          Real.log (m : ℝ) - (b - a) := le_of_not_gt hlow
      have hhi : Real.log (m : ℝ) - (b - a) ≤
          (1 / 128 : ℝ) := le_of_not_gt hhigh
      have habs : |Real.log (m : ℝ) - (b - a)| ≤
          (1 / 128 : ℝ) := abs_le.mpr ⟨hlo, hhi⟩
      linarith
  have hinv : logCrossV28 p q (-Real.log (m : ℝ)) = 0 := by
    apply logCross_zero_outside p q
      (a - 1 / 256) (a + 1 / 256)
      (b - 1 / 256) (b + 1 / 256) (-Real.log (m : ℝ)) hpI hqI
    rcases hsplit with hlow | hhigh
    · right; linarith
    · left; linarith
  have hrealinv : mixed p q ((m : ℝ)⁻¹) = 0 := by
    rw [logCross_eq_mixed_v28,
      Real.exp_neg, Real.exp_log hmR] at hinv
    exact (mul_eq_zero.mp hinv).resolve_left (by simp)
  exact ⟨hrealpos, hrealinv⟩

/-- The FULL genuine von Mangoldt series vanishes if the finite
correlation window meets no integer logarithm. In particular this
does not discard any prime-power term: every summand is exactly zero.
The condition explicitly remains an obligation on b-a. -/
theorem distinct_fine_actual_prime_zero_of_integer_log_gap
    (p q : WeilCompactSmoothGV1) (a b : ℝ)
    (hp : WidthOneOneTwentyEightAt p a)
    (hq : WidthOneOneTwentyEightAt q b)
    (hsep : (1 / 128 : ℝ) < b - a)
    (havoid : ∀ m : ℕ, 0 < m →
      (1 / 128 : ℝ) < |Real.log (m : ℝ) - (b - a)|) :
    WeilPrimeSumV1 (mixed p q) = 0 := by
  have hterm : ∀ n : ℕ, WeilPrimeTermV1 (mixed p q) n = 0 := by
    intro n
    have hm : 0 < n + 1 := by omega
    obtain ⟨hpos, hinv⟩ :=
      distinct_fine_prime_samples_vanish_of_integer_log_gap
        p q a b hp hq hsep (n + 1) hm (havoid (n + 1) hm)
    simp only [WeilPrimeTermV1, hpos, hinv,
      mul_zero, add_zero]
  unfold WeilPrimeSumV1
  simp only [hterm, tsum_zero]

/-- On every integer-log-free fine separation, the real actual Weil
interaction is purely Archimedean and has the proven moment-zero
decay. This is an unconditional equality of genuine B coefficients
given explicit geometric/log-gap hypotheses, not an RH certificate. -/
theorem distinct_fine_actual_B_of_integer_log_gap
    (p q : WeilCompactSmoothGV1) (a b : ℝ)
    (hp : WidthOneOneTwentyEightAt p a)
    (hq : WidthOneOneTwentyEightAt q b)
    (hm : WeilMomentConditionsV1 p)
    (hsep : (1 / 128 : ℝ) < b - a)
    (havoid : ∀ m : ℕ, 0 < m →
      (1 / 128 : ℝ) < |Real.log (m : ℝ) - (b - a)|) :
    ‖B p q‖ ≤
      (1 / 128 : ℝ) *
        (Real.exp (-5 * ((b - a) - 1 / 128) / 2) /
          (1 - Real.exp (-2 * ((b - a) - 1 / 128)))) *
          (energy p.1 + energy q.1) := by
  have hzero := distinct_fine_actual_prime_zero_of_integer_log_gap
    p q a b hp hq hsep havoid
  have hbound := distinct_fine_actual_B_any_positive_gap
    p q a b hp hq hm hsep
  rw [hzero] at hbound
  simpa using hbound


/-- Below the first nontrivial integer logarithm, every integer sample
misses a separated fine correlation window. -/
theorem integer_log_avoids_below_log_two
    (d : ℝ) (hlow : (1 / 128 : ℝ) < d)
    (hhigh : d < Real.log 2 - (1 / 128 : ℝ)) :
    ∀ m : ℕ, 0 < m → (1 / 128 : ℝ) < |Real.log (m : ℝ) - d| := by
  intro m hm
  by_cases hm1 : m = 1
  · subst m
    simp only [Nat.cast_one, Real.log_one, zero_sub, abs_neg]
    rw [abs_of_pos (by linarith : 0 < d)]
    exact hlow
  · have hm2 : 2 ≤ m := by omega
    have hreal : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
    have hlog : Real.log (2 : ℝ) ≤ Real.log (m : ℝ) :=
      Real.log_le_log (by norm_num : (0 : ℝ) < 2) hreal
    rw [abs_of_nonneg (by linarith : 0 ≤ Real.log (m : ℝ) - d)]
    linarith

/-- The entire genuine prime-power contribution vanishes on separated
fine windows below log 2; no integer-log exclusion is assumed. -/
theorem distinct_fine_prime_zero_below_log_two
    (p q : WeilCompactSmoothGV1) (a b : ℝ)
    (hp : WidthOneOneTwentyEightAt p a)
    (hq : WidthOneOneTwentyEightAt q b)
    (hlow : (1 / 128 : ℝ) < b - a)
    (hhigh : b - a < Real.log 2 - (1 / 128 : ℝ)) :
    WeilPrimeSumV1 (mixed p q) = 0 := by
  exact distinct_fine_actual_prime_zero_of_integer_log_gap p q a b hp hq hlow
    (integer_log_avoids_below_log_two (b - a) hlow hhigh)

/-- Actual mixed Weil interaction on the sub-log-2 interval: all prime
samples are zero, leaving the source-bound moment-zero Arch decay. -/
theorem distinct_fine_actual_B_below_log_two
    (p q : WeilCompactSmoothGV1) (a b : ℝ)
    (hp : WidthOneOneTwentyEightAt p a)
    (hq : WidthOneOneTwentyEightAt q b)
    (hm : WeilMomentConditionsV1 p)
    (hlow : (1 / 128 : ℝ) < b - a)
    (hhigh : b - a < Real.log 2 - (1 / 128 : ℝ)) :
    ‖B p q‖ ≤
      (1 / 128 : ℝ) *
        (Real.exp (-5 * ((b - a) - 1 / 128) / 2) /
          (1 - Real.exp (-2 * ((b - a) - 1 / 128)))) *
          (energy p.1 + energy q.1) := by
  exact distinct_fine_actual_B_of_integer_log_gap p q a b hp hq hm hlow
    (integer_log_avoids_below_log_two (b - a) hlow hhigh)

/-- A floating-point-free Q16.16 Arch certificate for the intermediate
fine gap. Quadratic Taylor lower bounds give the outward cost 676. -/
theorem moment_zero_fine_middle_arch_q16 (δ : ℝ) (hδ : (17 / 64 : ℝ) ≤ δ) :
    (1 / 128 : ℝ) *
      (Real.exp (-5 * δ / 2) / (1 - Real.exp (-2 * δ))) ≤
      (676 / 65536 : ℝ) := by
  have hx : (85 / 128 : ℝ) ≤ 5 * δ / 2 := by linarith
  have hy : (17 / 32 : ℝ) ≤ 2 * δ := by linarith
  have hxexp : (61753 / 32768 : ℝ) ≤ Real.exp (5 * δ / 2) := by
    have hq := Real.quadratic_le_exp_of_nonneg (by linarith : 0 ≤ 5 * δ / 2)
    have hp : (61753 / 32768 : ℝ) ≤ 1 + 5 * δ / 2 + (5 * δ / 2) ^ 2 / 2 := by
      nlinarith [sq_nonneg (5 * δ / 2 - 85 / 128)]
    exact hp.trans hq
  have hyexp : (3425 / 2048 : ℝ) ≤ Real.exp (2 * δ) := by
    have hq := Real.quadratic_le_exp_of_nonneg (by linarith : 0 ≤ 2 * δ)
    have hp : (3425 / 2048 : ℝ) ≤ 1 + 2 * δ + (2 * δ) ^ 2 / 2 := by
      nlinarith [sq_nonneg (2 * δ - 17 / 32)]
    exact hp.trans hq
  have hxpair : Real.exp (5 * δ / 2) * Real.exp (-5 * δ / 2) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    congr 1
    ring
  have hypair : Real.exp (2 * δ) * Real.exp (-2 * δ) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    congr 1
    ring
  have hxupper : Real.exp (-5 * δ / 2) ≤ (32768 / 61753 : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right hxexp (Real.exp_nonneg (-5 * δ / 2))
    rw [hxpair] at hmul
    nlinarith
  have hyupper : Real.exp (-2 * δ) ≤ (2048 / 3425 : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right hyexp (Real.exp_nonneg (-2 * δ))
    rw [hypair] at hmul
    nlinarith
  have hden : 0 < 1 - Real.exp (-2 * δ) := by linarith
  have hratio : Real.exp (-5 * δ / 2) / (1 - Real.exp (-2 * δ)) ≤
      (169 / 128 : ℝ) := by
    apply (div_le_iff₀ hden).mpr
    linarith
  have hmul := mul_le_mul_of_nonneg_left hratio (by norm_num : (0 : ℝ) ≤ 1 / 128)
  nlinarith

/-- Actual mixed Weil Q16.16 certificate for different fine atoms of
arbitrary energies in the intermediate interval below log 2. Every prime
sample is proved zero; the Arch remainder is charged, not discarded. -/
theorem distinct_fine_actual_B_q16_middle_gap
    (p q : WeilCompactSmoothGV1) (a b : ℝ)
    (hp : WidthOneOneTwentyEightAt p a)
    (hq : WidthOneOneTwentyEightAt q b)
    (hm : WeilMomentConditionsV1 p)
    (hlow : (35 / 128 : ℝ) ≤ b - a)
    (hhigh : b - a < Real.log 2 - (1 / 128 : ℝ)) :
    ‖B p q‖ ≤ (676 / 65536 : ℝ) * (energy p.1 + energy q.1) := by
  have hactual := distinct_fine_actual_B_below_log_two
    p q a b hp hq hm (by linarith) hhigh
  have hkernel := moment_zero_fine_middle_arch_q16
    ((b - a) - 1 / 128) (by linarith)
  exact hactual.trans (mul_le_mul_of_nonneg_right hkernel
    (add_nonneg (energy_nonnegative p.1) (energy_nonnegative q.1)))

/-- The first explicit integer-log-free middle interval, between the
two neighboring prime logarithms log 2 and log 3. No universally
quantified exclusion certificate is required from the caller. -/
theorem distinct_fine_prime_zero_between_log_two_three
    (p q : WeilCompactSmoothGV1) (a b : ℝ)
    (hp : WidthOneOneTwentyEightAt p a)
    (hq : WidthOneOneTwentyEightAt q b)
    (hlow : Real.log 2 + (1 / 128 : ℝ) < b - a)
    (hhigh : b - a < Real.log 3 - (1 / 128 : ℝ)) :
    WeilPrimeSumV1 (mixed p q) = 0 := by
  have hlog2 : 0 < Real.log (2 : ℝ) :=
    Real.log_pos (by norm_num : (1 : ℝ) < 2)
  apply distinct_fine_actual_prime_zero_of_integer_log_gap
    p q a b hp hq (by linarith)
  intro m hm
  by_cases hm1 : m = 1
  · subst m
    simp only [Nat.cast_one, Real.log_one, zero_sub, abs_neg]
    rw [abs_of_pos (by linarith : 0 < b - a)]
    linarith
  by_cases hm2 : m = 2
  · subst m
    norm_num only [Nat.cast_ofNat]
    have hneg : Real.log (2 : ℝ) - (b - a) < 0 := by linarith
    rw [abs_of_neg hneg]
    linarith
  · have hm3 : 3 ≤ m := by omega
    have hreal : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm3
    have hlog3 : Real.log (3 : ℝ) ≤ Real.log (m : ℝ) :=
      Real.log_le_log (by norm_num : (0 : ℝ) < 3) hreal
    have hpos : 0 ≤ Real.log (m : ℝ) - (b - a) := by linarith
    rw [abs_of_nonneg hpos]
    linarith

/-- Genuine full Weil mixed B, with exact moment-zero Arch decay and
exactly zero von Mangoldt sum, for every fine pair whose centers lie
strictly between the log-2 and log-3 sampling windows. -/
theorem distinct_fine_actual_B_between_log_two_three
    (p q : WeilCompactSmoothGV1) (a b : ℝ)
    (hp : WidthOneOneTwentyEightAt p a)
    (hq : WidthOneOneTwentyEightAt q b)
    (hm : WeilMomentConditionsV1 p)
    (hlow : Real.log 2 + (1 / 128 : ℝ) < b - a)
    (hhigh : b - a < Real.log 3 - (1 / 128 : ℝ)) :
    ‖B p q‖ ≤
      (1 / 128 : ℝ) *
        (Real.exp (-5 * ((b - a) - 1 / 128) / 2) /
          (1 - Real.exp (-2 * ((b - a) - 1 / 128)))) *
          (energy p.1 + energy q.1) := by
  apply distinct_fine_actual_B_of_integer_log_gap p q a b hp hq hm
  · linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  · intro m hm
    by_cases hm1 : m = 1
    · subst m
      simp only [Nat.cast_one, Real.log_one, zero_sub, abs_neg]
      rw [abs_of_pos (by linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)] : 0 < b - a)]
      linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
    by_cases hm2 : m = 2
    · subst m
      norm_num only [Nat.cast_ofNat]
      have hneg : Real.log (2 : ℝ) - (b - a) < 0 := by linarith
      rw [abs_of_neg hneg]
      linarith
    · have hm3 : 3 ≤ m := by omega
      have hreal : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm3
      have hlog3 : Real.log (3 : ℝ) ≤ Real.log (m : ℝ) :=
        Real.log_le_log (by norm_num : (0 : ℝ) < 3) hreal
      have hpos : 0 ≤ Real.log (m : ℝ) - (b - a) := by linarith
      rw [abs_of_nonneg hpos]
      linarith


/-- Exact actual-Weil Q16.16 certificate in the SECOND prime-log-free
window (strictly between log 2 and log 3). The zero prime component is
source-proven, while the Arch component is charged at 676/65536.
The lower separation is kept explicit, so no unverified real-log
inequality is needed in this source theorem. -/
theorem distinct_fine_actual_B_q16_between_log_two_three
    (p q : WeilCompactSmoothGV1) (a b : ℝ)
    (hp : WidthOneOneTwentyEightAt p a)
    (hq : WidthOneOneTwentyEightAt q b)
    (hm : WeilMomentConditionsV1 p)
    (hsep : (35 / 128 : ℝ) ≤ b - a)
    (hlo : Real.log 2 + (1 / 128 : ℝ) < b - a)
    (hhi : b - a < Real.log 3 - (1 / 128 : ℝ)) :
    ‖B p q‖ ≤ (676 / 65536 : ℝ) *
      (energy p.1 + energy q.1) := by
  have hactual := distinct_fine_actual_B_between_log_two_three
    p q a b hp hq hm hlo hhi
  have hkernel := moment_zero_fine_middle_arch_q16
    ((b - a) - 1 / 128) (by linarith)
  exact hactual.trans (mul_le_mul_of_nonneg_right hkernel
    (add_nonneg (energy_nonnegative p.1) (energy_nonnegative q.1)))

/-- Both prime-log-free intervals at the same genuine-Weil Q16.16
price, for arbitrary moment-zero fine atoms (no same-mother requirement).
This covers the intermediate support-gap and the log-2/log-3 gap.
No resonance claim is made outside these explicit intervals. -/
theorem distinct_fine_actual_B_q16_first_two_log_free_windows
    (p q : WeilCompactSmoothGV1) (a b : ℝ)
    (hp : WidthOneOneTwentyEightAt p a)
    (hq : WidthOneOneTwentyEightAt q b)
    (hm : WeilMomentConditionsV1 p)
    (hsep : (35 / 128 : ℝ) ≤ b - a)
    (hfree :
      b - a < Real.log 2 - (1 / 128 : ℝ) ∨
      (Real.log 2 + (1 / 128 : ℝ) < b - a ∧
        b - a < Real.log 3 - (1 / 128 : ℝ))) :
    ‖B p q‖ ≤ (676 / 65536 : ℝ) *
      (energy p.1 + energy q.1) := by
  rcases hfree with hbefore | ⟨hafter, hbeforeThree⟩
  · exact distinct_fine_actual_B_q16_middle_gap
      p q a b hp hq hm hsep hbefore
  · exact distinct_fine_actual_B_q16_between_log_two_three
      p q a b hp hq hm hsep hafter hbeforeThree

end AEGIS.RHActualMixedDefectV1

#print axioms AEGIS.RHActualMixedDefectV1.quantitative_lower_of_diagonal
#print axioms AEGIS.RHActualMixedDefectV1.every_packet_actual_mixed_defect_bound
#print axioms AEGIS.RHActualMixedDefectV1.actual_zero_sign_of_paid_mixed_defect
#print axioms AEGIS.RHActualMixedDefectV1.narrow_width_scale
#print axioms AEGIS.RHActualMixedDefectV1.narrow_width_add
#print axioms AEGIS.RHActualMixedDefectV1.actual_mixed_re_upper_of_narrow_sum
#print axioms AEGIS.RHActualMixedDefectV1.actual_mixed_re_abs_of_common_narrow_window
#print axioms AEGIS.RHActualMixedDefectV1.actual_mixed_norm_le_of_common_narrow_window
#print axioms AEGIS.RHActualMixedDefectV1.actual_nine_over_64_mixed_re_upper
#print axioms AEGIS.RHActualMixedDefectV1.actual_nine_over_64_mixed_re_abs
#print axioms AEGIS.RHActualMixedDefectV1.actual_nine_over_64_mixed_norm_le

#print axioms AEGIS.RHActualMixedDefectV1.fine_width_scale
#print axioms AEGIS.RHActualMixedDefectV1.fine_width_add
#print axioms AEGIS.RHActualMixedDefectV1.fine_width_packetSum
#print axioms AEGIS.RHActualMixedDefectV1.fine_local_exact_counterpart
#print axioms AEGIS.RHActualMixedDefectV1.fine_local_q16_counterpart
#print axioms AEGIS.RHActualMixedDefectV1.fine_local_exact_mixed_defect_opposite

#print axioms AEGIS.RHActualMixedDefectV1.fine_width_into_nine_midpoint
#print axioms AEGIS.RHActualMixedDefectV1.nearby_fine_pair_shared_nine_window
#print axioms AEGIS.RHActualMixedDefectV1.nearby_fine_pair_actual_mixed_signed
#print axioms AEGIS.RHActualMixedDefectV1.nearby_fine_pair_actual_mixed_q16
#print axioms AEGIS.RHActualMixedDefectV1.nearby_fine_pair_actual_mixed_norm

#print axioms AEGIS.RHActualMixedDefectV1.distinct_logCross_norm_le_mean_energy
#print axioms AEGIS.RHActualMixedDefectV1.distinct_fine_far_arch_norm_le

#print axioms AEGIS.RHActualMixedDefectV1.distinct_fine_far_mixed_one_zero
#print axioms AEGIS.RHActualMixedDefectV1.distinct_fine_far_actual_B_norm_le_prime_plus_arch

#print axioms AEGIS.RHActualMixedDefectV1.separated_arch_decay_bound
#print axioms AEGIS.RHActualMixedDefectV1.distinct_fine_far_arch_moment_decay
#print axioms AEGIS.RHActualMixedDefectV1.separated_arch_decay_any_positive_gap
#print axioms AEGIS.RHActualMixedDefectV1.distinct_fine_arch_decay_any_positive_gap
#print axioms AEGIS.RHActualMixedDefectV1.distinct_fine_actual_B_any_positive_gap
#print axioms AEGIS.RHActualMixedDefectV1.distinct_fine_far_actual_B_norm_le_prime_plus_moment_decay
#print axioms AEGIS.RHActualMixedDefectV1.distinct_fine_far_actual_B_q16_of_prime_decay_budget
#print axioms AEGIS.RHActualMixedDefectV1.distinct_fine_far_actual_B_q16_of_separate_rational_budgets
#print axioms AEGIS.RHActualMixedDefectV1.moment_zero_arch_rational_exp_bound
#print axioms AEGIS.RHActualMixedDefectV1.distinct_fine_far_actual_B_q16_prime_plus_120

#print axioms AEGIS.RHActualMixedDefectV1.moment_zero_arch_decay_geometric
#print axioms AEGIS.RHActualMixedDefectV1.distinct_fine_far_actual_arch_geometric
#print axioms AEGIS.RHActualMixedDefectV1.distinct_fine_far_actual_B_norm_le_prime_plus_geometric_arch
#print axioms AEGIS.RHActualMixedDefectV1.nine_window_packetSum
#print axioms AEGIS.RHActualMixedDefectV1.nine_moment_packetSum
#print axioms AEGIS.RHActualMixedDefectV1.nine_local_exact_counterpart
#print axioms AEGIS.RHActualMixedDefectV1.nine_local_exact_mixed_defect_opposite
#print axioms AEGIS.RHActualMixedDefectV1.fine_width_into_common_nine
#print axioms AEGIS.RHActualMixedDefectV1.fine_cluster_nine_exact_counterpart
#print axioms AEGIS.RHActualMixedDefectV1.fine_cluster_nine_mixed_defect_opposite
#print axioms AEGIS.RHActualMixedDefectV1.distinct_fine_prime_samples_vanish_of_integer_log_gap
#print axioms AEGIS.RHActualMixedDefectV1.distinct_fine_actual_prime_zero_of_integer_log_gap
#print axioms AEGIS.RHActualMixedDefectV1.distinct_fine_actual_B_of_integer_log_gap
#print axioms AEGIS.RHActualMixedDefectV1.distinct_fine_prime_zero_between_log_two_three
#print axioms AEGIS.RHActualMixedDefectV1.distinct_fine_actual_B_q16_between_log_two_three
#print axioms AEGIS.RHActualMixedDefectV1.distinct_fine_actual_B_q16_first_two_log_free_windows
#print axioms AEGIS.RHActualMixedDefectV1.distinct_fine_actual_B_between_log_two_three

#print axioms AEGIS.RHActualMixedDefectV1.integer_log_avoids_below_log_two
#print axioms AEGIS.RHActualMixedDefectV1.distinct_fine_prime_zero_below_log_two
#print axioms AEGIS.RHActualMixedDefectV1.distinct_fine_actual_B_below_log_two

#print axioms AEGIS.RHActualMixedDefectV1.moment_zero_fine_middle_arch_q16
#print axioms AEGIS.RHActualMixedDefectV1.distinct_fine_actual_B_q16_middle_gap
