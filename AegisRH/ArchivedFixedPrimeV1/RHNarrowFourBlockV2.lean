import RHNarrowMomentPacketV1
import WeilThreeBlockPrimeEvaluationV30
import WeilSeparatedArchBridgeV31
import Mathlib.Tactic

/-!
AEGIS Ω — corrected narrow four-block producer candidates V2.

SOURCE-BOUND CANDIDATE ONLY.
This file has NOT been Lean-replayed in the current environment.
It contains no `sorry`, `admit`, custom axiom, or `native_decide`.

The immediately checkable goals are:
1. expose the actual 1/80 support radius of gNarrow;
2. define the 1/40 total-width packet predicate;
3. record the exact rational four-block comparison certificate.

The analytic and m=8 producers are specified in RESEARCH_NOTE_V2.md and remain
separate obligations until exact-head Lean replay.
-/

open Set MeasureTheory Complex
open scoped ContDiff ComplexConjugate BigOperators

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHNarrowFourBlockV2

open AEGIS.WeilMomentKillerConstructionV1
open AEGIS.WeilLogCoordinateIsometryV21
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.WeilWidthArchCorrelationV25
open AEGIS.RHNarrowMomentPacketV1

/-- Actual narrow packet predicate: support radius 1/80, total packet width 1/40. -/
def WidthOneFortiethAt (g : WeilCompactSmoothGV1) (a : ℝ) : Prop :=
  tsupport (logLift g.1) ⊆
    Icc (a - (1 / 80 : ℝ)) (a + (1 / 80 : ℝ))

/-- `momentKiller` preserves the actual 1/80 seed support; the old 1/64 theorem
was only a relaxation into the generic width-1/32 interface. -/
theorem phiNarrow_tsupport_one_over_80_v2 :
    tsupport phiNarrow ⊆ Icc (-(1 / 80) : ℝ) (1 / 80) := by
  refine (tsupport_momentKiller_subset psiNarrow).trans ?_
  rw [psiNarrow_tsupport, Real.closedBall_eq_Icc]
  exact Icc_subset_Icc (by norm_num) (by norm_num)

/-- Exact log-lift support for the canonical packet. -/
theorem gNarrow_logLift_support_one_over_80_v2 :
    tsupport (logLift gNarrow.1) ⊆
      Icc (-(1 / 80) : ℝ) (1 / 80) := by
  apply closure_minimal
  · intro t ht
    by_contra hout
    have hphi : phiNarrow t = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hmem
      exact hout (phiNarrow_tsupport_one_over_80_v2 hmem)
    apply ht
    rw [logLift_gNarrow_apply, hphi]
    simp
  · exact isClosed_Icc

theorem gNarrow_width_one_fortieth_v2 :
    WidthOneFortiethAt gNarrow 0 := by
  change tsupport (logLift gNarrow.1) ⊆
    Icc (0 - (1 / 80 : ℝ)) (0 + (1 / 80 : ℝ))
  simpa using gNarrow_logLift_support_one_over_80_v2

/-- The narrow support implies autocorrelation vanishing outside total
difference-support radius 1/40. -/
theorem logCorrelation_zero_of_narrow_width_abs_v2
    (g : WeilCompactSmoothGV1) (a u : ℝ)
    (hw : WidthOneFortiethAt g a)
    (hu : (1 / 40 : ℝ) < |u|) :
    logCorrelationV25 g u = 0 := by
  unfold logCorrelationV25
  apply integral_eq_zero_of_ae
  filter_upwards [] with v
  by_cases h0 : logLift g.1 v = 0
  · simp [h0]
  · by_cases h1 : logLift g.1 (v + u) = 0
    · simp [h1]
    · have hm0 : v ∈ tsupport (logLift g.1) := subset_tsupport _ h0
      have hm1 : v + u ∈ tsupport (logLift g.1) := subset_tsupport _ h1
      have hv := hw hm0
      have hvu := hw hm1
      have habs : |u| ≤ (1 / 40 : ℝ) := by
        rw [abs_le]
        constructor <;> linarith [hv.1, hv.2, hvu.1, hvu.2]
      exact False.elim ((not_le_of_gt hu) habs)

/-- Exact scalar certificate consumed after diagonal/cross estimates are
attached to the actual four B-entries. -/
theorem four_block_comparison_sos_v2
    (r0 r1 r2 r3 : ℝ) :
    2 * ((127 : ℝ) / 250) * (r0*r1 + r1*r2 + r2*r3) +
      2 * ((44 : ℝ) / 125) * (r0*r2 + r1*r3) +
      2 * ((251 : ℝ) / 1000) * (r0*r3)
      ≤
    ((5 : ℝ) / 4) * (r0^2 + r1^2 + r2^2 + r3^2) := by
  let s : ℝ := r0 + r3
  let t : ℝ := r1 + r2
  let u : ℝ := r0 - r3
  let v : ℝ := r1 - r2
  have hS :
      0 ≤ 999*s^2 - 1720*s*t + 742*t^2 := by
    have hsq :
        0 ≤ (999*s - 860*t)^2 + 1658*t^2 := by positivity
    nlinarith
  have hA :
      0 ≤ 1501*u^2 - 312*u*v + 1758*v^2 := by
    have hsq :
        0 ≤ (1501*u - 156*v)^2 + 2614422*v^2 := by positivity
    nlinarith
  dsimp [s, t, u, v] at hS hA
  nlinarith

end AEGIS.RHNarrowFourBlockV2

#print axioms AEGIS.RHNarrowFourBlockV2.phiNarrow_tsupport_one_over_80_v2
#print axioms AEGIS.RHNarrowFourBlockV2.gNarrow_logLift_support_one_over_80_v2
#print axioms AEGIS.RHNarrowFourBlockV2.logCorrelation_zero_of_narrow_width_abs_v2
#print axioms AEGIS.RHNarrowFourBlockV2.four_block_comparison_sos_v2
