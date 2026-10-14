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

import AEGISOverlay.RHNarrowEventualTailV1
import RHNineFacesV13

/-!
# The same narrow detector across all nine RH formulations

The fixed narrow detecting packet on PR #47 is used verbatim.
The forward direction reuses the pinned AEGIS RH → universal Weil
positivity theorem. The converse reuses the kernel-checked detecting
packet criterion and eventual-tail compactness reduction.

This proves equivalences, not an unconditional proof of their statements.
The RH↔all-windows and RH↔certificate implications are the exact
RHNineFacesV13 declarations at AEGIS PR #679.
-/

set_option autoImplicit false
noncomputable section

open Set
namespace AEGIS.RHNarrowNineFacesBridgeV1

open AEGIS.RHNarrowFixedDetectorV1
open AEGIS.RHNarrowEventualTailV1
open AEGIS.WeilZeroTwoPointV11
open AEGIS.WeilAutocorrelationExplicitFormulaV10

/-- Under the exact Mathlib RH, every two-point translated packet
    of the *same* narrow detector has the four-phase Weil sign. -/
theorem narrow_four_phase_sign_of_rh (hRH : RiemannHypothesis) :
    AEGIS.RHFixedPacketFourPhaseV1.FixedPacketFourPhaseSignV1
      narrowDetectingPacket := by
  intro d c _hc
  have hm : WeilMomentConditionsV1
      (WeilTwoPointTranslateV11 narrowDetectingPacket d c) :=
    AEGIS.WeilZeroKernelHermitianV11.twoPointTranslate_preserves_moments_v11
      narrowDetectingPacket d c narrowDetectingPacket_moments
  exact
    (autocorrelation_arithmetic_nonpositive_iff_zero_nonnegative_v10
      (WeilTwoPointTranslateV11 narrowDetectingPacket d c) hm).mpr
        ((AEGIS.WeilRHImpliesFinalSignV13.rh_implies_universal_v13 hRH)
          (WeilTwoPointTranslateV11 narrowDetectingPacket d c) hm)

/-- Exact global boundedness of the one narrow detector follows from RH. -/
theorem narrow_kernel_bound_of_rh (hRH : RiemannHypothesis) :
    AEGIS.RHDetectingPacketCriterionV1.PacketKernelBoundV1
      narrowDetectingPacket :=
  AEGIS.RHFixedPacketFourPhaseV1.fixed_packet_four_phase_implies_bounded_zero_kernel
    narrowDetectingPacket narrowDetectingPacket_moments
    (narrow_four_phase_sign_of_rh hRH)

/-- The fixed narrow detecting packet is an exact one-packet RH criterion. -/
theorem rh_iff_narrow_kernel_bound :
    RiemannHypothesis ↔
      AEGIS.RHDetectingPacketCriterionV1.PacketKernelBoundV1
        narrowDetectingPacket :=
  ⟨narrow_kernel_bound_of_rh,
   riemannHypothesis_of_narrow_kernel_bound⟩

/-- Using the imported compactness + Hermitian reflection lemma, the
    *positive-tail* criterion is also equivalent to RH, for the same g. -/
theorem rh_iff_narrow_eventual_tail :
    RiemannHypothesis ↔ NarrowKernelEventuallyBoundedV1 := by
  constructor
  · intro hRH
    obtain ⟨C, hC⟩ := narrow_kernel_bound_of_rh hRH
    exact ⟨0, C, fun t _ht => hC t⟩
  · exact riemannHypothesis_of_narrow_eventual_bound

/-- Cross-repository junction: one fixed narrow kernel tail ↔ all
    positive Weil windows, using RHNineFacesV13 from PR #679. -/
theorem narrow_eventual_tail_iff_all_windows :
    NarrowKernelEventuallyBoundedV1 ↔
      ∀ L : ℝ, 0 < L →
        AEGIS.WeilWindowExhaustionV1.WindowArithmeticNonpositiveV1 L :=
  rh_iff_narrow_eventual_tail.symm.trans
    AEGIS.RHNineFacesV13.rh_iff_all_windows_v13

/-- Cross-repository junction to the full RH Millennium certificate. -/
theorem narrow_eventual_tail_iff_millennium_certificate :
    NarrowKernelEventuallyBoundedV1 ↔
      AEGIS.RHMillenniumGateV10.RHMillenniumCertificateV10 :=
  rh_iff_narrow_eventual_tail.symm.trans
    AEGIS.RHNineFacesV13.rh_iff_certificate_v13

end AEGIS.RHNarrowNineFacesBridgeV1

#print axioms AEGIS.RHNarrowNineFacesBridgeV1.narrow_four_phase_sign_of_rh
#print axioms AEGIS.RHNarrowNineFacesBridgeV1.narrow_kernel_bound_of_rh
#print axioms AEGIS.RHNarrowNineFacesBridgeV1.rh_iff_narrow_kernel_bound
#print axioms AEGIS.RHNarrowNineFacesBridgeV1.rh_iff_narrow_eventual_tail
#print axioms AEGIS.RHNarrowNineFacesBridgeV1.narrow_eventual_tail_iff_all_windows
#print axioms AEGIS.RHNarrowNineFacesBridgeV1.narrow_eventual_tail_iff_millennium_certificate
