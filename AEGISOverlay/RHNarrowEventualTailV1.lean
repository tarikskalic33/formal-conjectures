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

import AEGISOverlay.RHNarrowCenteredKernelV1
import RHZeroKernelLaplaceAnalyticV12
import WeilZeroKernelHermitianV11
import Mathlib.Topology.Order.Compact

/-!
Exact-source reuse of the existing AEGISOverlay/RHFixedPacketEventualTailV1
proof from PR #83, blob 92af6b0ccb4bfd4d9057bbbbcf13f0064705e9bd.
Only the consuming detector is changed: all statements below use
RHNarrowFixedDetectorV1.narrowDetectingPacket.
-/

open Set
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHNarrowEventualTailV1
open AEGIS.RHNarrowFixedDetectorV1
open AEGIS.RHDetectingPacketCriterionV1
open AEGIS.RHZeroKernelLaplaceAnalyticV12
open AEGIS.WeilZeroTranslationV11
open AEGIS.WeilZeroTwoPointV11
open AEGIS.WeilZeroKernelHermitianV11

/-- Eventual boundedness on the positive translation tail. -/
def PacketKernelEventuallyBoundedV1 (g : WeilCompactSmoothGV1) : Prop :=
  ∃ T C : ℝ, ∀ t : ℝ, T ≤ t →
    ‖WeilZeroTranslationKernelV11 g t‖ ≤ C

/-- For a moment-zero packet, a positive-tail bound extends to a global bound.
The compact middle interval is controlled by continuity and the negative tail
is reflected to the positive tail by the exact Hermitian kernel identity. -/
theorem packetKernelBound_of_eventuallyBounded
    (g : WeilCompactSmoothGV1)
    (hm : WeilMomentConditionsV1 g)
    (h : PacketKernelEventuallyBoundedV1 g) :
    PacketKernelBoundV1 g := by
  obtain ⟨T, C, hC⟩ := h
  let R : ℝ := max 0 T
  have hTR : T ≤ R := by
    dsimp [R]
    exact le_max_right _ _

  have hcont :
      Continuous (fun t : ℝ => ‖WeilZeroTranslationKernelV11 g t‖) :=
    (zero_translation_kernel_continuous_v12 g).norm
  have hcompact :
      BddAbove
        ((fun t : ℝ => ‖WeilZeroTranslationKernelV11 g t‖) ''
          Icc (-R) R) :=
    isCompact_Icc.bddAbove_image hcont.continuousOn
  obtain ⟨M, hM⟩ := bddAbove_def.mp hcompact

  have hmid :
      ∀ t : ℝ, t ∈ Icc (-R) R →
        ‖WeilZeroTranslationKernelV11 g t‖ ≤ M := by
    intro t ht
    exact hM _ ⟨t, ht, rfl⟩

  refine ⟨max C M, ?_⟩
  intro t
  by_cases ht : t ∈ Icc (-R) R
  · exact (hmid t ht).trans (le_max_right _ _)
  · have hout : t < -R ∨ R < t := by
      rcases lt_or_ge t (-R) with hneg | hge
      · exact Or.inl hneg
      · right
        by_contra hnot
        exact ht ⟨hge, le_of_not_gt hnot⟩
    rcases hout with hneg | hpos
    · have hTneg : T ≤ -t := by
        have hRneg : R ≤ -t := by linarith
        exact hTR.trans hRneg
      have htail := hC (-t) hTneg
      have hsym :
          ‖WeilZeroTranslationKernelV11 g (-t)‖ =
            ‖WeilZeroTranslationKernelV11 g t‖ := by
        rw [zero_translation_kernel_neg_eq_conj_v11 g t hm]
        simp
      calc
        ‖WeilZeroTranslationKernelV11 g t‖ =
            ‖WeilZeroTranslationKernelV11 g (-t)‖ := hsym.symm
        _ ≤ C := htail
        _ ≤ max C M := le_max_left _ _
    · have hTt : T ≤ t := hTR.trans hpos.le
      exact (hC t hTt).trans (le_max_left _ _)


/-- The actual narrow detector's positive tail, not a freshly selected packet. -/
def NarrowKernelEventuallyBoundedV1 : Prop :=
  PacketKernelEventuallyBoundedV1 narrowDetectingPacket

/-- The already verified detection property identifies the exact RH target. -/
theorem riemannHypothesis_of_narrow_eventual_bound
    (h : NarrowKernelEventuallyBoundedV1) : RiemannHypothesis :=
  riemannHypothesis_of_narrow_kernel_bound
    (packetKernelBound_of_eventuallyBounded
      narrowDetectingPacket narrowDetectingPacket_moments h)

end AEGIS.RHNarrowEventualTailV1

#print axioms AEGIS.RHNarrowEventualTailV1.packetKernelBound_of_eventuallyBounded
#print axioms AEGIS.RHNarrowEventualTailV1.riemannHypothesis_of_narrow_eventual_bound
