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

import AEGISOverlay.RHNarrowFixedDetectorV1
import RHMomentDecayCofinalJoinV1
import RHCofinalActualTerminalV1
import RHRestrictedWeilBridgeV13
import RHNineFacesV13

/-!
# Five-source RH spine — source-exact join across repository branches

The narrow detecting packet and its Mellin witness are copied, unchanged,
from formal-conjectures PR #47 (6b279c390e1dab535b435acaba2ff73ff358e2ca).
The Nine Faces file is the exact Git blob from AEGIS-OMEGA PR #679, already
present at the AEGIS source pin used by this fork's successful PR #83 replay.

This module COMPOSES existing kernel-level interfaces. The cofinal family
producer remains an explicit parameter; the Nine Faces are equivalences.
-/

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHCrossRepositoryFiveSpineV1

open AEGIS.RHNarrowFixedDetectorV1
open AEGIS.RHCofinalActualTerminalV1
open AEGIS.WeilZeroTwoPointV11

/-- The same narrow compact-smooth packet carries the moment constraints and
detects each nontrivial zeta zero, with no new construction. -/
theorem narrow_packet_moments_and_detection :
    WeilMomentConditionsV1 narrowDetectingPacket ∧
    (∀ rho : RiemannNontrivialZeroIndexV2,
      WeilZeroCoefficientV11 narrowDetectingPacket rho ≠ 0) :=
  ⟨narrowDetectingPacket_moments, narrowDetectingPacket_detects⟩

/-- Reuse the existing unconditional local sign of exactly that detector. -/
theorem narrow_packet_local_actual_arithmetic_sign :
    (WeilExplicitRightSideV1
      (WeilAutocorrelationV1 narrowDetectingPacket)).re ≤ 0 :=
  narrowDetectingPacket_arithmetic_nonpositive

/-- The cofinal moment/actual-zero join is instantiated on the fixed detector,
without switching to another test-packet representation. -/
theorem narrow_packet_actual_zero_of_cofinal
    (h : EveryPacketCofinalLowerCertificate) :
    0 ≤ (∑' rho : RiemannNontrivialZeroIndexV2,
      WeilZeroIndexSummandV1
        (WeilAutocorrelationV1 narrowDetectingPacket) rho).re :=
  (universal_of_cofinal_lower_certificates h)
    narrowDetectingPacket narrowDetectingPacket_moments

/-- The pre-existing Nine Faces interfaces consume the very same cofinal
actual-zero certificate through the fork's kernel-checked RH terminal. -/
theorem three_nine_faces_of_cofinal
    (h : EveryPacketCofinalLowerCertificate) :
    AEGIS.RHMillenniumGateV10.RHMillenniumCertificateV10 ∧
    AEGIS.WeilWindowExhaustionV1.UniversalArithmeticNonpositiveV1 ∧
    (∀ n : ℕ, 0 < n →
      AEGIS.WeilWindowExhaustionV1.WindowArithmeticNonpositiveV1 (n : ℝ)) := by
  have hRH : RiemannHypothesis :=
    riemannHypothesis_of_cofinal_lower_certificates h
  exact ⟨AEGIS.RHNineFacesV13.rh_iff_certificate_v13.mp hRH,
    AEGIS.RHNineFacesV13.rh_iff_universal_arithmetic_v13.mp hRH,
    AEGIS.RHNineFacesV13.rh_iff_nat_windows_v13.mp hRH⟩

end AEGIS.RHCrossRepositoryFiveSpineV1

#print axioms AEGIS.RHCrossRepositoryFiveSpineV1.narrow_packet_moments_and_detection
#print axioms AEGIS.RHCrossRepositoryFiveSpineV1.narrow_packet_local_actual_arithmetic_sign
#print axioms AEGIS.RHCrossRepositoryFiveSpineV1.narrow_packet_actual_zero_of_cofinal
#print axioms AEGIS.RHCrossRepositoryFiveSpineV1.three_nine_faces_of_cofinal
