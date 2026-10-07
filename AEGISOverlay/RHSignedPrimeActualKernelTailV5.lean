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

import RHPrimeOnlyReflectedTailV3
import WeilSignedPrimeEventualBridgeV1
import RHBoundedKernelCriterionV14

/-!
# Verified-source signed-prime versus reflected zero-kernel tail

This small consumer proves the *actual* signed-prime/B/zero-kernel remainder
bound, rather than postulating it. It uses only archived, source-bound Lean
theorems for B-S on separated translations and K_g(-d) = -B(g,T_d g).

The Chebyshev convolution dictionary is kept as a separate explicit
mathematical input. Subexponential growth remains a second input; neither
is silently asserted unconditionally.

All imported archival source objects are pinned by the source SHA verified
in the workflow prior to kernel compilation.
RH_PROVEN_UNCONDITIONALLY = false.
AUTHORITY_EFFECT = NONE.
-/

open Set Complex
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHSignedPrimeActualKernelTailV5

open AEGIS.WeilZeroTwoPointV11
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.WeilWindowExhaustionV1
open AEGIS.WeilDisjointEnergyV2
open AEGIS.WeilGeneralSignedKernelBoundV1
open AEGIS.WeilSignedKernelReductionV1
open AEGIS.RHBoundedKernelCriterionV14
open AEGIS.RHFixedPacketFrontierV1
open AEGIS.RHPrimeOnlyGrowthBridgeV1
open AEGIS.RHPrimeOnlyReflectedTailV3
open AEGIS.RHSubexpBoundedPerturbationV1

/-- The exact archive's B-S estimate and K(-d)=-B(T_d g) identity supply
the bounded remainder on a positive translation tail for the real source. -/
theorem signed_prime_reflected_zero_kernel_tail_bounded
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g) :
    ∃ T D : ℝ, 0 ≤ D ∧
      ∀ t : ℝ, T ≤ t →
        ‖-WeilZeroTranslationKernelV11 g (-t) -
          SignedPrimeCorrelationV1 g t‖ ≤ D := by
  obtain ⟨L, hL, hw⟩ := logLift_has_finite_window_v1 g
  let D : ℝ := 4 * (L - -L) * energy g.1
  have hD : 0 ≤ D := by
    dsimp [D]
    exact mul_nonneg (mul_nonneg (by norm_num) (by linarith))
      (energy_nonnegative g.1)
  refine ⟨(L - -L) + 1, D, hD, ?_⟩
  intro t ht
  have hB :=
    B_sub_signed_prime_norm_le_support_energy_v1
      g (-L) L 0 t (by linarith) hw (by simpa using ht)
  have hZero : translatePacket g 0 = g := by
    apply Subtype.ext
    funext x
    simp [translatePacket_apply]
  simp only [hZero, sub_zero] at hB
  have hK :=
    zero_kernel_v11_eq_neg_actual_B_v14 g hm (-t)
  simp only [neg_neg] at hK
  rw [hK]
  simpa only [neg_neg] using hB

/-- Exact remaining dictionary between the archived finite signed-prime
orbit and the already-defined Chebyshev full-psi convolution. This statement
only requires equality beyond a finite shift threshold. -/
def EventuallySignedPrimeEqualsCombinedOrbitV5 : Prop :=
  ∃ T : ℝ, ∀ t : ℝ, T ≤ t →
    SignedPrimeCorrelationV1 detectingPacket t =
      combinedArithmeticOrbitV1 detectingPacket t

/-- The archive's proved B-S and K=-B bounds discharge the previously
assumed eventual reflected arithmetic remainder once the dictionary holds. -/
theorem eventual_reflected_remainder_of_signed_dictionary
    (hDictionary : EventuallySignedPrimeEqualsCombinedOrbitV5) :
    EventuallyReflectedFixedKernelArithmeticRemainderBoundedV3 := by
  obtain ⟨T₁, D, hD, hTail⟩ :=
    signed_prime_reflected_zero_kernel_tail_bounded
      detectingPacket detectingPacket_moments
  obtain ⟨T₂, hEq⟩ := hDictionary
  refine ⟨max T₁ T₂, D, hD, ?_⟩
  intro t ht
  have ht₁ : T₁ ≤ t := (le_max_left _ _).trans ht
  have ht₂ : T₂ ≤ t := (le_max_right _ _).trans ht
  rw [← hEq t ht₂]
  exact hTail t ht₁

/-- The actual RH target follows from only the exact signed-prime/Chebyshev
dictionary and the separate prime-only growth estimate. -/
theorem riemannHypothesis_of_signed_dictionary_and_prime_growth
    (hDictionary : EventuallySignedPrimeEqualsCombinedOrbitV5)
    (hPrime : SubexponentialAtTopV1 (primeOnlyOrbitV1 detectingPacket)) :
    RiemannHypothesis :=
  riemannHypothesis_of_prime_only_growth_and_eventual_reflected_bridge
    hPrime (eventual_reflected_remainder_of_signed_dictionary hDictionary)

end AEGIS.RHSignedPrimeActualKernelTailV5

#print axioms AEGIS.RHSignedPrimeActualKernelTailV5.signed_prime_reflected_zero_kernel_tail_bounded
#print axioms AEGIS.RHSignedPrimeActualKernelTailV5.eventual_reflected_remainder_of_signed_dictionary
#print axioms AEGIS.RHSignedPrimeActualKernelTailV5.riemannHypothesis_of_signed_dictionary_and_prime_growth
