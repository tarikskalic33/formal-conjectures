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

import AEGISOverlay.RHFourLogThreeActualPrimeV1

/-!
# Canonical RH endpoint of the genuine weighted four-log-three Weil Gram

Unlike the earlier all-ones sparse reconstruction, this allows arbitrary
complex amplitudes z. The reconstruction premise remains explicitly
source-preserving. It is NOT derived from generic finite Gram existence.
-/

open Complex
open scoped BigOperators
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHFourLogThreeWeightedRHBridgeV1

open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilDisjointEnergyV2
open AEGIS.RHGramExpansionV13
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.RHDyadicDiagonalV13

/-- Weighted sparse translation reconstruction: the source, coefficients,
atoms and exact arithmetic spacings must all match. This is a Prop,
not a supplied axiom or an unconditional existence theorem. -/
def HasWeightedFourLogThreeReconstruction
    (source : WeilCompactSmoothGV1) : Prop :=
  ∃ (n : ℕ) (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (z : Fin (n + 1) → ℂ)
    (center : Fin (n + 1) → ℝ)
    (K : ℕ) (mother : WeilCompactSmoothGV1) (a : ℝ),
    source = packetSum z gs ∧
    (∀ i, AEGIS.RHRationalNinePacketPrimeWindowV1.WidthOneOneTwentyEightAt
      (gs i) (center i)) ∧
    (∀ i, WeilMomentConditionsV1 (gs i)) ∧
    (∀ i j : Fin (n + 1), i < j →
      1 ≤ Nat.dist i j ∧
        (65 / 32 : ℝ) * (Nat.dist i j : ℝ) ≤ center j - center i) ∧
    HalfWidthAt mother
      (AEGIS.RHOptimizedSchurGlobalJoinV1.timeHorizonRadius K) a ∧
    (∀ i, gs i = translatePacket mother (center i)) ∧
    (∀ i j : Fin (n + 1), i < j →
      4 * Nat.dist i j ≤ K ∧
        center j - center i =
          ((4 * Nat.dist i j : ℕ) : ℝ) * Real.log 3)

/-- Any source with an ACTUAL weighted sparse reconstruction has the
nonpositive arithmetic Weil sign, with all complex mixed terms retained. -/
theorem weighted_reconstruction_arithmetic_nonpositive
    (source : WeilCompactSmoothGV1)
    (hreconstruction : HasWeightedFourLogThreeReconstruction source) :
    (WeilExplicitRightSideV1 (WeilAutocorrelationV1 source)).re ≤ 0 := by
  obtain ⟨n, gs, z, center, K, mother, a, hsource,
    hwidth, hm, hsep, hmother, hfamily, hgap⟩ := hreconstruction
  have hbound :=
    AEGIS.RHFourLogThreeActualPrimeV1.actual_four_log_three_weighted_norm_coercive
      gs center hwidth hm hsep K mother a hmother hfamily hgap z
  have henergy :
      0 ≤ (∑ i, energy (gs i).1 * ‖z i‖ ^ 2) := by
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (energy_nonnegative (gs i).1) (sq_nonneg _)
  rw [hsource]
  change (B (packetSum z gs) (packetSum z gs)).re ≤ 0
  nlinarith [hbound, henergy]

/-- Direct canonical Mathlib RiemannHypothesis endpoint, strictly
conditional on a source-preserving weighted reconstruction for EVERY
moment-zero source. No RH assumption is used in its proof. -/
theorem riemannHypothesis_of_weighted_four_log_three_reconstruction
    (hglobal : ∀ source : WeilCompactSmoothGV1,
      WeilMomentConditionsV1 source →
        HasWeightedFourLogThreeReconstruction source) :
    RiemannHypothesis := by
  apply AEGIS.RHRestrictedWeilBridgeV13.final_sign_implies_rh_v13
  intro source _hm
  exact weighted_reconstruction_arithmetic_nonpositive source
    (hglobal source _hm)

end AEGIS.RHFourLogThreeWeightedRHBridgeV1

#print axioms AEGIS.RHFourLogThreeWeightedRHBridgeV1.weighted_reconstruction_arithmetic_nonpositive
#print axioms AEGIS.RHFourLogThreeWeightedRHBridgeV1.riemannHypothesis_of_weighted_four_log_three_reconstruction
