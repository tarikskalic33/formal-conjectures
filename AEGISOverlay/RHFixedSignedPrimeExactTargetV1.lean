import RHFixedPacketFrontierV1
import WeilSignedPrimeEventualBridgeV1
import RHBoundedKernelCriterionV14
import FormalConjectures.Millennium.RiemannHypothesis

/-!
# Fixed detecting signed-prime exact-target connector

This module closes only the source-composition gap from eventual boundedness of
the exact signed-prime correlation for the already existing detecting packet to
the exact Mathlib RiemannHypothesis target.

It does not prove the eventual signed-prime bound.
-/

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHFixedSignedPrimeExactTargetV1

open AEGIS.RHFixedPacketFrontierV1
open AEGIS.WeilSignedKernelReductionV1
open AEGIS.WeilSignedPrimeEventualBridgeV1
open AEGIS.RHBoundedKernelCriterionV14

/-- The one scalar arithmetic premise for the existing fixed detecting packet. -/
def FixedDetectingSignedPrimeEventuallyBoundedV1 : Prop :=
  ∃ T C : ℝ, ∀ d : ℝ, T ≤ d →
    ‖SignedPrimeCorrelationV1 detectingPacket d‖ ≤ C

/-- Eventual boundedness of the exact signed-prime orbit for the one detecting
packet supplies one bounded nonzero-residue witness for every nontrivial zero,
hence the exact Mathlib RiemannHypothesis proposition. -/
theorem fixed_detecting_signed_prime_eventual_bound_implies_rh_v1
    (h : FixedDetectingSignedPrimeEventuallyBoundedV1) :
    RiemannHypothesis := by
  apply eventually_bounded_actual_B_witnesses_implies_rh_v14
  intro rho
  refine ⟨detectingPacket, detectingPacket_moments, detectingPacket_detects rho, ?_⟩
  exact
    (signed_prime_eventually_bounded_iff_actual_B_eventually_bounded_v1
      detectingPacket).mp h

/-- Type-preserving connector to the official FormalConjectures Millennium
target. The target theorem is used only through its type; its placeholder proof
is not consumed. -/
theorem exact_target_of_fixed_detecting_signed_prime_eventual_bound_v1
    (h : FixedDetectingSignedPrimeEventuallyBoundedV1) :
    type_of% RiemannHypothesis.riemannHypothesis :=
  fixed_detecting_signed_prime_eventual_bound_implies_rh_v1 h

end AEGIS.RHFixedSignedPrimeExactTargetV1

#print axioms AEGIS.RHFixedSignedPrimeExactTargetV1.fixed_detecting_signed_prime_eventual_bound_implies_rh_v1
#print axioms AEGIS.RHFixedSignedPrimeExactTargetV1.exact_target_of_fixed_detecting_signed_prime_eventual_bound_v1
