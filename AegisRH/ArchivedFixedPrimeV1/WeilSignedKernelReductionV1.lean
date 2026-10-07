import WeilSignedPrimeKernelV1
import RHNarrowArchV1

/-!
The remaining large-translation bound is a bound for a signed prime-correlation
sum. The small Archimedean correction is inherited from the proved actual-packet
estimate. This does not establish boundedness of the prime sum or global sign.
-/
open Set Function MeasureTheory Complex
open scoped ComplexConjugate BigOperators
set_option autoImplicit false
noncomputable section

namespace AEGIS.WeilSignedKernelReductionV1

open AEGIS.WeilMixedClosureV2
open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilDisjointEnergyV2
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.WeilThreeBlockCrossPrimeV28
open AEGIS.WeilWidthArchCorrelationV25
open AEGIS.WeilSeparatedArchBridgeV31
open AEGIS.WeilSignedPrimeKernelV1
open AEGIS.RHNarrowFourBlockV2
open AEGIS.RHNarrowArchV1

/-- Exact signed prime correlation at a real displacement. -/
def SignedPrimeCorrelationV1 (g : WeilCompactSmoothGV1) (d : ℝ) : ℂ :=
  ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt (n + 1) : ℝ) : ℂ) *
    (Real.exp (-Real.log ((n + 1 : ℕ) : ℝ) / 2) : ℂ) *
      logCorrelationV25 g (-Real.log ((n + 1 : ℕ) : ℝ) + d)

/-- The nonsurviving prime sample is zero by separation of the actual supports. -/
theorem positive_prime_correlation_zero_of_separated_v1
    (g : WeilCompactSmoothGV1) (a b d : ℝ)
    (hw : LogSupportIn g a b) (hd : b - a < d) (n : ℕ) :
    logCorrelationV25 g (Real.log ((n + 1 : ℕ) : ℝ) + d) = 0 := by
  apply logCross_zero_outside g g a b a b _ hw hw
  right
  have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by norm_cast; omega
  have hl := Real.log_nonneg hn
  linarith

/-- The actual prime sum is the surviving signed correlation sum for an
arbitrary packet support interval and any larger displacement. -/
theorem separated_prime_sum_eq_signed_v1
    (g : WeilCompactSmoothGV1) (a b d1 d2 : ℝ)
    (hw : LogSupportIn g a b) (hd : b - a < d2 - d1) :
    WeilPrimeSumV1 (mixed (translatePacket g d1) (translatePacket g d2)) =
      SignedPrimeCorrelationV1 g (d2 - d1) := by
  rw [prime_sum_translate_eq_signed_correlation_v1]
  apply tsum_congr
  intro n
  have hp := positive_prime_correlation_zero_of_separated_v1 g a b (d2 - d1) hw hd n
  have harg (u : ℝ) : u + d2 - d1 = u + (d2 - d1) := by ring
  rw [harg, hp, zero_add, harg]

/-- Separation kills the centre term in the actual B expression. -/
theorem separated_mixed_one_zero_v1
    (g : WeilCompactSmoothGV1) (a b d1 d2 : ℝ)
    (hw : LogSupportIn g a b) (hd : b - a < d2 - d1) :
    mixed (translatePacket g d1) (translatePacket g d2) 1 = 0 := by
  have hz := logCross_zero_outside g g a b a b (d2 - d1) hw hw (Or.inr hd)
  have hc := exp_half_mul_mixed_translate_v28 g d1 d2 0
  simp only [zero_div, Real.exp_zero, Complex.ofReal_one, one_mul, zero_add] at hc
  exact hc.trans hz

/-- Exact actual-B decomposition, without absolute values or a surrogate matrix. -/
theorem separated_B_eq_signed_prime_add_arch_v1
    (g : WeilCompactSmoothGV1) (a b d1 d2 : ℝ)
    (hw : LogSupportIn g a b) (hd : b - a < d2 - d1) :
    B (translatePacket g d1) (translatePacket g d2) =
      SignedPrimeCorrelationV1 g (d2 - d1) +
        WeilArchimedeanIntegralV1 (mixed (translatePacket g d1) (translatePacket g d2)) := by
  unfold B WeilExplicitRightSideV1
  rw [separated_prime_sum_eq_signed_v1 g a b d1 d2 hw hd,
    separated_mixed_one_zero_v1 g a b d1 d2 hw hd, mul_zero, add_zero]

/-- Beyond 2 log 2, the already checked narrow Archimedean theorem makes the
actual B entry differ from its signed prime correlation by at most energy/500. -/
theorem narrow_B_sub_signed_prime_norm_le_v1
    (g : WeilCompactSmoothGV1) (a d1 d2 : ℝ)
    (hw : WidthOneFortiethAt g a) (hm : WeilMomentConditionsV1 g)
    (hd : 2 * Real.log 2 ≤ d2 - d1) :
    ‖B (translatePacket g d1) (translatePacket g d2) -
        SignedPrimeCorrelationV1 g (d2 - d1)‖ ≤
      (1 / 500 : ℝ) * energy g.1 := by
  have hsep : (a + 1 / 80) - (a - 1 / 80) < d2 - d1 := by
    have hlog := AEGIS.WeilThreeBlockAnalyticConstantsV21.log_two_lower
    linarith
  rw [separated_B_eq_signed_prime_add_arch_v1 g
    (a - 1 / 80) (a + 1 / 80) d1 d2 hw hsep, add_sub_cancel_left]
  exact narrow_translated_arch_two_or_more_v1 g a d1 d2 hw hm hd

/-- Reverse triangle inequality transfers the same error to the norms. -/
theorem narrow_B_signed_prime_norm_comparison_v1
    (g : WeilCompactSmoothGV1) (a d1 d2 : ℝ)
    (hw : WidthOneFortiethAt g a) (hm : WeilMomentConditionsV1 g)
    (hd : 2 * Real.log 2 ≤ d2 - d1) :
    |‖B (translatePacket g d1) (translatePacket g d2)‖ -
      ‖SignedPrimeCorrelationV1 g (d2 - d1)‖| ≤
        (1 / 500 : ℝ) * energy g.1 :=
  (abs_norm_sub_norm_le _ _).trans
    (narrow_B_sub_signed_prime_norm_le_v1 g a d1 d2 hw hm hd)

end AEGIS.WeilSignedKernelReductionV1

#print axioms AEGIS.WeilSignedKernelReductionV1.positive_prime_correlation_zero_of_separated_v1
#print axioms AEGIS.WeilSignedKernelReductionV1.separated_prime_sum_eq_signed_v1
#print axioms AEGIS.WeilSignedKernelReductionV1.separated_mixed_one_zero_v1
#print axioms AEGIS.WeilSignedKernelReductionV1.separated_B_eq_signed_prime_add_arch_v1
#print axioms AEGIS.WeilSignedKernelReductionV1.narrow_B_sub_signed_prime_norm_le_v1
#print axioms AEGIS.WeilSignedKernelReductionV1.narrow_B_signed_prime_norm_comparison_v1
