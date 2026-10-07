import WeilSeparatedArchBridgeV31

/-!
Exact signed prime samples for arbitrary real translates of an actual repository
packet. This module retains the correlation values, with no absolute-value
majorization or supplied matrix. The continuum prime density has zero pairing
with the translated correlation of a moment-zero packet.
No uniform prime discrepancy estimate, global sign, or RH is asserted.
-/

open Set Function MeasureTheory Complex
open scoped ComplexConjugate BigOperators
set_option autoImplicit false
noncomputable section

namespace AEGIS.WeilSignedPrimeKernelV1

open AEGIS.WeilMixedClosureV2
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.WeilThreeBlockCrossPrimeV28
open AEGIS.WeilWidthArchCorrelationV25
open AEGIS.WeilSeparatedArchBridgeV31

/-- Invert the already proved logarithmic transport without losing the complex
correlation or changing its shift orientation. -/
theorem mixed_translate_exp_eq_v1
    (g : WeilCompactSmoothGV1) (d1 d2 u : ℝ) :
    mixed (translatePacket g d1) (translatePacket g d2) (Real.exp u) =
      (Real.exp (-u / 2) : ℂ) * logCorrelationV25 g (u + d2 - d1) := by
  have he : (Real.exp (-u / 2) : ℂ) * (Real.exp (u / 2) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    simp [show -u / 2 + u / 2 = 0 by ring]
  calc
    mixed (translatePacket g d1) (translatePacket g d2) (Real.exp u) =
        (Real.exp (-u / 2) : ℂ) * ((Real.exp (u / 2) : ℂ) *
          mixed (translatePacket g d1) (translatePacket g d2) (Real.exp u)) := by
      rw [← mul_assoc, he, one_mul]
    _ = _ := by rw [exp_half_mul_mixed_translate_v28]

/-- The exact signed pair of prime samples. Index n still denotes the integer
n+1, exactly as in WeilPrimeTermV1. No moment or support-width assumption is used. -/
theorem prime_term_translate_eq_signed_correlation_v1
    (g : WeilCompactSmoothGV1) (d1 d2 : ℝ) (n : ℕ) :
    WeilPrimeTermV1 (mixed (translatePacket g d1) (translatePacket g d2)) n =
      ((ArithmeticFunction.vonMangoldt (n + 1) : ℝ) : ℂ) *
        (Real.exp (-Real.log ((n + 1 : ℕ) : ℝ) / 2) : ℂ) *
        (logCorrelationV25 g (Real.log ((n + 1 : ℕ) : ℝ) + d2 - d1) +
          logCorrelationV25 g (-Real.log ((n + 1 : ℕ) : ℝ) + d2 - d1)) := by
  let m : ℕ := n + 1
  have hm : (0 : ℝ) < (m : ℝ) := by dsimp [m]; positivity
  have hp := mixed_translate_exp_eq_v1 g d1 d2 (Real.log (m : ℝ))
  have hn := mixed_translate_exp_eq_v1 g d1 d2 (-Real.log (m : ℝ))
  rw [Real.exp_log hm] at hp
  rw [Real.exp_neg, Real.exp_log hm] at hn
  have hw : (1 / (m : ℂ)) * (Real.exp (-(-Real.log (m : ℝ)) / 2) : ℂ) =
      (Real.exp (-Real.log (m : ℝ) / 2) : ℂ) := by
    have hmc : (m : ℂ) = (Real.exp (Real.log (m : ℝ)) : ℂ) := by
      rw [Real.exp_log hm]
      simp
    rw [hmc, one_div, ← Complex.ofReal_inv, ← Real.exp_neg,
      ← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  change ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) *
    (mixed (translatePacket g d1) (translatePacket g d2) (m : ℝ) +
      (1 / (m : ℂ)) *
        mixed (translatePacket g d1) (translatePacket g d2) ((m : ℝ)⁻¹)) = _
  rw [hp, hn, ← mul_assoc (1 / (m : ℂ)), hw]
  dsimp [m]
  ring

/-- Summability of the signed correlation samples is inherited from the actual
mixed prime sum; it is not assumed as a separate analytical premise. -/
theorem signed_prime_samples_summable_v1
    (g : WeilCompactSmoothGV1) (d1 d2 : ℝ) :
    Summable (fun n : ℕ =>
      ((ArithmeticFunction.vonMangoldt (n + 1) : ℝ) : ℂ) *
        (Real.exp (-Real.log ((n + 1 : ℕ) : ℝ) / 2) : ℂ) *
        (logCorrelationV25 g (Real.log ((n + 1 : ℕ) : ℝ) + d2 - d1) +
          logCorrelationV25 g (-Real.log ((n + 1 : ℕ) : ℝ) + d2 - d1))) := by
  have hs := (rhs_convergent (translatePacket g d1) (translatePacket g d2)).1
  exact hs.congr (fun n => prime_term_translate_eq_signed_correlation_v1 g d1 d2 n)

/-- Exact signed prime sum for arbitrary shifts and support widths. -/
theorem prime_sum_translate_eq_signed_correlation_v1
    (g : WeilCompactSmoothGV1) (d1 d2 : ℝ) :
    WeilPrimeSumV1 (mixed (translatePacket g d1) (translatePacket g d2)) =
      ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt (n + 1) : ℝ) : ℂ) *
        (Real.exp (-Real.log ((n + 1 : ℕ) : ℝ) / 2) : ℂ) *
        (logCorrelationV25 g (Real.log ((n + 1 : ℕ) : ℝ) + d2 - d1) +
          logCorrelationV25 g (-Real.log ((n + 1 : ℕ) : ℝ) + d2 - d1)) := by
  exact tsum_congr (prime_term_translate_eq_signed_correlation_v1 g d1 d2)

/-- The continuum prime main term is annihilated by the actual repository
moment constraint. This is the logarithmic density e^(u/2), before any estimate
of the discrete prime discrepancy. The support interval is arbitrary. -/
theorem continuum_prime_main_term_zero_v1
    (g : WeilCompactSmoothGV1) (a b d : ℝ)
    (hw : LogSupportIn g a b) (hm : WeilMomentConditionsV1 g) :
    (∫ u : ℝ, (Real.exp (u / 2) : ℂ) * logCorrelationV25 g (-u + d)) = 0 := by
  have hz := logCross_minus_moment_zero
    (translatePacket g 0) (translatePacket g d)
    (a + 0) (b + 0) (a + d) (b + d)
    (translate_logSupportIn g 0 a b hw)
    (translate_logSupportIn g d a b hw)
    (translate_preserves_moments g 0 hm)
  calc
    (∫ u : ℝ, (Real.exp (u / 2) : ℂ) * logCorrelationV25 g (-u + d)) =
        ∫ u : ℝ, (Real.exp (-(-u) / 2) : ℂ) *
          logCrossV28 (translatePacket g 0) (translatePacket g d) (-u) := by
      apply integral_congr_ae
      filter_upwards [] with u
      rw [logCross_translate_eq_logCorrelation_v28]
      simp
    _ = ∫ u : ℝ, (Real.exp (-u / 2) : ℂ) *
          logCrossV28 (translatePacket g 0) (translatePacket g d) u :=
      integral_neg_eq_self (fun u : ℝ => (Real.exp (-u / 2) : ℂ) *
        logCrossV28 (translatePacket g 0) (translatePacket g d) u) volume
    _ = 0 := hz

end AEGIS.WeilSignedPrimeKernelV1

#print axioms AEGIS.WeilSignedPrimeKernelV1.mixed_translate_exp_eq_v1
#print axioms AEGIS.WeilSignedPrimeKernelV1.prime_term_translate_eq_signed_correlation_v1
#print axioms AEGIS.WeilSignedPrimeKernelV1.signed_prime_samples_summable_v1
#print axioms AEGIS.WeilSignedPrimeKernelV1.prime_sum_translate_eq_signed_correlation_v1
#print axioms AEGIS.WeilSignedPrimeKernelV1.continuum_prime_main_term_zero_v1
