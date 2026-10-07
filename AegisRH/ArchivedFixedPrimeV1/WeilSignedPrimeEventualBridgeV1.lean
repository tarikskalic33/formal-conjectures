import WeilGeneralSignedKernelBoundV1
import WeilWindowExhaustionV1

/-!
Remove the auxiliary support interval from the exact signed-prime/actual-B
boundedness equivalence. The quantified bound below is still an OPEN analytic
input. Neither side is asserted unconditionally by this module.
-/
open Set Function MeasureTheory Complex
open scoped ComplexConjugate BigOperators
set_option autoImplicit false
noncomputable section

namespace AEGIS.WeilSignedPrimeEventualBridgeV1
open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilDisjointEnergyV2
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.WeilSignedKernelReductionV1
open AEGIS.WeilGeneralSignedKernelBoundV1
open AEGIS.WeilWindowExhaustionV1

private theorem translate_zero (g : WeilCompactSmoothGV1) : translatePacket g 0 = g := by
  apply Subtype.ext
  funext x
  simp [translatePacket_apply]

/-- For every compact packet, eventual boundedness of the exact signed prime
correlation is equivalent to eventual boundedness of the actual translated B.
Support exhaustion supplies the finite interval; it is not an input assumption. -/
theorem signed_prime_eventually_bounded_iff_actual_B_eventually_bounded_v1
    (g : WeilCompactSmoothGV1) :
    (∃ T C : ℝ, ∀ d : ℝ, T ≤ d → ‖SignedPrimeCorrelationV1 g d‖ ≤ C) ↔
    (∃ T C : ℝ, ∀ d : ℝ, T ≤ d → ‖B g (translatePacket g d)‖ ≤ C) := by
  obtain ⟨L, hL, hw⟩ := logLift_has_finite_window_v1 g
  have hab : -L ≤ L := by linarith
  have hbound (d : ℝ) (hd : (L - -L) + 1 ≤ d) :
      ‖B g (translatePacket g d) - SignedPrimeCorrelationV1 g d‖ ≤
        4 * (L - -L) * energy g.1 := by
    have h := B_sub_signed_prime_norm_le_support_energy_v1 g (-L) L 0 d
      hab hw (by simpa using hd)
    simpa only [translate_zero, sub_zero] using h
  constructor
  · rintro ⟨T, C, hC⟩
    refine ⟨max T ((L - -L) + 1), C + 4 * (L - -L) * energy g.1, ?_⟩
    intro d hd
    have ht : T ≤ d := (le_max_left _ _).trans hd
    have hs : (L - -L) + 1 ≤ d := (le_max_right _ _).trans hd
    have hn := norm_sub_norm_le (B g (translatePacket g d)) (SignedPrimeCorrelationV1 g d)
    linarith [hbound d hs, hC d ht]
  · rintro ⟨T, C, hC⟩
    refine ⟨max T ((L - -L) + 1), C + 4 * (L - -L) * energy g.1, ?_⟩
    intro d hd
    have ht : T ≤ d := (le_max_left _ _).trans hd
    have hs : (L - -L) + 1 ≤ d := (le_max_right _ _).trans hd
    have hn := norm_sub_norm_le (SignedPrimeCorrelationV1 g d) (B g (translatePacket g d))
    rw [norm_sub_rev] at hn
    linarith [hbound d hs, hC d ht]

/-- The single signed prime series is genuinely summable on every separated
translation tail; boundedness below cannot arise from a totalized divergent sum. -/
theorem signed_prime_series_summable_of_separated_v1
    (g : WeilCompactSmoothGV1) (a b d : ℝ)
    (hw : LogSupportIn g a b) (hd : b - a < d) :
    Summable (fun n : ℕ => ((ArithmeticFunction.vonMangoldt (n + 1) : ℝ) : ℂ) *
      (Real.exp (-Real.log ((n + 1 : ℕ) : ℝ) / 2) : ℂ) *
        AEGIS.WeilWidthArchCorrelationV25.logCorrelationV25 g
          (-Real.log ((n + 1 : ℕ) : ℝ) + d)) := by
  have hs := AEGIS.WeilSignedPrimeKernelV1.signed_prime_samples_summable_v1 g 0 d
  apply hs.congr
  intro n
  rw [sub_zero, sub_zero,
    positive_prime_correlation_zero_of_separated_v1 g a b d hw hd n, zero_add]

/-- Exact remaining arithmetic boundedness input, with the repository moment
class. This is a definition, not a theorem producer of the bound. -/
def UniversalSignedPrimeCorrelationBoundedV1 : Prop :=
  ∀ g : WeilCompactSmoothGV1, WeilMomentConditionsV1 g →
    ∃ T C : ℝ, ∀ d : ℝ, T ≤ d → ‖SignedPrimeCorrelationV1 g d‖ ≤ C

/-- The open arithmetic bound supplies precisely an eventual actual-B bound. -/
theorem universal_signed_prime_bound_implies_eventual_actual_B_bound_v1
    (h : UniversalSignedPrimeCorrelationBoundedV1) :
    ∀ g : WeilCompactSmoothGV1, WeilMomentConditionsV1 g →
      ∃ T C : ℝ, ∀ d : ℝ, T ≤ d → ‖B g (translatePacket g d)‖ ≤ C := by
  intro g hm
  exact (signed_prime_eventually_bounded_iff_actual_B_eventually_bounded_v1 g).mp (h g hm)

end AEGIS.WeilSignedPrimeEventualBridgeV1

#print axioms AEGIS.WeilSignedPrimeEventualBridgeV1.signed_prime_eventually_bounded_iff_actual_B_eventually_bounded_v1
#print axioms AEGIS.WeilSignedPrimeEventualBridgeV1.universal_signed_prime_bound_implies_eventual_actual_B_bound_v1

#print axioms AEGIS.WeilSignedPrimeEventualBridgeV1.signed_prime_series_summable_of_separated_v1
