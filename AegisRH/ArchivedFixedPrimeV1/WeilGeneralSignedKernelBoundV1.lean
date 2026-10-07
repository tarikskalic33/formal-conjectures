import WeilSignedKernelReductionV1

/-!
For every actual compact packet, the far-translation Archimedean term has a
uniform bound depending only on the chosen support interval and packet energy.
Consequently eventual boundedness of the actual B entries is equivalent to
boundedness of the exact signed prime-correlation sum. Neither bound is asserted
unconditionally for that prime sum, and no global sign is inferred here.
-/
open Set Function MeasureTheory Complex
open scoped ComplexConjugate BigOperators
set_option autoImplicit false
noncomputable section

namespace AEGIS.WeilGeneralSignedKernelBoundV1

open AEGIS.WeilMixedClosureV2
open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilDisjointEnergyV2
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.WeilThreeBlockCrossPrimeV28
open AEGIS.WeilWidthArchCorrelationV25
open AEGIS.WeilSeparatedArchBridgeV31
open AEGIS.WeilSignedKernelReductionV1

/-- A coarse uniform kernel bound suffices for translation-boundedness; no
moment cancellation or numerical approximation is needed. -/
theorem arch_kernel_le_two_v1 (u : ℝ) (hu : 1 ≤ u) :
    0 ≤ Real.exp (-u / 2) / (1 - Real.exp (-2 * u)) ∧
      Real.exp (-u / 2) / (1 - Real.exp (-2 * u)) ≤ 2 := by
  have hnum : Real.exp (-u / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hlarge : 2 ≤ Real.exp (2 * u) := by linarith [Real.add_one_le_exp (2 * u)]
  have hprod : Real.exp (2 * u) * Real.exp (-2 * u) = 1 := by
    rw [← Real.exp_add]
    simp
  have hsmall : Real.exp (-2 * u) ≤ 1 / 2 := by
    have hh := mul_le_mul_of_nonneg_right hlarge (Real.exp_pos (-2 * u)).le
    rw [hprod] at hh
    linarith
  have hden : 0 < 1 - Real.exp (-2 * u) := by linarith
  constructor
  · exact (div_pos (Real.exp_pos _) hden).le
  · apply (div_le_iff₀ hden).mpr
    linarith

/-- Uniform actual Archimedean bound for an arbitrary packet support interval.
The cutoff ensures a positive distance of at least one between the supports. -/
theorem translated_arch_norm_le_support_energy_v1
    (g : WeilCompactSmoothGV1) (a b d1 d2 : ℝ)
    (hab : a ≤ b) (hw : LogSupportIn g a b)
    (hd : (b - a) + 1 ≤ d2 - d1) :
    ‖WeilArchimedeanIntegralV1
        (mixed (translatePacket g d1) (translatePacket g d2))‖ ≤
      4 * (b - a) * energy g.1 := by
  let lo := (a + d2) - (b + d1)
  let hi := (b + d2) - (a + d1)
  let K : ℝ → ℝ := fun u => Real.exp (-u / 2) / (1 - Real.exp (-2 * u))
  let F : ℝ → ℂ := fun u => (K u : ℂ) *
    logCrossV28 (translatePacket g d1) (translatePacket g d2) (-u)
  have hp := translate_logSupportIn g d1 a b hw
  have hq := translate_logSupportIn g d2 a b hw
  have hlo : 1 ≤ lo := by dsimp [lo]; linarith
  have hwidth : hi - lo = 2 * (b - a) := by dsimp [hi, lo]; ring
  have hwidth0 : 0 ≤ hi - lo := by rw [hwidth]; linarith
  have hzero (u : ℝ) (hu : u ∉ Icc lo hi) :
      logCrossV28 (translatePacket g d1) (translatePacket g d2) (-u) = 0 := by
    apply logCross_zero_outside (translatePacket g d1) (translatePacket g d2)
      (a + d1) (b + d1) (a + d2) (b + d2) (-u) hp hq
    by_cases hl : u < lo
    · right
      dsimp [lo] at hl
      linarith
    · have hh : hi < u := lt_of_not_ge (fun h => hu ⟨le_of_not_gt hl, h⟩)
      left
      dsimp [hi] at hh
      linarith
  have hfull : (∫ u in Icc lo hi, F u) = ∫ u, F u :=
    setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun u hu => by simp [F, hzero u hu])
  have hpos : (∫ u in Ioi (0 : ℝ), F u) = ∫ u, F u := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro u hu
    have hn : u ∉ Icc lo hi := by
      intro h
      exact hu (by change 0 < u; linarith [h.1])
    simp [F, hzero u hn]
  have harch : WeilArchimedeanIntegralV1
      (mixed (translatePacket g d1) (translatePacket g d2)) = ∫ u in Icc lo hi, F u := by
    rw [separated_arch_eq_log_kernel (translatePacket g d1) (translatePacket g d2)
      (a + d1) (b + d1) (a + d2) (b + d2) hp hq (by linarith)]
    exact hpos.trans hfull.symm
  rw [harch]
  calc
    ‖∫ u in Icc lo hi, F u‖ ≤
        (2 * energy g.1) * (volume.restrict (Icc lo hi)).real univ := by
      apply norm_integral_le_of_norm_le_const
      filter_upwards [self_mem_ae_restrict measurableSet_Icc] with u hu
      have hk := arch_kernel_le_two_v1 u (hlo.trans hu.1)
      have hc : ‖logCrossV28 (translatePacket g d1) (translatePacket g d2) (-u)‖ ≤
          energy g.1 := by
        rw [logCross_translate_eq_logCorrelation_v28]
        exact norm_logCorrelation_le_energy_v25 g _
      dsimp [F]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hk.1]
      exact mul_le_mul hk.2 hc (norm_nonneg _) (by norm_num)
    _ = 4 * (b - a) * energy g.1 := by
      simp [Measure.real, Real.volume_Icc, hwidth, ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
      ring

/-- Exact entries differ from their signed prime sums by the uniformly bounded
Archimedean tail on this full half-line of translations. -/
theorem B_sub_signed_prime_norm_le_support_energy_v1
    (g : WeilCompactSmoothGV1) (a b d1 d2 : ℝ)
    (hab : a ≤ b) (hw : LogSupportIn g a b)
    (hd : (b - a) + 1 ≤ d2 - d1) :
    ‖B (translatePacket g d1) (translatePacket g d2) -
        SignedPrimeCorrelationV1 g (d2 - d1)‖ ≤
      4 * (b - a) * energy g.1 := by
  rw [separated_B_eq_signed_prime_add_arch_v1 g a b d1 d2 hw (by linarith),
    add_sub_cancel_left]
  exact translated_arch_norm_le_support_energy_v1 g a b d1 d2 hab hw hd

/-- This is an equivalence between two unproved eventual-boundedness properties,
not an unconditional boundedness producer. The equivalence needs no moments. -/
theorem eventual_B_bounded_iff_signed_prime_bounded_v1
    (g : WeilCompactSmoothGV1) (a b : ℝ)
    (hab : a ≤ b) (hw : LogSupportIn g a b) :
    (∃ M : ℝ, ∀ d : ℝ, (b - a) + 1 ≤ d →
      ‖B (translatePacket g 0) (translatePacket g d)‖ ≤ M) ↔
    (∃ M : ℝ, ∀ d : ℝ, (b - a) + 1 ≤ d →
      ‖SignedPrimeCorrelationV1 g d‖ ≤ M) := by
  constructor
  · rintro ⟨M, hM⟩
    refine ⟨M + 4 * (b - a) * energy g.1, ?_⟩
    intro d hd
    have he := B_sub_signed_prime_norm_le_support_energy_v1 g a b 0 d hab hw (by simpa using hd)
    simp only [sub_zero] at he
    have hn := norm_sub_norm_le (SignedPrimeCorrelationV1 g d)
      (B (translatePacket g 0) (translatePacket g d))
    rw [norm_sub_rev] at hn
    linarith [hM d hd]
  · rintro ⟨M, hM⟩
    refine ⟨M + 4 * (b - a) * energy g.1, ?_⟩
    intro d hd
    have he := B_sub_signed_prime_norm_le_support_energy_v1 g a b 0 d hab hw (by simpa using hd)
    simp only [sub_zero] at he
    have hn := norm_sub_norm_le (B (translatePacket g 0) (translatePacket g d))
      (SignedPrimeCorrelationV1 g d)
    linarith [hM d hd]

end AEGIS.WeilGeneralSignedKernelBoundV1

#print axioms AEGIS.WeilGeneralSignedKernelBoundV1.arch_kernel_le_two_v1
#print axioms AEGIS.WeilGeneralSignedKernelBoundV1.translated_arch_norm_le_support_energy_v1
#print axioms AEGIS.WeilGeneralSignedKernelBoundV1.B_sub_signed_prime_norm_le_support_energy_v1
#print axioms AEGIS.WeilGeneralSignedKernelBoundV1.eventual_B_bounded_iff_signed_prime_bounded_v1
