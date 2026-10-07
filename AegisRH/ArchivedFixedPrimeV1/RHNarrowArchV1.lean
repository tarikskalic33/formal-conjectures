import RHNarrowFourBlockV2
import WeilSeparatedArchBridgeV31
import WeilThreeBlockCrossAssemblyV30
import Mathlib.Tactic

/-!
AEGIS Ω — narrow translated Archimedean bounds V1.

SOURCE CANDIDATE ONLY / LEAN REPLAY NOT RUN.

This file exploits the actual `gNarrow` packet support radius 1/80.
For any packet satisfying the same narrow predicate:
- adjacent dyadic separation (`>= log 2`) gets Arch bound `1/125 * E`;
- any separation `>= 2 log 2` gets Arch bound `1/500 * E`.

The second theorem therefore covers both distance two and distance three
in the four-block lane.

No prime estimate, four-block sign, global Weil sign, or RH theorem is asserted.
-/

open Set Function MeasureTheory Complex
open scoped ComplexConjugate BigOperators

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHNarrowArchV1

open AEGIS.WeilDisjointEnergyV2
open AEGIS.WeilLogCoordinateIsometryV21
open AEGIS.WeilMixedClosureV2
open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.WeilThreeBlockCrossPrimeV28
open AEGIS.WeilWidthArchCorrelationV25
open AEGIS.WeilSeparatedArchBridgeV31
open AEGIS.WeilThreeBlockCrossAssemblyV30
open AEGIS.WeilThreeBlockAnalyticConstantsV21
open AEGIS.RHNarrowFourBlockV2

theorem translate_narrow_logSupportIn
    (g : WeilCompactSmoothGV1) (d a : ℝ)
    (hw : WidthOneFortiethAt g a) :
    LogSupportIn (translatePacket g d)
      (a - (1 / 80 : ℝ) + d)
      (a + (1 / 80 : ℝ) + d) := by
  exact translate_logSupportIn g d
    (a - (1 / 80 : ℝ)) (a + (1 / 80 : ℝ)) hw


theorem translate_preserves_narrow_width_v1
    (g : WeilCompactSmoothGV1) (d a : ℝ)
    (hw : WidthOneFortiethAt g a) :
    WidthOneFortiethAt (translatePacket g d) (a + d) := by
  change LogSupportIn (translatePacket g d)
    (a + d - (1 / 80 : ℝ)) (a + d + (1 / 80 : ℝ))
  convert translate_narrow_logSupportIn g d a hw using 1 <;> ring

theorem exp_one_over_20_upper :
    Real.exp ((1 : ℝ) / 20) < (20 : ℝ) / 19 := by
  calc
    Real.exp ((1 : ℝ) / 20)
        < 1 / (1 - (1 : ℝ) / 20) :=
      Real.exp_bound_div_one_sub_of_interval' (by norm_num) (by norm_num)
    _ = (20 : ℝ) / 19 := by norm_num

/-- Residual kernel at the worst gap `2 log 2 - 1/40`. -/
theorem residual_kernel_two_gap_upper_v1 :
    Real.exp (-5 * (2 * Real.log 2 - (1 / 40 : ℝ)) / 2) /
        (1 - Real.exp (-2 * (2 * Real.log 2 - (1 / 40 : ℝ))))
      < (38 : ℝ) / 1065 := by
  have hnum :
      Real.exp (-5 * (2 * Real.log 2 - (1 / 40 : ℝ)) / 2)
        < (1 : ℝ) / 30 := by
    have he :
        -5 * (2 * Real.log 2 - (1 / 40 : ℝ)) / 2
          = (1 / 16 : ℝ) - 5 * Real.log 2 := by ring
    rw [he, Real.exp_sub,
      show Real.exp (5 * Real.log 2) = (32 : ℝ) by
        rw [show 5 * Real.log 2 = Real.log ((2 : ℝ)^5) by
          rw [Real.log_pow]
          norm_num,
          Real.exp_log (by positivity)]
        norm_num]
    nlinarith [exp_one_over_16_upper]
  have htail :
      Real.exp (-2 * (2 * Real.log 2 - (1 / 40 : ℝ)))
        < (5 : ℝ) / 76 := by
    have he :
        -2 * (2 * Real.log 2 - (1 / 40 : ℝ))
          = (1 / 20 : ℝ) - 4 * Real.log 2 := by ring
    rw [he, Real.exp_sub,
      show Real.exp (4 * Real.log 2) = (16 : ℝ) by
        rw [show 4 * Real.log 2 = Real.log ((2 : ℝ)^4) by
          rw [Real.log_pow]
          norm_num,
          Real.exp_log (by positivity)]
        norm_num]
    nlinarith [exp_one_over_20_upper]
  have hden :
      (71 : ℝ) / 76 <
        1 - Real.exp (-2 * (2 * Real.log 2 - (1 / 40 : ℝ))) := by
    linarith
  have hdenpos :
      0 <
        1 - Real.exp (-2 * (2 * Real.log 2 - (1 / 40 : ℝ))) := by
    linarith
  rw [div_lt_iff₀ hdenpos]
  have hmul :
      Real.exp (-5 * (2 * Real.log 2 - (1 / 40 : ℝ)) / 2)
        < (1 / 30 : ℝ) := hnum
  nlinarith

/-- Narrow version of the centered-kernel Arch estimate.
The mixed difference-support interval has total width 1/20. -/
theorem narrow_translated_arch_adjacent_v1
    (g : WeilCompactSmoothGV1) (a d1 d2 : ℝ)
    (hw : WidthOneFortiethAt g a)
    (hm : WeilMomentConditionsV1 g)
    (hd : Real.log 2 ≤ d2 - d1) :
    ‖WeilArchimedeanIntegralV1
        (mixed (translatePacket g d1) (translatePacket g d2))‖
      ≤ (1 / 125 : ℝ) * energy g.1 := by
  let plo := a - (1 / 80 : ℝ) + d1
  let phi := a + (1 / 80 : ℝ) + d1
  let qlo := a - (1 / 80 : ℝ) + d2
  let qhi := a + (1 / 80 : ℝ) + d2
  let lo := qlo - phi
  let hi := qhi - plo
  let K : ℝ → ℝ :=
    fun u => Real.exp (-u / 2) / (1 - Real.exp (-2 * u))
  let F : ℝ → ℂ :=
    fun u => (K u : ℂ) *
      logCrossV28 (translatePacket g d1) (translatePacket g d2) (-u)
  let M : ℝ → ℂ :=
    fun u => (Real.exp (-u / 2) : ℂ) *
      logCrossV28 (translatePacket g d1) (translatePacket g d2) (-u)
  have hp := translate_narrow_logSupportIn g d1 a hw
  have hq := translate_narrow_logSupportIn g d2 a hw
  have hlo : 0 < lo := by
    dsimp [lo, qlo, phi]
    have hlog : (1 / 40 : ℝ) < Real.log 2 := by
      exact (show (1 / 40 : ℝ) < 693 / 1000 by norm_num).trans log_two_lower
    linarith
  have hwidth : hi - lo = (1 / 20 : ℝ) := by
    dsimp [hi, lo, qhi, plo, qlo, phi]
    ring
  have hzero (u : ℝ) (hu : u ∉ Icc lo hi) :
      logCrossV28 (translatePacket g d1) (translatePacket g d2) (-u) = 0 := by
    apply logCross_zero_outside
      (translatePacket g d1) (translatePacket g d2)
      plo phi qlo qhi (-u) hp hq
    by_cases hlow : u < lo
    · right
      dsimp [lo, qlo, phi] at hlow
      linarith
    · have hhigh : hi < u :=
        lt_of_not_ge (fun h => hu ⟨le_of_not_gt hlow, h⟩)
      left
      dsimp [hi, qhi, plo] at hhigh
      linarith
  have harch :
      WeilArchimedeanIntegralV1
          (mixed (translatePacket g d1) (translatePacket g d2))
        = ∫ u in Icc lo hi, F u := by
    rw [separated_arch_eq_log_kernel
      (translatePacket g d1) (translatePacket g d2)
      plo phi qlo qhi hp hq (by dsimp [phi, qlo]; linarith)]
    have hfull :
        (∫ u in Icc lo hi, F u) = ∫ u, F u :=
      setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun u hu => by simp [F, hzero u hu])
    have hpos :
        (∫ u in Ioi (0 : ℝ), F u) = ∫ u, F u := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro u hu
      have hnot : u ∉ Icc lo hi := by
        intro h
        exact hu (lt_of_lt_of_le hlo h.1)
      simp [F, hzero u hnot]
    exact hpos.trans hfull.symm
  have hMfull : (∫ u, M u) = 0 := by
    have ht := integral_neg_eq_self
      (fun u : ℝ =>
        (Real.exp (u / 2) : ℂ) *
          logCrossV28 (translatePacket g d1) (translatePacket g d2) u) volume
    have hm' :=
      logCross_plus_moment_zero
        (translatePacket g d1) (translatePacket g d2)
        plo phi qlo qhi hp hq (translate_preserves_moments g d1 hm)
    exact ht.trans hm'
  have hMzero : (∫ u in Icc lo hi, M u) = 0 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (f := M) (s := Icc lo hi)
      (fun u hu => by simp [M, hzero u hu])]
    exact hMfull
  have hcancel :
      (∫ u in Icc lo hi, F u) =
        ∫ u in Icc lo hi, F u - (6 / 5 : ℂ) * M u := by
    have hMc : Continuous M := by
      dsimp [M]
      exact (by fun_prop :
        Continuous (fun u : ℝ => (Real.exp (-u / 2) : ℂ))).mul
        ((logCross_continuous _ _).comp continuous_neg)
    have hKc : ContinuousOn K (Icc lo hi) := by
      apply ContinuousOn.div (by fun_prop) (by fun_prop)
      intro u hu
      have hup : 0 < u := lt_of_lt_of_le hlo hu.1
      exact ne_of_gt (sub_pos.mpr
        (Real.exp_lt_one_iff.mpr (by linarith)))
    have hFc : ContinuousOn F (Icc lo hi) :=
      (Complex.continuous_ofReal.comp_continuousOn hKc).mul
        (((logCross_continuous _ _).comp continuous_neg).continuousOn)
    rw [integral_sub hFc.integrableOn_Icc
      (hMc.integrableOn_Icc.const_mul _),
      integral_const_mul, hMzero, mul_zero, sub_zero]
  rw [harch, hcancel]
  calc
    ‖∫ u in Icc lo hi, F u - (6 / 5 : ℂ) * M u‖
        ≤ (4 / 25 : ℝ) * energy g.1 *
            (volume.restrict (Icc lo hi)).real univ := by
      apply norm_integral_le_of_norm_le_const
      filter_upwards [self_mem_ae_restrict measurableSet_Icc] with u hu
      have hgap :
          Real.log 2 - (1 / 32 : ℝ) ≤ u := by
        have hul : lo ≤ u := hu.1
        dsimp [lo, qlo, phi] at hul
        linarith
      have hk := centered_arch_kernel_bound u hgap
      have hR :
          ‖logCrossV28
              (translatePacket g d1) (translatePacket g d2) (-u)‖
            ≤ energy g.1 := by
        rw [logCross_translate_eq_logCorrelation_v28]
        exact norm_logCorrelation_le_energy_v25 g _
      have heq :
          F u - (6 / 5 : ℂ) * M u =
            (((K u - (6 / 5 : ℝ) * Real.exp (-u / 2)) : ℝ) : ℂ) *
              logCrossV28
                (translatePacket g d1) (translatePacket g d2) (-u) := by
        dsimp [F, M]
        push_cast
        ring
      rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul hk hR (norm_nonneg _) (by norm_num)
    _ = (1 / 125 : ℝ) * energy g.1 := by
      simp [Measure.real, Real.volume_Icc, hwidth]
      ring

/-- One residual-kernel estimate handles every separation of at least `2 log 2`.
It therefore covers both distance two and distance three in the four-block family. -/
theorem narrow_translated_arch_two_or_more_v1
    (g : WeilCompactSmoothGV1) (a d1 d2 : ℝ)
    (hw : WidthOneFortiethAt g a)
    (hm : WeilMomentConditionsV1 g)
    (hd : 2 * Real.log 2 ≤ d2 - d1) :
    ‖WeilArchimedeanIntegralV1
        (mixed (translatePacket g d1) (translatePacket g d2))‖
      ≤ (1 / 500 : ℝ) * energy g.1 := by
  let plo := a - (1 / 80 : ℝ) + d1
  let phi := a + (1 / 80 : ℝ) + d1
  let qlo := a - (1 / 80 : ℝ) + d2
  let qhi := a + (1 / 80 : ℝ) + d2
  let lo := qlo - phi
  let hi := qhi - plo
  let K : ℝ → ℝ :=
    fun u => Real.exp (-u / 2) / (1 - Real.exp (-2 * u))
  let M : ℝ → ℂ :=
    fun u => (Real.exp (-u / 2) : ℂ) *
      logCrossV28 (translatePacket g d1) (translatePacket g d2) (-u)
  let R : ℝ → ℂ :=
    fun u =>
      (((Real.exp (-5*u/2) / (1 - Real.exp (-2*u)) : ℝ) : ℂ)) *
        logCrossV28 (translatePacket g d1) (translatePacket g d2) (-u)
  have hp := translate_narrow_logSupportIn g d1 a hw
  have hq := translate_narrow_logSupportIn g d2 a hw
  have hlo : 0 < lo := by
    dsimp [lo, qlo, phi]
    have hlog : (1 / 40 : ℝ) < Real.log 2 := by
      exact (show (1 / 40 : ℝ) < 693 / 1000 by norm_num).trans log_two_lower
    linarith
  have hwidth : hi - lo = (1 / 20 : ℝ) := by
    dsimp [hi, lo, qhi, plo, qlo, phi]
    ring
  have hdelta :
      2 * Real.log 2 - (1 / 40 : ℝ) ≤ lo := by
    dsimp [lo, qlo, phi]
    linarith
  have hkernel (u : ℝ) (hu : u ∈ Icc lo hi) :
      Real.exp (-5*u/2) / (1 - Real.exp (-2*u))
        < (38 : ℝ) / 1065 := by
    have hδpos :
        0 < 2 * Real.log 2 - (1 / 40 : ℝ) := by
      have hlog : (1 / 40 : ℝ) < Real.log 2 := by
        exact (show (1 / 40 : ℝ) < 693 / 1000 by norm_num).trans log_two_lower
      linarith
    have hmono :=
      arch_remainder_le_at_gap
        (2 * Real.log 2 - (1 / 40 : ℝ)) u
        hδpos (hdelta.trans hu.1)
    exact hmono.trans_lt residual_kernel_two_gap_upper_v1
  have hzero (u : ℝ) (hu : u ∉ Icc lo hi) :
      logCrossV28 (translatePacket g d1) (translatePacket g d2) (-u) = 0 := by
    apply logCross_zero_outside
      (translatePacket g d1) (translatePacket g d2)
      plo phi qlo qhi (-u) hp hq
    by_cases hlow : u < lo
    · right
      dsimp [lo, qlo, phi] at hlow
      linarith
    · have hhigh : hi < u :=
        lt_of_not_ge (fun h => hu ⟨le_of_not_gt hlow, h⟩)
      left
      dsimp [hi, qhi, plo] at hhigh
      linarith
  have harch :=
    separated_arch_eq_log_kernel
      (translatePacket g d1) (translatePacket g d2)
      plo phi qlo qhi hp hq (by dsimp [phi, qlo]; linarith)
  have hMfull : (∫ u, M u) = 0 := by
    have ht := integral_neg_eq_self
      (fun u : ℝ =>
        (Real.exp (u / 2) : ℂ) *
          logCrossV28 (translatePacket g d1) (translatePacket g d2) u) volume
    have hm' :=
      logCross_plus_moment_zero
        (translatePacket g d1) (translatePacket g d2)
        plo phi qlo qhi hp hq (translate_preserves_moments g d1 hm)
    exact ht.trans hm'
  have hMzero : (∫ u in Icc lo hi, M u) = 0 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (f := M) (s := Icc lo hi)
      (fun u hu => by simp [M, hzero u hu])]
    exact hMfull
  have hresidual_on (u : ℝ) (hu : 0 < u) :
      ((K u : ℂ) *
          logCrossV28 (translatePacket g d1) (translatePacket g d2) (-u))
        - M u = R u := by
    dsimp [K, M, R]
    rw [← sub_mul, ← Complex.ofReal_sub, arch_kernel_sub_rank_one u hu]
  rw [harch]
  have hfull :
      (∫ u in Ioi (0 : ℝ),
        (K u : ℂ) *
          logCrossV28 (translatePacket g d1) (translatePacket g d2) (-u))
      =
      ∫ u in Icc lo hi,
        (K u : ℂ) *
          logCrossV28 (translatePacket g d1) (translatePacket g d2) (-u) := by
    have hA :
        (∫ u in Icc lo hi,
          (K u : ℂ) *
            logCrossV28 (translatePacket g d1) (translatePacket g d2) (-u))
        =
        ∫ u,
          (K u : ℂ) *
            logCrossV28 (translatePacket g d1) (translatePacket g d2) (-u) :=
      setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun u hu => by simp [hzero u hu])
    have hB :
        (∫ u in Ioi (0 : ℝ),
          (K u : ℂ) *
            logCrossV28 (translatePacket g d1) (translatePacket g d2) (-u))
        =
        ∫ u,
          (K u : ℂ) *
            logCrossV28 (translatePacket g d1) (translatePacket g d2) (-u) := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro u hu
      have hnot : u ∉ Icc lo hi := by
        intro h
        exact hu (lt_of_lt_of_le hlo h.1)
      simp [hzero u hnot]
    exact hB.trans hA.symm
  rw [hfull]
  have hKc : ContinuousOn K (Icc lo hi) := by
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro u hu
    have hup : 0 < u := lt_of_lt_of_le hlo hu.1
    exact ne_of_gt (sub_pos.mpr
      (Real.exp_lt_one_iff.mpr (by linarith)))
  have hFc : ContinuousOn
      (fun u : ℝ =>
        (K u : ℂ) *
          logCrossV28 (translatePacket g d1) (translatePacket g d2) (-u))
      (Icc lo hi) :=
    (Complex.continuous_ofReal.comp_continuousOn hKc).mul
      (((logCross_continuous _ _).comp continuous_neg).continuousOn)
  have hMc : Continuous M := by
    dsimp [M]
    exact (by fun_prop :
      Continuous (fun u : ℝ => (Real.exp (-u / 2) : ℂ))).mul
      ((logCross_continuous _ _).comp continuous_neg)
  have hcancel :
      (∫ u in Icc lo hi,
          (K u : ℂ) *
            logCrossV28 (translatePacket g d1) (translatePacket g d2) (-u))
      =
      ∫ u in Icc lo hi, R u := by
    have hR_eq :
        ∀ u ∈ Icc lo hi,
          R u =
            (K u : ℂ) *
                logCrossV28 (translatePacket g d1) (translatePacket g d2) (-u)
              - M u := by
      intro u hu
      exact (hresidual_on u (lt_of_lt_of_le hlo hu.1)).symm
    rw [show
      (∫ u in Icc lo hi, R u) =
        ∫ u in Icc lo hi,
          ((K u : ℂ) *
              logCrossV28 (translatePacket g d1) (translatePacket g d2) (-u)
            - M u) by
      apply setIntegral_congr_fun measurableSet_Icc
      intro u hu
      exact hR_eq u hu]
    rw [integral_sub hFc.integrableOn_Icc hMc.integrableOn_Icc,
      hMzero, sub_zero]
  rw [hcancel]
  calc
    ‖∫ u in Icc lo hi, R u‖
        ≤ (38 / 1065 : ℝ) * energy g.1 *
            (volume.restrict (Icc lo hi)).real univ := by
      apply norm_integral_le_of_norm_le_const
      filter_upwards [self_mem_ae_restrict measurableSet_Icc] with u hu
      have hk := (hkernel u hu).le
      have hR :
          ‖logCrossV28
              (translatePacket g d1) (translatePacket g d2) (-u)‖
            ≤ energy g.1 := by
        rw [logCross_translate_eq_logCorrelation_v28]
        exact norm_logCorrelation_le_energy_v25 g _
      dsimp [R]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hnonneg :
          0 ≤ Real.exp (-5*u/2) / (1 - Real.exp (-2*u)) := by
        have hup : 0 < u := lt_of_lt_of_le hlo hu.1
        have hden : 0 < 1 - Real.exp (-2 * u) :=
          sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
        exact le_of_lt (div_pos (Real.exp_pos _) hden)
      rw [abs_of_nonneg hnonneg]
      exact mul_le_mul hk hR (norm_nonneg _) (by positivity)
    _ ≤ (1 / 500 : ℝ) * energy g.1 := by
      have hE := energy_nonnegative g.1
      have hrat :
          (38 / 1065 : ℝ) * (1 / 20) ≤ 1 / 500 := by norm_num
      simp [Measure.real, Real.volume_Icc, hwidth]
      nlinarith only [mul_le_mul_of_nonneg_right hrat hE]

end AEGIS.RHNarrowArchV1

#print axioms AEGIS.RHNarrowArchV1.residual_kernel_two_gap_upper_v1
#print axioms AEGIS.RHNarrowArchV1.narrow_translated_arch_adjacent_v1
#print axioms AEGIS.RHNarrowArchV1.narrow_translated_arch_two_or_more_v1
