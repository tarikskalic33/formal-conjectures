import RHZeroKernelLaplaceAnalyticV12

/-! Generic one-sided bounded-kernel Laplace bridge.
Source proof refactored from pinned AEGIS V12. No final-sign premise is used.
-/
open Set Filter Topology Complex MeasureTheory
open scoped BigOperators
set_option autoImplicit false
noncomputable section
namespace AEGIS.RHBoundedKernelLaplaceV14
open AEGIS.WeilZeroTwoPointV11
open AEGIS.RHZeroKernelLaplaceV12
open AEGIS.RHZeroKernelLaplaceAnalyticV12

/-- The bounded zero kernel has an integrable Laplace transform for every
parameter in Re(w)>0. -/
theorem zero_kernel_laplace_integrable_of_bound_v14
    (g : WeilCompactSmoothGV1)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ t : ℝ, 0 < t → ‖WeilZeroTranslationKernelV11 g t‖ ≤ C)
    (w : ℂ) (hw : 0 < w.re) :
    IntegrableOn
      (fun t : ℝ =>
        Complex.exp (-(w * (t : ℂ))) *
          WeilZeroTranslationKernelV11 g t)
      (Ioi (0 : ℝ)) := by
  let B : ℝ := C
  have hB : 0 ≤ B := hC
  have hmajor :
      IntegrableOn
        (fun t : ℝ => B * Real.exp (-w.re * t))
        (Ioi (0 : ℝ)) := by
    exact
      (integrableOn_exp_mul_Ioi (a := -w.re) (by linarith) 0).const_mul B
  have hmeas :
      AEStronglyMeasurable
        (fun t : ℝ =>
          Complex.exp (-(w * (t : ℂ))) *
            WeilZeroTranslationKernelV11 g t)
        (volume.restrict (Ioi (0 : ℝ))) := by
    exact
      ((by fun_prop :
        Continuous (fun t : ℝ =>
          Complex.exp (-(w * (t : ℂ))))).aestronglyMeasurable.mul
        (zero_translation_kernel_continuous_v12 g).aestronglyMeasurable).restrict
  refine hmajor.mono' hmeas ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  exact Filter.Eventually.of_forall (fun t ht => by
    rw [norm_mul, Complex.norm_exp]
    have hK := hbound t ht
    have hre :
        (-(w * (t : ℂ))).re = -w.re * t := by
      simp
    rw [hre, mul_comm B]
    exact mul_le_mul_of_nonneg_left hK (Real.exp_nonneg _))

/-- An integrable first-moment exponential tail used to dominate the
w-derivative locally. -/
private theorem first_moment_exp_tail_integrable_v14
    (δ B : ℝ) (hδ : 0 < δ) :
    IntegrableOn
      (fun t : ℝ => B * (t * Real.exp (-(δ * t))))
      (Ioi (0 : ℝ)) := by
  by_cases hB : B = 0
  · simp [hB]
  have hbase :
      IntegrableOn
        (fun t : ℝ => t * Real.exp (-(δ * t)))
        (Ioi (0 : ℝ)) := by
    have hI :=
      integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1) (b := δ)
        (by norm_num) (by norm_num) hδ
    refine hI.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp [Real.rpow_one]
  exact hbase.const_mul B

/-- Differentiability of the bounded-kernel Laplace transform at every point
of the open right half-plane. -/
theorem zero_kernel_laplace_differentiableAt_of_bound_v14
    (g : WeilCompactSmoothGV1)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ t : ℝ, 0 < t → ‖WeilZeroTranslationKernelV11 g t‖ ≤ C)
    (w0 : ℂ) (hw0 : 0 < w0.re) :
    DifferentiableAt ℂ (WeilZeroKernelLaplaceV12 g) w0 := by
  let δ : ℝ := w0.re / 2
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  let B : ℝ := C
  have hB : 0 ≤ B := hC

  let F : ℂ → ℝ → ℂ := fun w t =>
    Complex.exp (-(w * (t : ℂ))) *
      WeilZeroTranslationKernelV11 g t
  let F' : ℂ → ℝ → ℂ := fun w t =>
    (-(t : ℂ)) *
      Complex.exp (-(w * (t : ℂ))) *
        WeilZeroTranslationKernelV11 g t
  let bound : ℝ → ℝ := fun t =>
    B * (t * Real.exp (-(δ * t)))

  have hs : Metric.ball w0 δ ∈ 𝓝 w0 :=
    Metric.ball_mem_nhds _ hδ

  have hFmeas :
      ∀ᶠ w in 𝓝 w0,
        AEStronglyMeasurable (F w)
          (volume.restrict (Ioi (0 : ℝ))) := by
    exact Filter.Eventually.of_forall (fun w => by
      apply AEStronglyMeasurable.restrict
      exact
        ((by fun_prop :
          Continuous (fun t : ℝ =>
            Complex.exp (-(w * (t : ℂ))))).aestronglyMeasurable.mul
          (zero_translation_kernel_continuous_v12 g).aestronglyMeasurable))

  have hFint :
      Integrable (F w0) (volume.restrict (Ioi (0 : ℝ))) := by
    exact zero_kernel_laplace_integrable_of_bound_v14
      g C hC hbound w0 hw0

  have hF'meas :
      AEStronglyMeasurable (F' w0)
        (volume.restrict (Ioi (0 : ℝ))) := by
    apply AEStronglyMeasurable.restrict
    exact
      ((by fun_prop :
        Continuous (fun t : ℝ =>
          (-(t : ℂ)) *
            Complex.exp (-(w0 * (t : ℂ))))).aestronglyMeasurable.mul
        (zero_translation_kernel_continuous_v12 g).aestronglyMeasurable)

  have hderivbound :
      ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
        ∀ w ∈ Metric.ball w0 δ, ‖F' w t‖ ≤ bound t := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    exact Filter.Eventually.of_forall (fun t ht w hw => by
      have ht0 : 0 ≤ t := le_of_lt ht
      have hdist : ‖w - w0‖ < δ := by
        simpa [Metric.mem_ball, dist_eq_norm] using hw
      have hreDiff : |w.re - w0.re| ≤ ‖w - w0‖ := by
        simpa [Complex.sub_re] using Complex.abs_re_le_norm (w - w0)
      have hwre : δ ≤ w.re := by
        have hlo := (abs_lt.mp (lt_of_le_of_lt hreDiff hdist)).1
        dsimp only [δ] at hlo ⊢
        linarith
      have hK := hbound t ht
      simp only [F', bound, B]
      rw [norm_mul, norm_mul, norm_neg, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg ht0, Complex.norm_exp]
      have hre :
          (-(w * (t : ℂ))).re = -w.re * t := by
        simp
      rw [hre]
      have hexp :
          Real.exp (-w.re * t) ≤ Real.exp (-(δ * t)) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      calc
        t * Real.exp (-w.re * t) *
            ‖WeilZeroTranslationKernelV11 g t‖
          ≤ t * Real.exp (-(δ * t)) *
              C := by
              gcongr
        _ = C *
              (t * Real.exp (-(δ * t))) := by ring)

  have hboundInt :
      Integrable bound (volume.restrict (Ioi (0 : ℝ))) := by
    exact first_moment_exp_tail_integrable_v14 δ B hδ

  have hdiff :
      ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
        ∀ w ∈ Metric.ball w0 δ,
          HasDerivAt (F · t) (F' w t) w := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    exact Filter.Eventually.of_forall (fun t ht w hw => by
      simp only [F, F']
      have hinner :
          HasDerivAt (fun z : ℂ => -(z * (t : ℂ))) (-(t : ℂ)) w :=
        (hasDerivAt_mul_const (t : ℂ)).neg
      have hExp :
          HasDerivAt
            (fun z : ℂ => Complex.exp (-(z * (t : ℂ))))
            (-(t : ℂ) *
              Complex.exp (-(w * (t : ℂ)))) w :=
        hinner.cexp.congr_deriv (by ring)
      exact hExp.mul_const
        (WeilZeroTranslationKernelV11 g t))

  have main :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict (Ioi (0 : ℝ)))
      (F := F) (F' := F') (bound := bound)
      hs hFmeas hFint hF'meas hderivbound hboundInt hdiff

  exact main.2.differentiableAt

/-- Under the supplied bound, the zero-kernel Laplace transform is holomorphic on the
entire open right half-plane. -/
theorem zero_kernel_laplace_analyticOnNhd_of_bound_v14
    (g : WeilCompactSmoothGV1)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ t : ℝ, 0 < t → ‖WeilZeroTranslationKernelV11 g t‖ ≤ C) :
    AnalyticOnNhd ℂ
      (WeilZeroKernelLaplaceV12 g)
      ZeroLaplaceRightHalfPlaneV12 := by
  apply DifferentiableOn.analyticOnNhd
  · intro w hw
    exact
      (zero_kernel_laplace_differentiableAt_of_bound_v14
        g C hC hbound w hw).differentiableWithinAt
  · exact zeroLaplaceRightHalfPlane_isOpen_v12

end AEGIS.RHBoundedKernelLaplaceV14
#print axioms AEGIS.RHBoundedKernelLaplaceV14.zero_kernel_laplace_integrable_of_bound_v14
#print axioms AEGIS.RHBoundedKernelLaplaceV14.zero_kernel_laplace_differentiableAt_of_bound_v14
#print axioms AEGIS.RHBoundedKernelLaplaceV14.zero_kernel_laplace_analyticOnNhd_of_bound_v14
