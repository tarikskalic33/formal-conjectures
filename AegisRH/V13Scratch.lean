import RestrictedWeilCriterionResidueCoefficientV11
import RestrictedWeilCriterionPoleIsolationV10
import MeromorphicIdentityPreconnectedV11
import WeilRHImpliesFinalSignV11
import RHZeroKernelLaplaceAnalyticV12
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.Convex
import Mathlib.Tactic

open Set Filter Topology Complex
open scoped BigOperators

set_option autoImplicit false
noncomputable section

namespace AEGIS.V13Scratch

open AEGIS.RHFinalClosureV1
open AEGIS.RHMillenniumGateV10
open AEGIS.RestrictedWeilCriterionLaplaceV10
open AEGIS.RestrictedWeilCriterionPoleIsolationV10
open AEGIS.RestrictedWeilCriterionResidueCoefficientV11
open AEGIS.MeromorphicIdentityPreconnectedV11
open AEGIS.RHZeroKernelLaplaceV12
open AEGIS.RHZeroKernelLaplaceAnalyticV12
open AEGIS.WeilZeroTwoPointV11

theorem zero_coefficient_v10_eq_v11
    (g : WeilCompactSmoothGV1)
    (rho : RiemannNontrivialZeroIndexV2) :
    ZeroCoefficientV10 g rho = WeilZeroCoefficientV11 g rho := by
  rfl

theorem centered_exponent_v12_eq_neg_v10
    (rho : RiemannNontrivialZeroIndexV2) :
    WeilCenteredZeroExponentV12 rho =
      - CenteredZeroExponentV10 rho := by
  unfold WeilCenteredZeroExponentV12 CenteredZeroExponentV10
  ring

theorem centered_zero_dist_ge_isolation_v12
    (rho : RiemannNontrivialZeroIndexV2) :
    ∃ eps : ℝ, 0 < eps ∧
      ∀ sigma : RiemannNontrivialZeroIndexV2,
        sigma ≠ rho →
        eps ≤
          dist (WeilCenteredZeroExponentV12 sigma)
            (WeilCenteredZeroExponentV12 rho) := by
  obtain ⟨eps, heps, hsep⟩ :=
    centered_zero_dist_ge_isolation_v10 rho
  refine ⟨eps, heps, ?_⟩
  intro sigma hne
  have h := hsep sigma hne
  simpa [centered_exponent_v12_eq_neg_v10] using h

def RightHalfPlaneV13 : Set ℂ := {w : ℂ | 0 < w.re}

theorem rightHalfPlane_isPreconnected_v13 :
    IsPreconnected RightHalfPlaneV13 := by
  simpa [RightHalfPlaneV13] using
    (convex_halfSpace_re_gt (0 : ℝ)).isPreconnected

theorem final_sign_to_universal_zero_quadratic_v13
    (h : FinalSignResidualV1) :
    UniversalZeroQuadraticNonnegativeV10 :=
  universal_zero_quadratic_iff_final_sign_v10.mpr h

theorem laplace_cauchy_seed_eventuallyEq_v13
    (g : WeilCompactSmoothGV1) :
    ZeroKernelLaplaceV10 g =ᶠ[𝓝 (1 : ℂ)]
      ZeroCauchyTransformV10 g := by
  let S : Set ℂ := {w : ℂ | (1 / 2 : ℝ) < w.re}
  have hSopen : IsOpen S := by
    simpa [S] using
      Complex.continuous_re.isOpen_preimage (Ioi (1 / 2 : ℝ)) isOpen_Ioi
  have h1S : (1 : ℂ) ∈ S := by
    simp [S]
  filter_upwards [hSopen.mem_nhds h1S] with w hw
  exact zero_kernel_laplace_eq_cauchy_v10 g hw


def ZeroCauchyRemainderV13
    (g : WeilCompactSmoothGV1)
    (rho : RiemannNontrivialZeroIndexV2)
    (w : ℂ) : ℂ :=
  ∑' sigma : RiemannNontrivialZeroIndexV2,
    if sigma = rho then 0 else ZeroCauchySummandV10 g w sigma

private theorem other_center_denominator_lower_v13
    (rho sigma : RiemannNontrivialZeroIndexV2)
    (eps : ℝ)
    (hsep : ∀ tau : RiemannNontrivialZeroIndexV2,
      tau ≠ rho →
      eps ≤ dist (CenteredZeroExponentV10 tau)
        (CenteredZeroExponentV10 rho))
    (hsigma : sigma ≠ rho)
    {w : ℂ}
    (hw : w ∈ Metric.ball (CenteredZeroExponentV10 rho) (eps / 2)) :
    eps / 2 < dist w (CenteredZeroExponentV10 sigma) := by
  have hs := hsep sigma hsigma
  have ht := dist_triangle
    (CenteredZeroExponentV10 sigma) w
    (CenteredZeroExponentV10 rho)
  have hw' :
      dist w (CenteredZeroExponentV10 rho) < eps / 2 := by
    simpa [Metric.mem_ball] using hw
  rw [dist_comm (CenteredZeroExponentV10 sigma) w] at ht
  linarith

theorem zero_cauchy_remainder_differentiable_near_pole_v13
    (g : WeilCompactSmoothGV1)
    (rho : RiemannNontrivialZeroIndexV2) :
    ∃ eps : ℝ, 0 < eps ∧
      DifferentiableOn ℂ (ZeroCauchyRemainderV13 g rho)
        (Metric.ball (CenteredZeroExponentV10 rho) (eps / 2)) := by
  obtain ⟨eps, heps, hsep⟩ :=
    centered_zero_dist_ge_isolation_v10 rho
  have hr : 0 < eps / 2 := by linarith
  let u : RiemannNontrivialZeroIndexV2 → ℝ := fun sigma =>
    ‖ZeroCoefficientV10 g sigma‖ * (1 / (eps / 2))
  have hu : Summable u := by
    dsimp [u]
    exact (zero_coefficient_norm_summable_v10 g).mul_right (1 / (eps / 2))

  have hterm :
      ∀ sigma : RiemannNontrivialZeroIndexV2,
        DifferentiableOn ℂ
          (fun w : ℂ =>
            if sigma = rho then 0 else ZeroCauchySummandV10 g w sigma)
          (Metric.ball (CenteredZeroExponentV10 rho) (eps / 2)) := by
    intro sigma
    by_cases hsigma : sigma = rho
    · simp [hsigma]
    · intro w hw
      have hd :=
        other_center_denominator_lower_v13 rho sigma eps hsep hsigma hw
      have hne :
          w - CenteredZeroExponentV10 sigma ≠ 0 := by
        apply sub_ne_zero.mpr
        intro heq
        rw [heq, dist_self] at hd
        linarith
      simp only [hsigma, if_false]
      unfold ZeroCauchySummandV10
      apply DifferentiableAt.differentiableWithinAt
      fun_prop (disch := exact hne)

  have hbound :
      ∀ (sigma : RiemannNontrivialZeroIndexV2) (w : ℂ),
        w ∈ Metric.ball (CenteredZeroExponentV10 rho) (eps / 2) →
        ‖(if sigma = rho then 0 else ZeroCauchySummandV10 g w sigma)‖ ≤
          u sigma := by
    intro sigma w hw
    by_cases hsigma : sigma = rho
    · simp [hsigma, u]
      positivity
    · simp only [hsigma, if_false]
      have hd :=
        other_center_denominator_lower_v13 rho sigma eps hsep hsigma hw
      have hden :
          eps / 2 ≤ ‖w - CenteredZeroExponentV10 sigma‖ := by
        simpa [dist_eq_norm] using le_of_lt hd
      have hrec :
          1 / ‖w - CenteredZeroExponentV10 sigma‖ ≤
            1 / (eps / 2) :=
        one_div_le_one_div_of_le hr hden
      unfold ZeroCauchySummandV10
      rw [norm_div]
      dsimp [u]
      simpa [div_eq_mul_inv, one_div] using
        mul_le_mul_of_nonneg_left hrec
          (norm_nonneg (ZeroCoefficientV10 g sigma))

  have hd :=
    differentiableOn_tsum_of_summable_norm
      (F := fun sigma w =>
        if sigma = rho then 0 else ZeroCauchySummandV10 g w sigma)
      hu hterm Metric.isOpen_ball hbound

  refine ⟨eps, heps, ?_⟩
  simpa [ZeroCauchyRemainderV13] using hd


private theorem zero_cauchy_remainder_summable_near_pole_v13
    (g : WeilCompactSmoothGV1)
    (rho : RiemannNontrivialZeroIndexV2)
    (eps : ℝ) (heps : 0 < eps)
    (hsep : ∀ sigma : RiemannNontrivialZeroIndexV2,
      sigma ≠ rho →
      eps ≤ dist (CenteredZeroExponentV10 sigma)
        (CenteredZeroExponentV10 rho))
    {w : ℂ}
    (hw : w ∈ Metric.ball (CenteredZeroExponentV10 rho) (eps / 2)) :
    Summable (fun sigma : RiemannNontrivialZeroIndexV2 =>
      if sigma = rho then 0 else ZeroCauchySummandV10 g w sigma) := by
  let u : RiemannNontrivialZeroIndexV2 → ℝ := fun sigma =>
    ‖ZeroCoefficientV10 g sigma‖ * (1 / (eps / 2))
  have hr : 0 < eps / 2 := by linarith
  have hu : Summable u := by
    dsimp [u]
    exact (zero_coefficient_norm_summable_v10 g).mul_right (1 / (eps / 2))
  apply Summable.of_norm_bounded hu
  intro sigma
  by_cases hsigma : sigma = rho
  · simp [hsigma, u]
    positivity
  · simp only [hsigma, if_false]
    have hd :=
      other_center_denominator_lower_v13 rho sigma eps hsep hsigma hw
    have hden :
        eps / 2 ≤ ‖w - CenteredZeroExponentV10 sigma‖ := by
      simpa [dist_eq_norm] using le_of_lt hd
    have hrec :
        1 / ‖w - CenteredZeroExponentV10 sigma‖ ≤ 1 / (eps / 2) :=
      one_div_le_one_div_of_le hr hden
    unfold ZeroCauchySummandV10
    rw [norm_div]
    dsimp [u]
    simpa [div_eq_mul_inv, one_div] using
      mul_le_mul_of_nonneg_left hrec
        (norm_nonneg (ZeroCoefficientV10 g sigma))

theorem zero_cauchy_transform_split_near_pole_v13
    (g : WeilCompactSmoothGV1)
    (rho : RiemannNontrivialZeroIndexV2) :
    ∃ eps : ℝ, 0 < eps ∧
      ∀ w ∈ Metric.ball (CenteredZeroExponentV10 rho) (eps / 2),
        ZeroCauchyTransformV10 g w =
          ZeroCauchySummandV10 g w rho +
            ZeroCauchyRemainderV13 g rho w := by
  obtain ⟨eps, heps, hsep⟩ :=
    centered_zero_dist_ge_isolation_v10 rho
  refine ⟨eps, heps, ?_⟩
  intro w hw
  have hrem :=
    zero_cauchy_remainder_summable_near_pole_v13
      g rho eps heps hsep hw
  have hfull :
      Summable (fun sigma : RiemannNontrivialZeroIndexV2 =>
        ZeroCauchySummandV10 g w sigma) := by
    apply hrem.congr_cofinite
    filter_upwards [eventually_cofinite_ne rho] with sigma hsigma
    simp [hsigma]
  unfold ZeroCauchyTransformV10 ZeroCauchyRemainderV13
  exact hfull.tsum_eq_add_tsum_ite rho

end AEGIS.V13Scratch
