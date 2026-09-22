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


def ZeroResolventRemainderV13
    (g : WeilCompactSmoothGV1)
    (rho : RiemannNontrivialZeroIndexV2)
    (w : ℂ) : ℂ :=
  ∑' sigma : RiemannNontrivialZeroIndexV2,
    if sigma = rho then 0 else
      WeilZeroCoefficientV11 g sigma /
        (w - WeilCenteredZeroExponentV12 sigma)

private theorem other_center_denominator_lower_v12
    (rho sigma : RiemannNontrivialZeroIndexV2)
    (eps : ℝ)
    (hsep : ∀ tau : RiemannNontrivialZeroIndexV2,
      tau ≠ rho →
      eps ≤ dist (WeilCenteredZeroExponentV12 tau)
        (WeilCenteredZeroExponentV12 rho))
    (hsigma : sigma ≠ rho)
    {w : ℂ}
    (hw : w ∈ Metric.ball (WeilCenteredZeroExponentV12 rho) (eps / 2)) :
    eps / 2 < dist w (WeilCenteredZeroExponentV12 sigma) := by
  have hs := hsep sigma hsigma
  have ht := dist_triangle
    (WeilCenteredZeroExponentV12 sigma) w
    (WeilCenteredZeroExponentV12 rho)
  have hw' :
      dist w (WeilCenteredZeroExponentV12 rho) < eps / 2 := by
    simpa [Metric.mem_ball] using hw
  rw [dist_comm (WeilCenteredZeroExponentV12 sigma) w] at ht
  linarith

theorem zero_resolvent_remainder_differentiable_near_pole_v13
    (g : WeilCompactSmoothGV1)
    (rho : RiemannNontrivialZeroIndexV2) :
    ∃ eps : ℝ, 0 < eps ∧
      DifferentiableOn ℂ (ZeroResolventRemainderV13 g rho)
        (Metric.ball (WeilCenteredZeroExponentV12 rho) (eps / 2)) := by
  obtain ⟨eps, heps, hsep⟩ :=
    centered_zero_dist_ge_isolation_v12 rho
  have hr : 0 < eps / 2 := by linarith
  let u : RiemannNontrivialZeroIndexV2 → ℝ := fun sigma =>
    ‖WeilZeroCoefficientV11 g sigma‖ * (1 / (eps / 2))
  have hu : Summable u := by
    dsimp [u]
    exact (zero_coefficient_norm_summable_v12 g).mul_right (1 / (eps / 2))

  have hterm :
      ∀ sigma : RiemannNontrivialZeroIndexV2,
        DifferentiableOn ℂ
          (fun w : ℂ =>
            if sigma = rho then 0 else
              WeilZeroCoefficientV11 g sigma /
                (w - WeilCenteredZeroExponentV12 sigma))
          (Metric.ball (WeilCenteredZeroExponentV12 rho) (eps / 2)) := by
    intro sigma
    by_cases hsigma : sigma = rho
    · simp [hsigma]
    · intro w hw
      have hd :=
        other_center_denominator_lower_v12 rho sigma eps hsep hsigma hw
      have hne :
          w - WeilCenteredZeroExponentV12 sigma ≠ 0 := by
        apply sub_ne_zero.mpr
        intro heq
        rw [heq, dist_self] at hd
        linarith
      simp only [hsigma, if_false]
      apply DifferentiableAt.differentiableWithinAt
      fun_prop (disch := exact hne)

  have hbound :
      ∀ (sigma : RiemannNontrivialZeroIndexV2) (w : ℂ),
        w ∈ Metric.ball (WeilCenteredZeroExponentV12 rho) (eps / 2) →
        ‖(if sigma = rho then 0 else
          WeilZeroCoefficientV11 g sigma /
            (w - WeilCenteredZeroExponentV12 sigma))‖ ≤ u sigma := by
    intro sigma w hw
    by_cases hsigma : sigma = rho
    · simp [hsigma, u]
      positivity
    · simp only [hsigma, if_false]
      have hd :=
        other_center_denominator_lower_v12 rho sigma eps hsep hsigma hw
      have hden :
          eps / 2 ≤ ‖w - WeilCenteredZeroExponentV12 sigma‖ := by
        simpa [dist_eq_norm] using le_of_lt hd
      have hrec :
          1 / ‖w - WeilCenteredZeroExponentV12 sigma‖ ≤
            1 / (eps / 2) :=
        one_div_le_one_div_of_le hr hden
      rw [norm_div]
      dsimp [u]
      simpa [div_eq_mul_inv, one_div] using
        mul_le_mul_of_nonneg_left hrec
          (norm_nonneg (WeilZeroCoefficientV11 g sigma))

  have hd :=
    differentiableOn_tsum_of_summable_norm
      (F := fun sigma w =>
        if sigma = rho then 0 else
          WeilZeroCoefficientV11 g sigma /
            (w - WeilCenteredZeroExponentV12 sigma))
      hu hterm Metric.isOpen_ball hbound

  refine ⟨eps, heps, ?_⟩
  simpa [ZeroResolventRemainderV13] using hd

private theorem zero_resolvent_remainder_summable_near_pole_v13
    (g : WeilCompactSmoothGV1)
    (rho : RiemannNontrivialZeroIndexV2)
    (eps : ℝ) (heps : 0 < eps)
    (hsep : ∀ sigma : RiemannNontrivialZeroIndexV2,
      sigma ≠ rho →
      eps ≤ dist (WeilCenteredZeroExponentV12 sigma)
        (WeilCenteredZeroExponentV12 rho))
    {w : ℂ}
    (hw : w ∈ Metric.ball (WeilCenteredZeroExponentV12 rho) (eps / 2)) :
    Summable (fun sigma : RiemannNontrivialZeroIndexV2 =>
      if sigma = rho then 0 else
        WeilZeroCoefficientV11 g sigma /
          (w - WeilCenteredZeroExponentV12 sigma)) := by
  let u : RiemannNontrivialZeroIndexV2 → ℝ := fun sigma =>
    ‖WeilZeroCoefficientV11 g sigma‖ * (1 / (eps / 2))
  have hr : 0 < eps / 2 := by linarith
  have hu : Summable u := by
    dsimp [u]
    exact (zero_coefficient_norm_summable_v12 g).mul_right (1 / (eps / 2))
  apply Summable.of_norm_bounded hu
  intro sigma
  by_cases hsigma : sigma = rho
  · simp [hsigma, u]
    positivity
  · simp only [hsigma, if_false]
    have hd :=
      other_center_denominator_lower_v12 rho sigma eps hsep hsigma hw
    have hden :
        eps / 2 ≤ ‖w - WeilCenteredZeroExponentV12 sigma‖ := by
      simpa [dist_eq_norm] using le_of_lt hd
    have hrec :
        1 / ‖w - WeilCenteredZeroExponentV12 sigma‖ ≤ 1 / (eps / 2) :=
      one_div_le_one_div_of_le hr hden
    rw [norm_div]
    dsimp [u]
    simpa [div_eq_mul_inv, one_div] using
      mul_le_mul_of_nonneg_left hrec
        (norm_nonneg (WeilZeroCoefficientV11 g sigma))

theorem zero_resolvent_split_near_pole_v13
    (g : WeilCompactSmoothGV1)
    (rho : RiemannNontrivialZeroIndexV2) :
    ∃ eps : ℝ, 0 < eps ∧
      ∀ w ∈ Metric.ball (WeilCenteredZeroExponentV12 rho) (eps / 2),
        WeilZeroResolventV12 g w =
          WeilZeroCoefficientV11 g rho /
            (w - WeilCenteredZeroExponentV12 rho) +
          ZeroResolventRemainderV13 g rho w := by
  obtain ⟨eps, heps, hsep⟩ :=
    centered_zero_dist_ge_isolation_v12 rho
  refine ⟨eps, heps, ?_⟩
  intro w hw
  have hrem :=
    zero_resolvent_remainder_summable_near_pole_v13
      g rho eps heps hsep hw
  have hfull :
      Summable (fun sigma : RiemannNontrivialZeroIndexV2 =>
        WeilZeroCoefficientV11 g sigma /
          (w - WeilCenteredZeroExponentV12 sigma)) := by
    apply hrem.congr_cofinite
    filter_upwards [eventually_cofinite_ne rho] with sigma hsigma
    simp [hsigma]
  unfold WeilZeroResolventV12 ZeroResolventRemainderV13
  exact hfull.tsum_eq_add_tsum_ite rho


theorem zero_resolvent_order_eq_neg_one_v13
    (g : WeilCompactSmoothGV1)
    (rho : RiemannNontrivialZeroIndexV2)
    (hcoef : WeilZeroCoefficientV11 g rho ≠ 0) :
    meromorphicOrderAt (WeilZeroResolventV12 g)
      (WeilCenteredZeroExponentV12 rho) = (-1 : ℤ) := by
  let y : ℂ := WeilCenteredZeroExponentV12 rho

  obtain ⟨epsR, hepsR, hRdiff⟩ :=
    zero_resolvent_remainder_differentiable_near_pole_v13 g rho
  have hRanalytic :
      AnalyticAt ℂ (ZeroResolventRemainderV13 g rho) y := by
    apply hRdiff.analyticAt
    simpa [y] using
      (Metric.ball_mem_nhds
        (WeilCenteredZeroExponentV12 rho) (by linarith : 0 < epsR / 2))

  let G : ℂ → ℂ := fun z =>
    WeilZeroCoefficientV11 g rho +
      (z - y) * ZeroResolventRemainderV13 g rho z

  have hGanalytic : AnalyticAt ℂ G y := by
    dsimp [G]
    fun_prop

  have hGne : G y ≠ 0 := by
    simpa [G] using hcoef

  obtain ⟨epsS, hepsS, hsplit⟩ :=
    zero_resolvent_split_near_pole_v13 g rho

  have hball :
      Metric.ball y (epsS / 2) ∈ 𝓝 y := by
    simpa [y] using
      (Metric.ball_mem_nhds
        (WeilCenteredZeroExponentV12 rho) (by linarith : 0 < epsS / 2))

  have hballNE :
      ∀ᶠ z in 𝓝[≠] y, z ∈ Metric.ball y (epsS / 2) :=
    hball.filter_mono nhdsWithin_le_nhds

  have heq :
      ∀ᶠ z in 𝓝[≠] y,
        WeilZeroResolventV12 g z =
          (z - y) ^ (-1 : ℤ) * G z := by
    filter_upwards [hballNE, self_mem_nhdsWithin] with z hzball hzNE
    have hzy : z - y ≠ 0 := by
      apply sub_ne_zero.mpr
      simpa using hzNE
    have hs :=
      hsplit z (by simpa [y] using hzball)
    rw [hs]
    dsimp [G]
    rw [zpow_neg_one]
    field_simp [hzy]
    ring

  have hmer :
      MeromorphicAt (WeilZeroResolventV12 g) y := by
    rw [MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt]
    refine ⟨(-1 : ℤ), G, hGanalytic, ?_⟩
    filter_upwards [heq] with z hz
    simpa [smul_eq_mul] using hz

  rw [meromorphicOrderAt_eq_int_iff hmer]
  refine ⟨G, hGanalytic, hGne, ?_⟩
  filter_upwards [heq] with z hz
  simpa [smul_eq_mul] using hz


private theorem zeta_shift_ne_zero_of_not_center_v13
    {w : ℂ} (hw : 0 < w.re)
    (hnopole : ∀ rho : RiemannNontrivialZeroIndexV2,
      WeilCenteredZeroExponentV12 rho ≠ w) :
    riemannZeta (w + (1 / 2 : ℂ)) ≠ 0 := by
  intro hz
  let s : ℂ := w + (1 / 2 : ℂ)
  have hspos : 0 < s.re := by
    dsimp [s]
    simp
    linarith
  have htriv :
      ¬ ∃ n : ℕ, s = -(2 : ℂ) * (n + 1) := by
    rintro ⟨n, hn⟩
    rw [hn] at hspos
    have hnonpos :
        (-(2 : ℂ) * ((n + 1 : ℕ) : ℂ)).re ≤ 0 := by
      simp
      positivity
    exact (not_lt_of_ge hnonpos) hspos
  let rho : RiemannNontrivialZeroIndexV2 :=
    ⟨s, hz, htriv⟩
  have hc : WeilCenteredZeroExponentV12 rho = w := by
    dsimp [rho, s, WeilCenteredZeroExponentV12]
    ring
  exact hnopole rho hc

private theorem centered_zero_dist_ge_of_not_center_v13
    {w : ℂ} (hw : 0 < w.re)
    (hnopole : ∀ rho : RiemannNontrivialZeroIndexV2,
      WeilCenteredZeroExponentV12 rho ≠ w) :
    ∃ eps : ℝ, 0 < eps ∧
      ∀ sigma : RiemannNontrivialZeroIndexV2,
        eps ≤ dist (WeilCenteredZeroExponentV12 sigma) w := by
  let s : ℂ := w + (1 / 2 : ℂ)
  have hz : riemannZeta s ≠ 0 := by
    simpa [s] using zeta_shift_ne_zero_of_not_center_v13 hw hnopole
  have hscompl : s ∈ riemannZetaZerosᶜ := by
    simpa [mem_riemannZetaZeros] using hz
  obtain ⟨eps, heps, hball⟩ :=
    Metric.isOpen_iff.mp isClosed_riemannZetaZeros.isOpen_compl s hscompl
  refine ⟨eps, heps, ?_⟩
  intro sigma
  by_contra hnot
  have hlt :
      dist (WeilCenteredZeroExponentV12 sigma) w < eps :=
    lt_of_not_ge hnot
  have hdist :
      dist sigma.1 s =
        dist (WeilCenteredZeroExponentV12 sigma) w := by
    rw [dist_eq_norm, dist_eq_norm]
    congr 1
    dsimp [s, WeilCenteredZeroExponentV12]
    ring
  have hsball : sigma.1 ∈ Metric.ball s eps := by
    rw [Metric.mem_ball, hdist]
    exact hlt
  have hsnotzero : sigma.1 ∉ riemannZetaZeros :=
    hball hsball
  exact hsnotzero (mem_riemannZetaZeros.mpr sigma.2.1)

private theorem center_denominator_lower_from_point_v13
    (w0 : ℂ)
    (sigma : RiemannNontrivialZeroIndexV2)
    (eps : ℝ)
    (hsep : ∀ tau : RiemannNontrivialZeroIndexV2,
      eps ≤ dist (WeilCenteredZeroExponentV12 tau) w0)
    {w : ℂ} (hw : w ∈ Metric.ball w0 (eps / 2)) :
    eps / 2 < dist w (WeilCenteredZeroExponentV12 sigma) := by
  have hs := hsep sigma
  have ht :=
    dist_triangle (WeilCenteredZeroExponentV12 sigma) w w0
  have hw' : dist w w0 < eps / 2 := by
    simpa [Metric.mem_ball] using hw
  rw [dist_comm (WeilCenteredZeroExponentV12 sigma) w] at ht
  linarith

private theorem zero_resolvent_differentiable_near_nonpole_v13
    (g : WeilCompactSmoothGV1)
    {w0 : ℂ} (hw0 : 0 < w0.re)
    (hnopole : ∀ rho : RiemannNontrivialZeroIndexV2,
      WeilCenteredZeroExponentV12 rho ≠ w0) :
    ∃ eps : ℝ, 0 < eps ∧
      DifferentiableOn ℂ (WeilZeroResolventV12 g)
        (Metric.ball w0 (eps / 2)) := by
  obtain ⟨eps, heps, hsep⟩ :=
    centered_zero_dist_ge_of_not_center_v13 hw0 hnopole
  have hr : 0 < eps / 2 := by linarith
  let u : RiemannNontrivialZeroIndexV2 → ℝ := fun sigma =>
    ‖WeilZeroCoefficientV11 g sigma‖ * (1 / (eps / 2))
  have hu : Summable u := by
    dsimp [u]
    exact (zero_coefficient_norm_summable_v12 g).mul_right (1 / (eps / 2))

  have hterm :
      ∀ sigma : RiemannNontrivialZeroIndexV2,
        DifferentiableOn ℂ
          (fun w : ℂ =>
            WeilZeroCoefficientV11 g sigma /
              (w - WeilCenteredZeroExponentV12 sigma))
          (Metric.ball w0 (eps / 2)) := by
    intro sigma w hw
    have hd :=
      center_denominator_lower_from_point_v13 w0 sigma eps hsep hw
    have hne :
        w - WeilCenteredZeroExponentV12 sigma ≠ 0 := by
      apply sub_ne_zero.mpr
      intro heq
      rw [heq, dist_self] at hd
      linarith
    apply DifferentiableAt.differentiableWithinAt
    fun_prop (disch := exact hne)

  have hbound :
      ∀ (sigma : RiemannNontrivialZeroIndexV2) (w : ℂ),
        w ∈ Metric.ball w0 (eps / 2) →
        ‖WeilZeroCoefficientV11 g sigma /
          (w - WeilCenteredZeroExponentV12 sigma)‖ ≤ u sigma := by
    intro sigma w hw
    have hd :=
      center_denominator_lower_from_point_v13 w0 sigma eps hsep hw
    have hden :
        eps / 2 ≤ ‖w - WeilCenteredZeroExponentV12 sigma‖ := by
      simpa [dist_eq_norm] using le_of_lt hd
    have hrec :
        1 / ‖w - WeilCenteredZeroExponentV12 sigma‖ ≤
          1 / (eps / 2) :=
      one_div_le_one_div_of_le hr hden
    rw [norm_div]
    dsimp [u]
    simpa [div_eq_mul_inv, one_div] using
      mul_le_mul_of_nonneg_left hrec
        (norm_nonneg (WeilZeroCoefficientV11 g sigma))

  have hd :=
    differentiableOn_tsum_of_summable_norm
      (F := fun sigma w =>
        WeilZeroCoefficientV11 g sigma /
          (w - WeilCenteredZeroExponentV12 sigma))
      hu hterm Metric.isOpen_ball hbound

  refine ⟨eps, heps, ?_⟩
  simpa [WeilZeroResolventV12] using hd

theorem zero_resolvent_meromorphicAt_center_v13
    (g : WeilCompactSmoothGV1)
    (rho : RiemannNontrivialZeroIndexV2) :
    MeromorphicAt (WeilZeroResolventV12 g)
      (WeilCenteredZeroExponentV12 rho) := by
  let y : ℂ := WeilCenteredZeroExponentV12 rho
  obtain ⟨epsR, hepsR, hRdiff⟩ :=
    zero_resolvent_remainder_differentiable_near_pole_v13 g rho
  have hRanalytic :
      AnalyticAt ℂ (ZeroResolventRemainderV13 g rho) y := by
    apply hRdiff.analyticAt
    simpa [y] using
      (Metric.ball_mem_nhds
        (WeilCenteredZeroExponentV12 rho) (by linarith : 0 < epsR / 2))
  let G : ℂ → ℂ := fun z =>
    WeilZeroCoefficientV11 g rho +
      (z - y) * ZeroResolventRemainderV13 g rho z
  have hGanalytic : AnalyticAt ℂ G y := by
    dsimp [G]
    fun_prop
  obtain ⟨epsS, hepsS, hsplit⟩ :=
    zero_resolvent_split_near_pole_v13 g rho
  have hball :
      Metric.ball y (epsS / 2) ∈ 𝓝 y := by
    simpa [y] using
      (Metric.ball_mem_nhds
        (WeilCenteredZeroExponentV12 rho) (by linarith : 0 < epsS / 2))
  have hballNE :
      ∀ᶠ z in 𝓝[≠] y, z ∈ Metric.ball y (epsS / 2) :=
    hball.filter_mono nhdsWithin_le_nhds
  have heq :
      ∀ᶠ z in 𝓝[≠] y,
        WeilZeroResolventV12 g z =
          (z - y) ^ (-1 : ℤ) * G z := by
    filter_upwards [hballNE, self_mem_nhdsWithin] with z hzball hzNE
    have hzy : z - y ≠ 0 := by
      apply sub_ne_zero.mpr
      simpa using hzNE
    have hs := hsplit z (by simpa [y] using hzball)
    rw [hs]
    dsimp [G]
    rw [zpow_neg_one]
    field_simp [hzy]
    ring
  rw [MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt]
  refine ⟨(-1 : ℤ), G, hGanalytic, ?_⟩
  filter_upwards [heq] with z hz
  simpa [smul_eq_mul] using hz

theorem zero_resolvent_meromorphicOn_rightHalfPlane_v13
    (g : WeilCompactSmoothGV1) :
    MeromorphicOn (WeilZeroResolventV12 g) RightHalfPlaneV13 := by
  intro w hw
  by_cases hpole :
      ∃ rho : RiemannNontrivialZeroIndexV2,
        WeilCenteredZeroExponentV12 rho = w
  · obtain ⟨rho, hrho⟩ := hpole
    rw [← hrho]
    exact zero_resolvent_meromorphicAt_center_v13 g rho
  · push_neg at hpole
    obtain ⟨eps, heps, hdiff⟩ :=
      zero_resolvent_differentiable_near_nonpole_v13
        g (by simpa [RightHalfPlaneV13] using hw) hpole
    have han : AnalyticAt ℂ (WeilZeroResolventV12 g) w := by
      apply hdiff.analyticAt
      exact Metric.ball_mem_nhds w (by linarith)
    exact han.meromorphicAt

end AEGIS.V13Scratch
