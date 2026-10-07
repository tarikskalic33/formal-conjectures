import RHBoundedKernelLaplaceV14
import RHRestrictedWeilBridgeV13
import RestrictedWeilCriterionZeroKernelV10

/-! Conditional RH criterion from actual one-sided translated-kernel bounds.
No bound is asserted unconditionally. No finite-family sign is promoted.
-/
open Set Filter Topology Complex
open scoped BigOperators ComplexConjugate
set_option autoImplicit false
noncomputable section
namespace AEGIS.RHBoundedKernelCriterionV14
open AEGIS.WeilZeroTwoPointV11
open AEGIS.WeilZeroTranslationV11
open AEGIS.RHZeroKernelLaplaceV12
open AEGIS.RHZeroKernelLaplaceAnalyticV12
open AEGIS.RHBoundedKernelLaplaceV14
open AEGIS.RHRestrictedWeilBridgeV13
open AEGIS.RestrictedWeilCriterionFinalV13
open AEGIS.RestrictedWeilCriterionResidueCoefficientV11
open AEGIS.RestrictedWeilCriterionZeroKernelV10
open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.WeilZeroKernelHermitianV11

/-- One-sided boundedness with an arbitrary finite nonnegative constant. -/
def ZeroKernelBoundedV14 (g : WeilCompactSmoothGV1) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ t : ℝ, 0 < t → ‖WeilZeroTranslationKernelV11 g t‖ ≤ C

theorem laplace_eq_resolvent_on_domain_of_bound_v14
    (g : WeilCompactSmoothGV1) (hb : ZeroKernelBoundedV14 g) :
    EqOn (WeilZeroKernelLaplaceV12 g) (WeilZeroResolventV12 g) BridgeDomainV13 := by
  obtain ⟨C, hC, hbound⟩ := hb
  have hL : AnalyticOnNhd ℂ (WeilZeroKernelLaplaceV12 g) BridgeDomainV13 :=
    (zero_kernel_laplace_analyticOnNhd_of_bound_v14 g C hC hbound).mono (fun w hw => hw.1)
  have hR : AnalyticOnNhd ℂ (WeilZeroResolventV12 g) BridgeDomainV13 := by
    intro w hw
    obtain ⟨ε, hε, hsep⟩ :=
      exists_sep_of_not_centered_zero_v13 w hw.1 (fun rho heq => hw.2 ⟨rho, heq⟩)
    rw [resolvent_eq_resolventSum_v13]
    exact resolventSum_analyticAt_v13 (WeilZeroCoefficientV11 g)
      (zero_coefficient_norm_summable_v12 g) w hε (fun rho _ => hsep rho)
  refine hL.eqOn_of_preconnected_of_eventuallyEq hR bridgeDomain_isPreconnected_v13
    one_mem_bridgeDomain_v13 ?_
  have hopen : IsOpen {w : ℂ | (1 / 2 : ℝ) < w.re} :=
    Complex.continuous_re.isOpen_preimage (Ioi (1 / 2 : ℝ)) isOpen_Ioi
  have hmem : {w : ℂ | (1 / 2 : ℝ) < w.re} ∈ 𝓝 (1 : ℂ) :=
    hopen.mem_nhds (by simp; norm_num)
  filter_upwards [hmem] with w hw
  exact zero_kernel_laplace_eq_resolvent_v12 g w hw

/-! ### The pole contradiction -/

theorem zero_re_le_half_of_bounded_witness_v14
    (rho0 : RiemannNontrivialZeroIndexV2)
    (hwitness : ∃ g : WeilCompactSmoothGV1,
      WeilMomentConditionsV1 g ∧ WeilZeroCoefficientV11 g rho0 ≠ 0 ∧
        ZeroKernelBoundedV14 g) :
    rho0.1.re ≤ 1 / 2 := by
  by_contra hlt
  have hlt' : 1 / 2 < rho0.1.re := lt_of_not_ge hlt
  set z : ℂ := WeilCenteredZeroExponentV12 rho0 with hz
  have hzpos : 0 < z.re := by
    rw [hz, centered_re_v13]
    linarith
  obtain ⟨g, hm, ha, hbnd⟩ := hwitness
  obtain ⟨C, hC, hbound⟩ := hbnd
  have ha' : WeilZeroCoefficientV11 g rho0 ≠ 0 := ha
  classical
  let a : RiemannNontrivialZeroIndexV2 → ℂ := WeilZeroCoefficientV11 g
  let b : RiemannNontrivialZeroIndexV2 → ℂ := fun rho => if rho = rho0 then 0 else a rho
  have hb : Summable (fun rho => ‖b rho‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun rho => ?_)
      (zero_coefficient_norm_summable_v12 g)
    by_cases hr : rho = rho0
    · simp [b, hr]
    · simp only [b, hr, if_false]
      exact le_rfl
  obtain ⟨ε₁, hε₁, hiso⟩ := exists_sep_of_centered_zero_v13 rho0
  have hH : AnalyticAt ℂ (ResolventSumV13 b) z := by
    refine resolventSum_analyticAt_v13 b hb z hε₁ (fun rho hb0 => ?_)
    have hne : rho ≠ rho0 := by
      intro heq
      apply hb0
      simp [b, heq]
    exact hiso rho hne
  have hLc : ContinuousAt (WeilZeroKernelLaplaceV12 g) z :=
    (zero_kernel_laplace_analyticOnNhd_of_bound_v14 g C hC hbound z hzpos).continuousAt
  -- pointwise split of the resolvent on the bridge domain
  have hsplit : ∀ w ∈ BridgeDomainV13,
      WeilZeroResolventV12 g w = a rho0 / (w - z) + ResolventSumV13 b w := by
    intro w hw
    obtain ⟨ε, hε, hsep⟩ :=
      exists_sep_of_not_centered_zero_v13 w hw.1 (fun rho heq => hw.2 ⟨rho, heq⟩)
    have hs : Summable (fun rho => a rho / (w - WeilCenteredZeroExponentV12 rho)) := by
      refine Summable.of_norm_bounded
        ((zero_coefficient_norm_summable_v12 g).mul_left (1 / ε)) (fun rho => ?_)
      rw [norm_div]
      have hl := hsep rho
      have hpos : 0 < ‖w - WeilCenteredZeroExponentV12 rho‖ := lt_of_lt_of_le hε hl
      rw [div_le_iff₀ hpos]
      calc
        ‖a rho‖ = (1 / ε * ‖a rho‖) * ε := by field_simp
        _ ≤ (1 / ε * ‖a rho‖) * ‖w - WeilCenteredZeroExponentV12 rho‖ := by
          gcongr
    unfold WeilZeroResolventV12 ResolventSumV13
    rw [hs.tsum_eq_add_tsum_ite rho0]
    congr 1
    apply tsum_congr
    intro rho
    by_cases hr : rho = rho0
    · simp [b, hr]
    · simp only [b, hr, if_false]
  -- punctured neighbourhood of z inside the bridge domain
  let δ : ℝ := min ε₁ z.re
  have hδ : 0 < δ := lt_min hε₁ hzpos
  have hnear : ∀ w ∈ Metric.ball z δ, w ≠ z → w ∈ BridgeDomainV13 := by
    intro w hw hne
    have hd : ‖w - z‖ < δ := by
      simpa [Metric.mem_ball, dist_eq_norm] using hw
    refine ⟨?_, ?_⟩
    · show 0 < w.re
      have hreabs : |w.re - z.re| ≤ ‖w - z‖ := by
        simpa [Complex.sub_re] using Complex.abs_re_le_norm (w - z)
      have hlo := (abs_lt.mp (lt_of_le_of_lt hreabs hd)).1
      have hmin : δ ≤ z.re := min_le_right _ _
      linarith
    · rintro ⟨rho, hrho⟩
      have hrho' : WeilCenteredZeroExponentV12 rho = w := hrho
      have hne' : rho ≠ rho0 := by
        intro heq
        apply hne
        rw [← hrho', heq]
      have h1 := hiso rho hne'
      have hmin : δ ≤ ε₁ := min_le_left _ _
      rw [hrho', norm_sub_rev, ← hz] at h1
      linarith
  have heq : WeilZeroKernelLaplaceV12 g =ᶠ[𝓝[≠] z]
      fun w => a rho0 / (w - z) + ResolventSumV13 b w := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds z hδ),
      self_mem_nhdsWithin] with w hw hne
    have hwz : w ≠ z := by simpa using hne
    have hwD := hnear w hw hwz
    rw [laplace_eq_resolvent_on_domain_of_bound_v14 g ⟨C, hC, hbound⟩ hwD, hsplit w hwD]
  exact continuous_cannot_equal_nonzero_simple_pole_v13 hLc hH.continuousAt ha' heq


/-- It suffices to bound one nonzero-residue witness per nontrivial zero. -/
theorem bounded_zero_witnesses_implies_rh_v14
    (h : ∀ rho : RiemannNontrivialZeroIndexV2,
      ∃ g : WeilCompactSmoothGV1,
        WeilMomentConditionsV1 g ∧ WeilZeroCoefficientV11 g rho ≠ 0 ∧
          ZeroKernelBoundedV14 g) : RiemannHypothesis := by
  intro s hz hnt _
  let rho : RiemannNontrivialZeroIndexV2 := ⟨s, hz, hnt⟩
  have h1 : s.re ≤ 1 / 2 := zero_re_le_half_of_bounded_witness_v14 rho (h rho)
  obtain ⟨sigma, hsig⟩ := exists_reflected_zero_v13 rho
  have h2 := zero_re_le_half_of_bounded_witness_v14 sigma (h sigma)
  rw [hsig] at h2
  simp at h2
  linarith

/-- A uniform translation bound for each legal packet implies exact Mathlib RH. -/
theorem bounded_zero_translation_kernels_implies_rh
    (h : ∀ g : WeilCompactSmoothGV1, WeilMomentConditionsV1 g →
      ZeroKernelBoundedV14 g) : RiemannHypothesis := by
  apply bounded_zero_witnesses_implies_rh_v14
  intro rho
  obtain ⟨g, hm, ha⟩ := exists_nonzero_zero_coefficient_v11 rho
  exact ⟨g, hm, ha, h g hm⟩

/-- V11 uses the opposite translation orientation from V10. -/
theorem zero_kernel_v11_eq_v10_neg_v14
    (g : WeilCompactSmoothGV1) (t : ℝ) :
    WeilZeroTranslationKernelV11 g t = TranslatedZeroKernelV10 g (-t) := by
  rw [translated_zero_kernel_eq_centered_exp_tsum_v10]
  unfold WeilZeroTranslationKernelV11
  apply tsum_congr
  intro rho
  unfold WeilZeroCoefficientV11 WeilZeroIndexSummandV1
    WeilZeroTranslationFactorV11 CenteredZeroExponentV10
  have hexp : (rho.1 - (1 / 2 : ℂ)) * (t : ℂ) =
      ((1 / 2 : ℂ) - rho.1) * ((-t : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hexp]
  ring

/-- Exact arithmetic orientation bridge; B is the repository mixed form. -/
theorem zero_kernel_v11_eq_neg_actual_B_v14
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g) (t : ℝ) :
    WeilZeroTranslationKernelV11 g t = -B g (translatePacket g (-t)) := by
  rw [zero_kernel_v11_eq_v10_neg_v14, translated_zero_kernel_eq_neg_B_v10 g hm]

/-- Signed actual arithmetic boundedness suffices; no Gram surrogate is accepted. -/
theorem bounded_actual_B_translates_implies_rh_v14
    (h : ∀ g : WeilCompactSmoothGV1, WeilMomentConditionsV1 g →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t →
        ‖B g (translatePacket g (-t))‖ ≤ C) : RiemannHypothesis := by
  apply bounded_zero_translation_kernels_implies_rh
  intro g hm
  obtain ⟨C, hC, hbound⟩ := h g hm
  refine ⟨C, hC, ?_⟩
  intro t ht
  rw [zero_kernel_v11_eq_neg_actual_B_v14 g hm t, norm_neg]
  exact hbound t ht

/-- Hermitian symmetry also permits positive arithmetic translation parameters. -/
theorem norm_zero_kernel_eq_actual_B_positive_v14
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g) (t : ℝ) :
    ‖WeilZeroTranslationKernelV11 g t‖ = ‖B g (translatePacket g t)‖ := by
  have h := congrArg norm (zero_kernel_v11_eq_neg_actual_B_v14 g hm (-t))
  simpa only [neg_neg, zero_translation_kernel_neg_eq_conj_v11 g t hm,
    norm_conj, norm_neg] using h

/-- A continuous kernel with an eventually uniform bound is bounded on t>0. -/
theorem zero_kernel_bounded_of_eventual_bound_v14
    (g : WeilCompactSmoothGV1)
    (h : ∃ T C : ℝ, ∀ t : ℝ, T ≤ t →
      ‖WeilZeroTranslationKernelV11 g t‖ ≤ C) : ZeroKernelBoundedV14 g := by
  obtain ⟨T, C, htail⟩ := h
  obtain ⟨D, hcompact⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (0 : ℝ) (max 0 T))
    (zero_translation_kernel_continuous_v12 g).continuousOn
  refine ⟨max 0 (max C D), le_max_left _ _, ?_⟩
  intro t ht
  by_cases hT : T ≤ t
  · exact (htail t hT).trans ((le_max_left C D).trans (le_max_right _ _))
  · have hmem : t ∈ Icc (0 : ℝ) (max 0 T) :=
      ⟨ht.le, (le_of_lt (lt_of_not_ge hT)).trans (le_max_right _ _)⟩
    exact (hcompact t hmem).trans ((le_max_right C D).trans (le_max_right _ _))

/-- Eventual boundedness of the actual signed arithmetic cross terms suffices. -/
theorem eventually_bounded_actual_B_implies_rh_v14
    (h : ∀ g : WeilCompactSmoothGV1, WeilMomentConditionsV1 g →
      ∃ T C : ℝ, ∀ t : ℝ, T ≤ t → ‖B g (translatePacket g t)‖ ≤ C) :
    RiemannHypothesis := by
  apply bounded_zero_translation_kernels_implies_rh
  intro g hm
  apply zero_kernel_bounded_of_eventual_bound_v14 g
  obtain ⟨T, C, hbound⟩ := h g hm
  refine ⟨T, C, ?_⟩
  intro t ht
  rw [norm_zero_kernel_eq_actual_B_positive_v14 g hm]
  exact hbound t ht

/-- Only one nonzero-residue witness per zero needs an eventual arithmetic bound. -/
theorem eventually_bounded_actual_B_witnesses_implies_rh_v14
    (h : ∀ rho : RiemannNontrivialZeroIndexV2,
      ∃ g : WeilCompactSmoothGV1,
        WeilMomentConditionsV1 g ∧ WeilZeroCoefficientV11 g rho ≠ 0 ∧
        ∃ T C : ℝ, ∀ t : ℝ, T ≤ t → ‖B g (translatePacket g t)‖ ≤ C) :
    RiemannHypothesis := by
  apply bounded_zero_witnesses_implies_rh_v14
  intro rho
  obtain ⟨g, hm, ha, T, C, htail⟩ := h rho
  refine ⟨g, hm, ha, zero_kernel_bounded_of_eventual_bound_v14 g ?_⟩
  refine ⟨T, C, ?_⟩
  intro t ht
  rw [norm_zero_kernel_eq_actual_B_positive_v14 g hm]
  exact htail t ht

end AEGIS.RHBoundedKernelCriterionV14
#print axioms AEGIS.RHBoundedKernelCriterionV14.laplace_eq_resolvent_on_domain_of_bound_v14
#print axioms AEGIS.RHBoundedKernelCriterionV14.zero_re_le_half_of_bounded_witness_v14
#print axioms AEGIS.RHBoundedKernelCriterionV14.bounded_zero_witnesses_implies_rh_v14
#print axioms AEGIS.RHBoundedKernelCriterionV14.bounded_zero_translation_kernels_implies_rh
#print axioms AEGIS.RHBoundedKernelCriterionV14.zero_kernel_v11_eq_v10_neg_v14
#print axioms AEGIS.RHBoundedKernelCriterionV14.zero_kernel_v11_eq_neg_actual_B_v14
#print axioms AEGIS.RHBoundedKernelCriterionV14.bounded_actual_B_translates_implies_rh_v14
#print axioms AEGIS.RHBoundedKernelCriterionV14.norm_zero_kernel_eq_actual_B_positive_v14
#print axioms AEGIS.RHBoundedKernelCriterionV14.zero_kernel_bounded_of_eventual_bound_v14
#print axioms AEGIS.RHBoundedKernelCriterionV14.eventually_bounded_actual_B_implies_rh_v14
#print axioms AEGIS.RHBoundedKernelCriterionV14.eventually_bounded_actual_B_witnesses_implies_rh_v14
